// exact.cpp -- exact rational checks of "Regular Morley tetrahedra from p-secting planes".
//
// Arithmetic in Q and in Q(sqrt 105) with 128-bit numerators.  Checks:
//   Section 3   the face functions L_X at the vertices; the inward normals of the box
//               tetrahedron are positive multiples of (alpha, beta, gamma), ...; the
//               cosines (3.1); the half-turns permute L_A, ..., L_D as stated
//   (3.2)/4     the table of w_E on the four lines
//   Example 1.5 cosines, squared sines, L_A(X), lambda, ratios 2, 13/5, 14/5, tan^2 phi
//   Example 1.6 in Q(sqrt(5/21)) = Q(sqrt 105): every identity in its proof
//   Theorem 1.7 the identity for r(u,v); the impossibility of the lines l_2, l_3, l_4 and
//               the case analysis, for all integer triples 1 <= alpha, beta, gamma <= 60
// Prints ALL OK on success.   c++ -O2 -std=c++17 -o exact exact.cpp && ./exact
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>

typedef __int128 i128;

static i128 gcd128(i128 a, i128 b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  while (b) {
    i128 t = a % b;
    a = b;
    b = t;
  }
  return a;
}

struct Q {
  i128 n, d;
  Q(i128 n_ = 0, i128 d_ = 1) : n(n_), d(d_) {
    if (d < 0) n = -n, d = -d;
    i128 g = gcd128(n, d);
    if (g > 1) n /= g, d /= g;
  }
};
static Q operator+(Q a, Q b) { return Q(a.n * b.d + b.n * a.d, a.d * b.d); }
static Q operator-(Q a, Q b) { return Q(a.n * b.d - b.n * a.d, a.d * b.d); }
static Q operator-(Q a) { return Q(-a.n, a.d); }
static Q operator*(Q a, Q b) { return Q(a.n * b.n, a.d * b.d); }
static Q operator/(Q a, Q b) { return Q(a.n * b.d, a.d * b.n); }
static bool operator==(Q a, Q b) { return a.n == b.n && a.d == b.d; }
static bool operator!=(Q a, Q b) { return !(a == b); }
static bool pos(Q a) { return a.n > 0; }

// a + b sqrt(105)
struct S {
  Q a, b;
};
static const Q D105(105);
static S operator+(S x, S y) { return {x.a + y.a, x.b + y.b}; }
static S operator-(S x, S y) { return {x.a - y.a, x.b - y.b}; }
static S operator*(S x, S y) { return {x.a * y.a + D105 * x.b * y.b, x.a * y.b + x.b * y.a}; }
static S operator*(Q c, S x) { return {c * x.a, c * x.b}; }
static bool operator==(S x, S y) { return x.a == y.a && x.b == y.b; }
static S sq(Q c) { return {c, Q(0)}; }
// sign of a + b sqrt 105
static int sgn(S x) {
  int sa = x.a.n > 0 ? 1 : x.a.n < 0 ? -1 : 0, sb = x.b.n > 0 ? 1 : x.b.n < 0 ? -1 : 0;
  if (sa == 0) return sb;
  if (sb == 0 || sa == sb) return sa;
  // opposite signs: compare a^2 with 105 b^2
  Q diff = x.a * x.a - D105 * x.b * x.b;
  return diff.n > 0 ? sa : diff.n < 0 ? sb : 0;
}

static int failures = 0;
static void check(const char *name, bool ok) {
  printf("%s %s\n", ok ? "ok   " : "FAIL ", name);
  if (!ok) failures++;
}

struct V3 {
  Q x, y, z;
};
static V3 sub(V3 a, V3 b) { return {a.x - b.x, a.y - b.y, a.z - b.z}; }
static V3 cross(V3 a, V3 b) {
  return {a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x};
}
static Q dot(V3 a, V3 b) { return a.x * b.x + a.y * b.y + a.z * b.z; }

// face functions: sign rows for L_A, L_B, L_C, L_D
static const int SG[4][3] = {{1, 1, 1}, {1, -1, -1}, {-1, 1, -1}, {-1, -1, 1}};
static Q L(int X, Q al, Q be, Q ga, V3 P) {
  return Q(1) + Q(SG[X][0]) * al * P.x + Q(SG[X][1]) * be * P.y + Q(SG[X][2]) * ga * P.z;
}

int main() {
  std::mt19937 rng(20261010);
  auto rq = [&](int lo, int hi) {
    std::uniform_int_distribution<int> num(lo, hi), den(1, 12);
    return Q(num(rng), den(rng));
  };

  // ---------------------------------------------------------------- Section 3
  {
    bool ok_vert = true, ok_norm = true, ok_cos = true, ok_turn = true, ok_w = true;
    for (int n = 0; n < 2000; n++) {
      Q a = rq(1, 40), b = rq(1, 40), c = rq(1, 40);
      Q al = Q(1) / a, be = Q(1) / b, ga = Q(1) / c;
      V3 P[4] = {{a, b, c}, {a, -b, -c}, {-a, b, -c}, {-a, -b, c}};
      for (int X = 0; X < 4; X++)
        for (int Y = 0; Y < 4; Y++)
          if (L(X, al, be, ga, P[Y]) != Q(X == Y ? 4 : 0)) ok_vert = false;
      // inward normal of the face opposite X is a positive multiple of SG[X] * (al,be,ga)
      V3 nrm[4];
      for (int X = 0; X < 4; X++) {
        int f[3], k = 0;
        for (int i = 0; i < 4; i++)
          if (i != X) f[k++] = i;
        V3 m = cross(sub(P[f[1]], P[f[0]]), sub(P[f[2]], P[f[0]]));
        if (!pos(dot(m, sub(P[X], P[f[0]])))) m = {-m.x, -m.y, -m.z};
        V3 g = {Q(SG[X][0]) * al, Q(SG[X][1]) * be, Q(SG[X][2]) * ga};
        Q k1 = m.x / g.x;
        if (!(pos(k1) && m.y == k1 * g.y && m.z == k1 * g.z)) ok_norm = false;
        nrm[X] = g;
      }
      Q N2 = al * al + be * be + ga * ga;
      // cos theta at CD = -(n_A . n_B)/N^2 etc. (the normals g have length N)
      if (-dot(nrm[0], nrm[1]) / N2 != (-al * al + be * be + ga * ga) / N2) ok_cos = false;
      if (-dot(nrm[0], nrm[2]) / N2 != (al * al - be * be + ga * ga) / N2) ok_cos = false;
      if (-dot(nrm[0], nrm[3]) / N2 != (al * al + be * be - ga * ga) / N2) ok_cos = false;
      // half-turns: h1 = (x,-y,-z) swaps A<->B, C<->D; h2 swaps A<->C, B<->D; h3 A<->D, B<->C
      V3 Pt = {rq(-30, 30), rq(-30, 30), rq(-30, 30)};
      V3 H[3] = {{Pt.x, -Pt.y, -Pt.z}, {-Pt.x, Pt.y, -Pt.z}, {-Pt.x, -Pt.y, Pt.z}};
      const int perm[3][4] = {{1, 0, 3, 2}, {2, 3, 0, 1}, {3, 2, 1, 0}};
      for (int h = 0; h < 3; h++)
        for (int X = 0; X < 4; X++)
          if (L(X, al, be, ga, H[h]) != L(perm[h][X], al, be, ga, Pt)) ok_turn = false;
      // table of w_E: L_B - L_A = -2t w_CD, L_C - L_A = -2t w_BD, L_D - L_A = -2t w_BC
      Q t = rq(-20, 20);
      const int dl[4][3] = {{1, 1, 1}, {1, -1, -1}, {-1, 1, -1}, {-1, -1, 1}};
      Q w[4][3] = {{be + ga, al + ga, al + be},
                   {-be - ga, al - ga, al - be},
                   {be - ga, -al - ga, be - al},
                   {ga - be, ga - al, -al - be}};
      for (int i = 0; i < 4; i++) {
        V3 X = {t * Q(dl[i][0]), t * Q(dl[i][1]), t * Q(dl[i][2])};
        Q LA = L(0, al, be, ga, X);
        for (int E = 0; E < 3; E++)
          if (L(E + 1, al, be, ga, X) - LA != Q(-2) * t * w[i][E]) ok_w = false;
      }
    }
    check("Section 3: L_X equals 4 at X and 0 at the other vertices", ok_vert);
    check("Section 3: inward normals are positive multiples of (+-alpha, +-beta, +-gamma)", ok_norm);
    check("(3.1): the cosines of the dihedral angles at CD, BD, BC", ok_cos);
    check("Section 3: the half-turns permute L_A, ..., L_D", ok_turn);
    check("(3.2) and Section 4: the table of w_E on the four lines", ok_w);
  }

  // ---------------------------------------------------------------- Example 1.5
  {
    Q al(1), be(1, 2), ga(1, 3), N2 = al * al + be * be + ga * ga;
    Q cCD = (-al * al + be * be + ga * ga) / N2, cBD = (al * al - be * be + ga * ga) / N2,
      cBC = (al * al + be * be - ga * ga) / N2;
    Q t(2, 7), LAX = Q(1) - t * (al + be + ga), lam = t / LAX;
    Q rCD = Q(1) + Q(2) * (be + ga) * lam, rBD = Q(1) + Q(2) * (al + ga) * lam,
      rBC = Q(1) + Q(2) * (al + be) * lam;
    bool ok = N2 == Q(49, 36) && cCD == Q(-23, 49) && cBD == Q(31, 49) && cBC == Q(41, 49) &&
              Q(1) - cCD * cCD == Q(144 * 13, 49 * 49) && Q(1) - cBD * cBD == Q(144 * 10, 49 * 49) &&
              Q(1) - cBC * cBC == Q(144 * 5, 49 * 49) && LAX == Q(10, 21) && lam == Q(3, 5) &&
              rCD == Q(2) && rBD == Q(13, 5) && rBC == Q(14, 5) && pos(rCD + cCD) &&
              pos(rBD + cBD) && pos(rBC + cBC) &&
              (Q(1) - cCD * cCD) / ((rCD + cCD) * (rCD + cCD)) == Q(16 * 13, 625) &&
              (Q(1) - cBD * cBD) / ((rBD + cBD) * (rBD + cBD)) == Q(25 * 10, 66 * 66) &&
              (Q(1) - cBC * cBC) / ((rBC + cBC) * (rBC + cBC)) == Q(400 * 5, 297 * 297);
    check("Example 1.5: cosines, sines, L_A(X) = 10/21, lambda = 3/5, ratios, tan^2 phi", ok);
  }

  // ---------------------------------------------------------------- Example 1.6
  {
    Q al(1, 4), be(1, 2), ga(1), N2 = al * al + be * be + ga * ga;
    Q cCD = (-al * al + be * be + ga * ga) / N2, cBD = (al * al - be * be + ga * ga) / N2,
      cBC = (al * al + be * be - ga * ga) / N2;
    S s = {Q(0), Q(1, 21)};  // sqrt(5/21) = sqrt(105)/21
    S lam = Q(4, 3) * s;
    S t = sq(Q(5, 2)) - Q(9, 2) * s;
    S one = sq(Q(1));
    bool ok = N2 == Q(21, 16) && cCD == Q(19, 21) && cBD == Q(13, 21) && cBC == Q(-11, 21);
    ok = ok && s * s == sq(Q(5, 21));
    ok = ok && sq(Q(2) * (Q(1) + cCD)) == (Q(4) * s) * (Q(4) * s);   // (R_4 - 1)^2, edge CD
    ok = ok && sq(Q(2) * (Q(1) + cBC)) == (Q(2) * s) * (Q(2) * s);   // (R_4 - 1)^2, edge BC
    ok = ok && one + (Q(2) * (be + ga)) * lam == one + Q(4) * s;     // e = 4
    ok = ok && one + (Q(2) * (al + be)) * lam == one + Q(2) * s;     // f = 4
    ok = ok && t * (one + (al + be + ga) * lam) == lam;               // t = lam/(1 + 7lam/4)
    ok = ok && sgn(t) > 0 && sgn(one - (al + be + ga) * t) > 0;        // X interior
    ok = ok && one + (Q(2) * (al + ga)) * lam == one + Q(10, 3) * s;  // third ratio
    ok = ok && Q(1) - cBD * cBD == Q(16 * 17, 441);
    // tan phi_BD = (4 sqrt17/21) / (1 + 10s/3 + 13/21) = 2 sqrt17 / (17 + 35 s)
    // <=> (4/21)(17 + 35 s) = 2 (34/21 + (10/3) s)
    ok = ok && Q(4, 21) * (sq(Q(17)) + Q(35) * s) ==
                   Q(2) * (sq(Q(1) + Q(13, 21)) + Q(10, 3) * s);
    ok = ok && sgn(sq(Q(17)) + Q(35) * s) > 0;
    check("Example 1.6: every identity of its proof, in Q(sqrt 105)", ok);
  }

  // ---------------------------------------------------------------- Theorem 1.7
  {
    bool ok_r = true;
    for (int n = 0; n < 5000; n++) {
      Q u = rq(1, 30), v = rq(1, 30), w = rq(1, 30);
      auto r = [](Q x, Q y) { return x * y / ((x + y) * (x + y)); };
      Q lhs = r(u, v) - r(u, w);
      Q rhs = u * (v - w) * (u * u - v * w) / ((u + v) * (u + v) * (u + w) * (u + w));
      if (lhs != rhs) ok_r = false;
      if ((u * u + v * v) / ((u + v) * (u + v)) != Q(1) - Q(2) * r(u, v)) ok_r = false;
    }
    check("Theorem 1.7: r(u,v) - r(u,w) and (u^2+v^2)/(u+v)^2 = 1 - 2r(u,v)", ok_r);

    bool ok_lines = true, ok_case = true, ok_l1 = true;
    for (int A = 1; A <= 60; A++)
      for (int B = 1; B <= 60; B++)
        for (int C = 1; C <= 60; C++) {
          i128 al = A, be = B, ga = C;
          // q_E / w_E^2 equal for two edges <=> q1 w2^2 = q2 w1^2 (cross-multiplied)
          auto same = [](i128 q1, i128 w1, i128 q2, i128 w2) { return q1 * w2 * w2 == q2 * w1 * w1; };
          i128 qCD = be * be + ga * ga, qBD = al * al + ga * ga, qBC = al * al + be * be;
          // delta_2: CD (w = -(be+ga)) and BD (w = al - ga) cannot agree
          if (al != ga && same(qCD, be + ga, qBD, al - ga)) ok_lines = false;
          // delta_3: BD (w = -(al+ga)) and CD (w = be - ga)
          if (be != ga && same(qBD, al + ga, qCD, be - ga)) ok_lines = false;
          // delta_4: BC (w = -(al+be)) and CD (w = ga - be)
          if (ga != be && same(qBC, al + be, qCD, ga - be)) ok_lines = false;
          // the case analysis
          bool eq1 = (be - al) * (ga * ga - al * be) == 0, eq2 = (ga - be) * (al * al - be * ga) == 0;
          if (eq1 && eq2 && !(al == be && be == ga)) ok_case = false;
          // directly: the three quotients on l_1 agree only if al = be = ga
          if (same(qCD, be + ga, qBD, al + ga) && same(qBD, al + ga, qBC, al + be) &&
              !(al == be && be == ga))
            ok_l1 = false;
        }
    check("Theorem 1.7: l_2, l_3, l_4 impossible for integer triples <= 60", ok_lines);
    check("Theorem 1.7: case analysis for integer triples <= 60", ok_case);
    check("Theorem 1.7: equal quotients on l_1 only for alpha = beta = gamma (<= 60)", ok_l1);
  }

  if (failures) {
    printf("%d FAILED\n", failures);
    return 1;
  }
  printf("ALL OK\n");
  return 0;
}
