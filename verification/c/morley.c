/* morley.c -- long double checks of "Regular Morley tetrahedra from p-secting planes".
 *
 * The p-secting planes are built from Definition 1.1 by turning a face about its edge;
 * A' is found by Cramer's rule.  Checks:
 *   - Examples 1.5 and 1.6: the Morley tetrahedron is regular, with the stated vertices;
 *   - Lemma 2.4: for random isosceles tetrahedra and random parameters, B', C', D' are
 *     the half-turns of A' (so the edge lengths are 2 sqrt(y^2+z^2), ...);
 *   - Theorem 1.3(b): random points of the four lines, turned into parameters by
 *     Lemma 2.1 and (2.3), give regular Morley tetrahedra with A' at the chosen point;
 *   - Lemma 2.1: R_p(theta) is increasing in p and exceeds 1 exactly when p > 2.
 * Prints ALL OK on success.   cc -O2 -o morley morley.c -lm && ./morley
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

typedef long double ld;
typedef struct { ld x, y, z; } vec;

static vec v(ld x, ld y, ld z) { vec r = {x, y, z}; return r; }
static vec add(vec a, vec b) { return v(a.x + b.x, a.y + b.y, a.z + b.z); }
static vec sub(vec a, vec b) { return v(a.x - b.x, a.y - b.y, a.z - b.z); }
static vec mul(ld s, vec a) { return v(s * a.x, s * a.y, s * a.z); }
static ld dot(vec a, vec b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
static vec cross(vec a, vec b) {
  return v(a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x);
}
static ld norm(vec a) { return sqrtl(dot(a, a)); }
static vec unit(vec a) { return mul(1 / norm(a), a); }

static int failures = 0;
static void check(const char *name, int ok, ld err) {
  printf("%s %s (%.3Le)\n", ok ? "ok   " : "FAIL ", name, err);
  if (!ok) failures++;
}

/* parameter index of the edge {i,j}: 0 = e (AB, CD), 1 = f (BC, AD), 2 = g (AC, BD) */
static int param_of(int i, int j) {
  int lo = i < j ? i : j, hi = i < j ? j : i;
  if ((lo == 0 && hi == 1) || (lo == 2 && hi == 3)) return 0;
  if ((lo == 1 && hi == 2) || (lo == 0 && hi == 3)) return 1;
  return 2;
}

/* p-secting plane of the edge YZ towards the face opposite U: m.Q = c */
static void psect(const vec P[4], int Y, int Z, int U, ld p, vec *m, ld *c) {
  int W = 6 - Y - Z - U;
  vec t = unit(sub(P[Z], P[Y]));
  vec wy = sub(P[W], P[Y]), uy = sub(P[U], P[Y]);
  vec vU = unit(sub(wy, mul(dot(wy, t), t)));  /* in the face opposite U */
  vec vW = unit(sub(uy, mul(dot(uy, t), t)));  /* in the face opposite W */
  ld cth = dot(vU, vW);
  if (cth > 1) cth = 1;
  if (cth < -1) cth = -1;
  ld th = acosl(cth), phi = th / p;
  vec d = mul(1 / sinl(th), add(mul(sinl(th - phi), vU), mul(sinl(phi), vW)));
  *m = unit(cross(t, d));
  *c = dot(*m, P[Y]);
}

static ld det3(vec a, vec b, vec c) { return dot(a, cross(b, c)); }

static void morley(const vec P[4], const ld par[3], vec M[4]) {
  for (int X = 0; X < 4; X++) {
    int o[3], k = 0;
    for (int i = 0; i < 4; i++)
      if (i != X) o[k++] = i;
    vec m[3];
    ld c[3];
    for (k = 0; k < 3; k++) {
      int Y = o[k], Z = o[(k + 1) % 3];
      psect(P, Y, Z, X, par[param_of(Y, Z)], &m[k], &c[k]);
    }
    /* solve m[k].Q = c[k] by Cramer's rule */
    vec cx = v(m[0].x, m[1].x, m[2].x), cy = v(m[0].y, m[1].y, m[2].y),
        cz = v(m[0].z, m[1].z, m[2].z), cc = v(c[0], c[1], c[2]);
    ld D = det3(cx, cy, cz);
    M[X] = v(det3(cc, cy, cz) / D, det3(cx, cc, cz) / D, det3(cx, cy, cc) / D);
  }
}

static void iso(ld a, ld b, ld c, vec P[4]) {
  P[0] = v(a, b, c);
  P[1] = v(a, -b, -c);
  P[2] = v(-a, b, -c);
  P[3] = v(-a, -b, c);
}

static ld spread(const vec M[4]) {  /* (max edge - min edge) / max edge */
  ld lo = 1e300L, hi = 0;
  for (int i = 0; i < 4; i++)
    for (int j = i + 1; j < 4; j++) {
      ld d = norm(sub(M[i], M[j]));
      if (d < lo) lo = d;
      if (d > hi) hi = d;
    }
  return (hi - lo) / hi;
}

static ld R(ld p, ld th) { return sinl((p - 1) * th / p) / sinl(th / p); }
static ld p_of(ld rho, ld th) { return th / atan2l(sinl(th), rho + cosl(th)); }

static ld urand(ld lo, ld hi) { return lo + (hi - lo) * (ld)rand() / (ld)RAND_MAX; }

int main(void) {
  srand(20261010);
  vec P[4], M[4];

  /* Example 1.5 */
  {
    ld par[3] = {acosl(-23.0L / 49) / atanl(4 * sqrtl(13.0L) / 25),
                 acosl(41.0L / 49) / atanl(20 * sqrtl(5.0L) / 297),
                 acosl(31.0L / 49) / atanl(5 * sqrtl(10.0L) / 66)};
    iso(1, 2, 3, P);
    morley(P, par, M);
    ld s = 2.0L / 7, err = 0;
    vec E[4] = {v(-s, -s, -s), v(-s, s, s), v(s, -s, s), v(s, s, -s)};
    for (int i = 0; i < 4; i++) err = fmaxl(err, norm(sub(M[i], E[i])));
    check("Example 1.5: vertices (2/7)(-1,-1,-1), ...", err < 1e-15L, err);
  }
  /* Example 1.6 */
  {
    ld r = sqrtl(5.0L / 21);
    ld par[3] = {4, 4, acosl(13.0L / 21) / atanl(2 * sqrtl(17.0L) / (17 + 35 * r))};
    iso(4, 2, 1, P);
    morley(P, par, M);
    ld s = 2.5L - 4.5L * r, err = 0;
    vec E[4] = {v(-s, -s, -s), v(-s, s, s), v(s, -s, s), v(s, s, -s)};
    for (int i = 0; i < 4; i++) err = fmaxl(err, norm(sub(M[i], E[i])));
    check("Example 1.6: vertices s(-1,-1,-1), ..., s = 5/2 - (9/2)sqrt(5/21)", err < 1e-15L, err);
  }
  /* Lemma 2.4 */
  {
    ld worst = 0;
    for (int n = 0; n < 20000; n++) {
      iso(urand(0.3L, 3), urand(0.3L, 3), urand(0.3L, 3), P);
      ld par[3] = {1 + expl(urand(-3, 3)), 1 + expl(urand(-3, 3)), 1 + expl(urand(-3, 3))};
      morley(P, par, M);
      vec A = M[0];
      worst = fmaxl(worst, norm(sub(M[1], v(A.x, -A.y, -A.z))));
      worst = fmaxl(worst, norm(sub(M[2], v(-A.x, A.y, -A.z))));
      worst = fmaxl(worst, norm(sub(M[3], v(-A.x, -A.y, A.z))));
    }
    check("Lemma 2.4: B', C', D' are the half-turns of A' (20000 cases)", worst < 1e-14L, worst);
  }
  /* Theorem 1.3(b) */
  {
    ld worst = 0;
    const int D[4][3] = {{1, 1, 1}, {1, -1, -1}, {-1, 1, -1}, {-1, -1, 1}};
    const int S[4][3] = {{1, 1, 1}, {1, -1, -1}, {-1, 1, -1}, {-1, -1, 1}}; /* signs of L_X */
    for (int n = 0; n < 20000; n++) {
      ld a = urand(0.3L, 3), b = urand(0.3L, 3), c = urand(0.3L, 3);
      ld al = 1 / a, be = 1 / b, ga = 1 / c;
      iso(a, b, c, P);
      const int *d = D[n % 4];
      ld Lmax = 0, Lmin = 0;
      for (int X = 0; X < 4; X++) {
        ld l = S[X][0] * al * d[0] + S[X][1] * be * d[1] + S[X][2] * ga * d[2];
        if (l > Lmax) Lmax = l;
        if (l < Lmin) Lmin = l;
      }
      ld t = urand(-1 / Lmax, 1 / -Lmin) * 0.999L;
      if (fabsl(t) < 1e-4L) continue;
      vec Xp = v(t * d[0], t * d[1], t * d[2]);
      ld L[4];
      for (int X = 0; X < 4; X++)
        L[X] = 1 + S[X][0] * al * Xp.x + S[X][1] * be * Xp.y + S[X][2] * ga * Xp.z;
      ld N2 = al * al + be * be + ga * ga;
      ld cCD = (-al * al + be * be + ga * ga) / N2, cBD = (al * al - be * be + ga * ga) / N2,
         cBC = (al * al + be * be - ga * ga) / N2;
      ld par[3] = {p_of(L[1] / L[0], acosl(cCD)), p_of(L[3] / L[0], acosl(cBC)),
                   p_of(L[2] / L[0], acosl(cBD))};
      morley(P, par, M);
      worst = fmaxl(worst, spread(M) + norm(sub(M[0], Xp)) / (a + b + c));
    }
    check("Theorem 1.3(b): points of the four lines give regular tetrahedra", worst < 1e-12L, worst);
  }
  /* Lemma 2.1 */
  {
    int bad = 0;
    for (int n = 0; n < 100000; n++) {
      ld th = urand(0.01L, 3.13L), p = 1 + expl(urand(-3, 3)), q = p * (1 + urand(1e-6L, 1));
      if (!(R(p, th) < R(q, th))) bad++;
      if ((R(p, th) > 1) != (p > 2) && fabsl(p - 2) > 1e-12L) bad++;
      if (fabsl(p_of(R(p, th), th) - p) > 1e-12L * p) bad++;
    }
    check("Lemma 2.1: monotone, R_p > 1 iff p > 2, inverse formula", bad == 0, (ld)bad);
  }
  if (failures) {
    printf("%d FAILED\n", failures);
    return 1;
  }
  printf("ALL OK\n");
  return 0;
}
