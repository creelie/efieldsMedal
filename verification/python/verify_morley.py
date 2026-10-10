#!/usr/bin/env python3
"""verify_morley.py -- numerical checks of "Regular Morley tetrahedra from p-secting planes".

The Morley tetrahedron is built here directly from Definition 1.1: each p-secting plane is
spanned by its edge and by the direction obtained by turning the face F towards the other
face through the edge by the angle theta/p.  Nothing below uses the distance formulas of
Section 2, so the checks of Lemma 2.2 and Proposition 2.3 are not circular.

Checks (each prints a line; the script ends with ALL OK or exits with status 1):
  Lemma 2.1      R_p increasing in p, R_p > 1 iff p > 2, the inverse formula p = theta/phi
  Lemma 2.2      points of the p-secting plane satisfy d_W = R_p(theta) d_U
  Prop. 2.3      A' is interior; P -> (e,f,g) -> A' gives back P (random tetrahedra)
  after 2.3      A' = B' is impossible unless e = 2
  Lemma 2.4      an isometry carries the Morley tetrahedron along; the half-turns of an
                 isosceles tetrahedron map A' to B', C', D'
  Remark 2.5     measuring from the other face replaces p by p/(p-1)
  Theorem 1.3    regular iff A' on one of the four lines; every point of the lines occurs
  Corollary 1.4  three different edge lengths, no pair with four equal cross edges
  Lemma 3.1      the bimedians put a moved isosceles tetrahedron back in its box
  Examples 1.5, 1.6 (floating point)
  Theorem 1.7    e = f = g = 4: a scan of isosceles tetrahedra finds A' on a line only
                 near the regular one; the table of w's and the identity for r(u,v)

Needs numpy.  Usage: python3 verify_morley.py [number of random trials, default 2000]
"""
import math
import sys

import numpy as np

RNG = np.random.default_rng(20261010)
FAILED = []


def check(name, cond, detail=""):
    print(("ok    " if cond else "FAIL  ") + name + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILED.append(name)


# --------------------------------------------------------------------------- geometry
V = "ABCD"
# parameter attached to an edge: e on AB, CD; f on BC, AD; g on AC, BD
EDGE_PARAM = {frozenset("AB"): "e", frozenset("CD"): "e", frozenset("BC"): "f",
              frozenset("AD"): "f", frozenset("AC"): "g", frozenset("BD"): "g"}


def face_normal(P, X):
    """Inward unit normal of the face opposite X (pointing towards X)."""
    i = V.index(X)
    f = [P[k] for k in range(4) if k != i]
    n = np.cross(f[1] - f[0], f[2] - f[0])
    n /= np.linalg.norm(n)
    if np.dot(n, P[i] - f[0]) < 0:
        n = -n
    return n


def dist(P, X, Q):
    """Signed distance from Q to the plane of the face opposite X, positive towards X."""
    i = V.index(X)
    j = (i + 1) % 4
    return float(np.dot(face_normal(P, X), Q - P[j]))


def dihedral(P, Y, Z):
    """Interior dihedral angle at the edge YZ."""
    U, W = [X for X in V if X not in (Y, Z)]
    return math.acos(max(-1.0, min(1.0, -np.dot(face_normal(P, U), face_normal(P, W)))))


def psect_plane(P, Y, Z, U, p):
    """The p-secting plane of YZ towards the face F_U (the face through Y, Z, W), as (m, c)
    with m.Q = c.  Built by turning F_U about YZ by theta/p towards the other face."""
    W = [X for X in V if X not in (Y, Z, U)][0]
    y, z, w, u = (P[V.index(X)] for X in (Y, Z, W, U))
    t = (z - y) / np.linalg.norm(z - y)
    # in-face unit vectors orthogonal to the edge: F_U contains W, F_W contains U
    vU = (w - y) - np.dot(w - y, t) * t
    vU /= np.linalg.norm(vU)
    vW = (u - y) - np.dot(u - y, t) * t
    vW /= np.linalg.norm(vW)
    th = math.acos(max(-1.0, min(1.0, float(np.dot(vU, vW)))))
    phi = th / p
    d = (math.sin(th - phi) * vU + math.sin(phi) * vW) / math.sin(th)
    m = np.cross(t, d)
    m /= np.linalg.norm(m)
    return m, float(np.dot(m, y)), d


def morley_vertex(P, X, params):
    """X' : the common point of the three p-secting planes towards F_X."""
    others = [Y for Y in V if Y != X]
    rows, rhs = [], []
    for k in range(3):
        Y, Z = others[k], others[(k + 1) % 3]
        p = params[EDGE_PARAM[frozenset(Y + Z)]]
        m, c, _ = psect_plane(P, Y, Z, X, p)
        rows.append(m)
        rhs.append(c)
    return np.linalg.solve(np.array(rows), np.array(rhs))


def morley(P, e, f, g):
    params = {"e": e, "f": f, "g": g}
    return np.array([morley_vertex(P, X, params) for X in V])


def edges(Q):
    return np.array([np.linalg.norm(Q[i] - Q[j]) for i in range(4) for j in range(i + 1, 4)])


def R(p, th):
    return math.sin((p - 1) * th / p) / math.sin(th / p)


def p_from_ratio(rho, th):
    """Lemma 2.1: the p > 1 with R_p(theta) = rho."""
    phi = math.atan2(math.sin(th), rho + math.cos(th))
    return th / phi


def random_tetra():
    while True:
        P = RNG.normal(size=(4, 3))
        vol = abs(np.linalg.det(P[1:] - P[0])) / 6
        if vol > 0.05 and min(edges(P)) > 0.3:
            return P


def iso(a, b, c):
    return np.array([[a, b, c], [a, -b, -c], [-a, b, -c], [-a, -b, c]], float)


def params_of_point(P, Q):
    """Proposition 2.3: the parameters (e, f, g) for which A' = Q."""
    dA, dB, dC, dD = (dist(P, X, Q) for X in V)
    e = p_from_ratio(dB / dA, dihedral(P, "C", "D"))
    g = p_from_ratio(dC / dA, dihedral(P, "B", "D"))
    f = p_from_ratio(dD / dA, dihedral(P, "B", "C"))
    return e, f, g


def random_interior(P):
    w = RNG.dirichlet(np.ones(4))
    return w @ P


def rand_param():
    return 1 + math.exp(RNG.uniform(-3, 3))


# --------------------------------------------------------------------------- checks
def lemma_2_1(n):
    worst_mono, worst_inv, bad_gt = -math.inf, 0.0, 0
    for _ in range(n):
        th = RNG.uniform(0.01, math.pi - 0.01)
        p1, p2 = sorted((rand_param(), rand_param()))
        if p2 - p1 > 1e-9:
            worst_mono = max(worst_mono, R(p1, th) - R(p2, th))
        p = rand_param()
        worst_inv = max(worst_inv, abs(p_from_ratio(R(p, th), th) - p) / p)
        if (R(p, th) > 1) != (p > 2) and abs(p - 2) > 1e-9:
            bad_gt += 1
    check("Lemma 2.1: R_p increasing in p", worst_mono < 0)
    check("Lemma 2.1: inverse formula", worst_inv < 1e-9, f"rel. error {worst_inv:.1e}")
    check("Lemma 2.1: R_p > 1 iff p > 2", bad_gt == 0)


def lemma_2_2(n):
    worst = 0.0
    for _ in range(n):
        P = random_tetra()
        Y, Z = RNG.choice(list(V), 2, replace=False)
        U = RNG.choice([X for X in V if X not in (Y, Z)])
        W = [X for X in V if X not in (Y, Z, U)][0]
        p = rand_param()
        m, c, d = psect_plane(P, Y, Z, U, p)
        th = dihedral(P, Y, Z)
        y, z = P[V.index(Y)], P[V.index(Z)]
        Q = y + RNG.uniform(-2, 2) * (z - y) + RNG.uniform(-2, 2) * d
        # F_U is the face opposite U, so d_U is the distance to it
        lhs, rhs = dist(P, W, Q), R(p, th) * dist(P, U, Q)
        worst = max(worst, abs(lhs - rhs) / (1 + abs(lhs)))
    check("Lemma 2.2: d_W = R_p d_U on the p-secting plane towards F_U", worst < 1e-9,
          f"max error {worst:.1e}")


def prop_2_3(n):
    worst_back, min_inside = 0.0, math.inf
    for _ in range(n):
        P = random_tetra()
        e, f, g = rand_param(), rand_param(), rand_param()
        A1 = morley_vertex(P, "A", {"e": e, "f": f, "g": g})
        scale = np.linalg.norm(P[0] - P[1])
        min_inside = min(min_inside, min(dist(P, X, A1) for X in V) / scale)
        Q = random_interior(P)
        e2, f2, g2 = params_of_point(P, Q)
        A2 = morley_vertex(P, "A", {"e": e2, "f": f2, "g": g2})
        worst_back = max(worst_back, np.linalg.norm(A2 - Q) / scale)
    check("Prop. 2.3: A' lies in the interior", min_inside > 0, f"min distance {min_inside:.1e}")
    check("Prop. 2.3: P -> (e,f,g) -> A' returns P", worst_back < 1e-8, f"max error {worst_back:.1e}")


def coincidence(n):
    bad = 0
    for _ in range(n):
        P = random_tetra()
        e = rand_param()
        if abs(e - 2) < 1e-3:
            continue
        Q = morley(P, e, rand_param(), rand_param())
        if np.linalg.norm(Q[0] - Q[1]) < 1e-9:
            bad += 1
    check("after Prop. 2.3: A' != B' when e != 2", bad == 0)


def random_isometry():
    Qm, _ = np.linalg.qr(RNG.normal(size=(3, 3)))
    if RNG.uniform() < 0.5:
        Qm[:, 0] = -Qm[:, 0]          # include reflections
    return Qm, RNG.normal(size=3)


def lemma_2_4(n):
    worst = 0.0
    for _ in range(n):
        P = random_tetra()
        e, f, g = rand_param(), rand_param(), rand_param()
        Qm, o = random_isometry()
        moved = P @ Qm.T + o
        worst = max(worst, np.max(np.abs(morley(moved, e, f, g) - (morley(P, e, f, g) @ Qm.T + o))))
    check("Lemma 2.4: an isometry maps M(ABCD) to M of the image", worst < 1e-8,
          f"max error {worst:.1e}")
    worst = 0.0
    for _ in range(n):
        a, b, c = RNG.uniform(0.3, 3, size=3)
        P = iso(a, b, c)
        Q = morley(P, rand_param(), rand_param(), rand_param())
        x, y, z = Q[0]
        for k, img in ((1, (x, -y, -z)), (2, (-x, y, -z)), (3, (-x, -y, z))):
            worst = max(worst, np.linalg.norm(Q[k] - np.array(img)))
    check("Lemma 2.4: B', C', D' are the half-turns of A'", worst < 1e-9, f"max error {worst:.1e}")


def lemma_3_1(n):
    worst_orth, worst_box = 0.0, 0.0
    for _ in range(n):
        a, b, c = RNG.uniform(0.3, 3, size=3)
        Qm, o = random_isometry()
        A, B, C, D = iso(a, b, c) @ Qm.T + o
        O = (A + B + C + D) / 4
        u = [(A + B - C - D) / 4, (A - B + C - D) / 4, (A - B - C + D) / 4]
        worst_orth = max(worst_orth, abs(u[0] @ u[1]), abs(u[0] @ u[2]), abs(u[1] @ u[2]))
        ln = [np.linalg.norm(v) for v in u]
        h = lambda X: np.array([(X - O) @ u[i] / ln[i] for i in range(3)])
        img = np.array([h(X) for X in (A, B, C, D)])
        worst_box = max(worst_box, np.max(np.abs(img - iso(*ln))), abs(ln[0] - a) + abs(ln[1] - b) + abs(ln[2] - c))
    check("Lemma 3.1: the half-bimedians of an isosceles tetrahedron are orthogonal", worst_orth < 1e-9,
          f"max |u_i.u_j| {worst_orth:.1e}")
    check("Lemma 3.1: h maps A, B, C, D to (1.1) in this order", worst_box < 1e-9,
          f"max error {worst_box:.1e}")


def remark_2_5(n):
    worst = 0.0
    for _ in range(n):
        P = random_tetra()
        Y, Z = RNG.choice(list(V), 2, replace=False)
        U, W = [X for X in V if X not in (Y, Z)]
        p = rand_param()
        m1, c1, _ = psect_plane(P, Y, Z, U, p)              # angle theta/p from F_U
        m2, c2, _ = psect_plane(P, Y, Z, W, p / (p - 1))    # angle theta(p-1)/p from F_U
        s = 1.0 if np.dot(m1, m2) > 0 else -1.0
        worst = max(worst, np.linalg.norm(m1 - s * m2) + abs(c1 - s * c2))
    check("Remark 2.5: other face <-> p/(p-1)", worst < 1e-9, f"max error {worst:.1e}")


def theorem_1_3(n):
    worst_formula, wrong = 0.0, 0
    for _ in range(n):
        a, b, c = RNG.uniform(0.3, 3, size=3)
        P = iso(a, b, c)
        Q = morley(P, rand_param(), rand_param(), rand_param())
        x, y, z = Q[0]
        E = edges(Q)  # AB AC AD BC BD CD
        expect = 2 * np.sqrt([y * y + z * z, x * x + z * z, x * x + y * y,
                              x * x + y * y, x * x + z * z, y * y + z * z])
        worst_formula = max(worst_formula, np.max(np.abs(E - expect)))
        regular = np.ptp(E) < 1e-9 * E.max()
        online = abs(x * x - y * y) < 1e-9 and abs(y * y - z * z) < 1e-9
        wrong += regular != online
    check("Theorem 1.3(a): edge lengths 2*sqrt(y^2+z^2), ...", worst_formula < 1e-9,
          f"max error {worst_formula:.1e}")
    check("Theorem 1.3(a): random parameters are not regular unless A' is on a line", wrong == 0)
    worst_reg, count = 0.0, 0
    deltas = np.array([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], float)
    for _ in range(n):
        a, b, c = RNG.uniform(0.3, 3, size=3)
        P = iso(a, b, c)
        d = deltas[RNG.integers(4)]
        al, be, ga = 1 / a, 1 / b, 1 / c
        # largest |t| with t*d in the interior: all L_X(t d) > 0
        L = np.array([[al, be, ga], [al, -be, -ga], [-al, be, -ga], [-al, -be, ga]]) @ d
        tmax = 1 / L.max()
        tmin = -1 / (-L).max()
        t = RNG.uniform(tmin, tmax) * 0.999
        if abs(t) < 1e-6:
            continue
        X = t * d
        e, f, g = params_of_point(P, X)
        Q = morley(P, e, f, g)
        E = edges(Q)
        worst_reg = max(worst_reg, np.ptp(E) / E.max() + np.linalg.norm(Q[0] - X))
        count += 1
    check("Theorem 1.3(b): every point of the lines gives a regular A'B'C'D'", worst_reg < 1e-8,
          f"{count} points, max error {worst_reg:.1e}")


def corollary_1_4():
    a, b, c = 1.0, 2.0, 3.0
    P = iso(a, b, c)
    E = dict(zip(["AB", "AC", "AD", "BC", "BD", "CD"], edges(P)))
    ok = True
    for pair, cross in ((("AB", "CD"), ("AC", "AD", "BC", "BD")),
                        (("AC", "BD"), ("AB", "AD", "BC", "CD")),
                        (("AD", "BC"), ("AB", "AC", "BD", "CD"))):
        vals = [E[k] for k in cross]
        ok &= max(vals) - min(vals) > 0.1
    ok &= len({round(v, 9) for v in E.values()}) == 3
    check("Corollary 1.4: (1,2,3) has three lengths and no four equal cross edges", ok)


def examples():
    # Example 1.5
    P = iso(1, 2, 3)
    e = math.acos(-23 / 49) / math.atan(4 * math.sqrt(13) / 25)
    f = math.acos(41 / 49) / math.atan(20 * math.sqrt(5) / 297)
    g = math.acos(31 / 49) / math.atan(5 * math.sqrt(10) / 66)
    Q = morley(P, e, f, g)
    expect = 2 / 7 * np.array([[-1, -1, -1], [-1, 1, 1], [1, -1, 1], [1, 1, -1]])
    err = np.max(np.abs(Q - expect))
    check("Example 1.5: e, f, g ~ 3.9358, 3.8775, 3.7673",
          abs(e - 3.9358) < 5e-5 and abs(f - 3.8775) < 5e-5 and abs(g - 3.7673) < 5e-5,
          f"{e:.6f} {f:.6f} {g:.6f}")
    check("Example 1.5: the vertices are (2/7)(-1,-1,-1), ...", err < 1e-12, f"max error {err:.1e}")
    # Example 1.6
    P = iso(4, 2, 1)
    r = math.sqrt(5 / 21)
    g = math.acos(13 / 21) / math.atan(2 * math.sqrt(17) / (17 + 35 * r))
    s = 5 / 2 - 9 / 2 * r
    Q = morley(P, 4, 4, g)
    expect = s * np.array([[-1, -1, -1], [-1, 1, 1], [1, -1, 1], [1, 1, -1]])
    err = np.max(np.abs(Q - expect))
    check("Example 1.6: g ~ 3.8046, s ~ 0.3042", abs(g - 3.8046) < 5e-5 and abs(s - 0.3042) < 5e-5,
          f"g={g:.6f} s={s:.6f}")
    check("Example 1.6: the vertices are s(-1,-1,-1), ...", err < 1e-12, f"max error {err:.1e}")


def theorem_1_7(n):
    # the identity for r(u,v) and the table of w's, at random points
    worst = 0.0
    for _ in range(n):
        u, v, w = RNG.uniform(0.1, 5, size=3)
        r = lambda x, y: x * y / (x + y) ** 2
        lhs = r(u, v) - r(u, w)
        rhs = u * (v - w) * (u * u - v * w) / ((u + v) ** 2 * (u + w) ** 2)
        worst = max(worst, abs(lhs - rhs))
    check("Theorem 1.7: r(u,v) - r(u,w) identity", worst < 1e-12)
    worst = 0.0
    for _ in range(n):
        al, be, ga = RNG.uniform(0.2, 3, size=3)
        t = RNG.uniform(-0.2, 0.2)
        table = {(1, 1, 1): (be + ga, al + ga, al + be),
                 (1, -1, -1): (-be - ga, al - ga, al - be),
                 (-1, 1, -1): (be - ga, -al - ga, be - al),
                 (-1, -1, 1): (ga - be, ga - al, -al - be)}
        for dlt, ws in table.items():
            x, y, z = t * np.array(dlt, float)
            LA = 1 + al * x + be * y + ga * z
            LB = 1 + al * x - be * y - ga * z
            LC = 1 - al * x + be * y - ga * z
            LD = 1 - al * x - be * y + ga * z
            for Lx, wE in zip((LB, LC, LD), ws):
                worst = max(worst, abs((Lx - LA) - (-2 * t * wE)))
    check("Theorem 1.7: the table of w_E", worst < 1e-12)
    # scan: for e = f = g = 4, measure how far A' is from the four lines.  Near the regular
    # tetrahedron the distance vanishes to second order, so the test compares it with the
    # square of the distance from regular.
    worst_ratio = math.inf
    grid = np.linspace(-1.2, 1.2, 41)
    for lb in grid:
        for lc in grid:
            a, b, c = 1.0, math.exp(lb), math.exp(lc)
            Q = morley(iso(a, b, c), 4, 4, 4)
            x, y, z = np.abs(Q[0])
            off = (abs(x - y) + abs(y - z)) / (x + y + z)
            nonreg = max(abs(lb), abs(lc), abs(lb - lc))
            if nonreg > 1e-9:
                worst_ratio = min(worst_ratio, off / nonreg ** 2)
    check("Theorem 1.7: e=f=g=4 on a 41x41 grid of isosceles shapes: A' is off the lines "
          "unless regular", worst_ratio > 0.01,
          f"min distance / (log-distance from regular)^2 = {worst_ratio:.3f}")
    Q = morley(iso(1, 1, 1), 4, 4, 4)
    E = edges(Q)
    check("Theorem 1.7: the regular tetrahedron gives a regular M_{4,4,4}", np.ptp(E) < 1e-12 * E.max())


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    lemma_2_1(n)
    lemma_2_2(n)
    prop_2_3(n)
    coincidence(n // 4)
    lemma_2_4(n)
    remark_2_5(n)
    theorem_1_3(n)
    corollary_1_4()
    lemma_3_1(n)
    examples()
    theorem_1_7(n)
    if FAILED:
        print("FAILED:", ", ".join(FAILED))
        sys.exit(1)
    print("ALL OK")


if __name__ == "__main__":
    main()
