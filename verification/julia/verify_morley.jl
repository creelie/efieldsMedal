# verify_morley.jl -- 256-bit checks of "Regular Morley tetrahedra from p-secting planes".
#
# Here X' is computed from the distance form (2.2) of Lemma 2.2: it solves
#   d_Y(P) = R_p(theta_{YZ}) d_X(P)   for the three vertices Y != X,
# where theta_{YZ} is the angle at the edge F_X ∩ F_Y.  (verify_morley.py and morley.c use
# the rotated planes of Definition 1.1 instead.)  Checks, in BigFloat with 256 bits:
#   Examples 1.5 and 1.6 to 70 digits;
#   Proposition 2.3 (interior point, round trip) and Lemma 2.4 on random tetrahedra;
#   Theorem 1.3(a): regular iff x^2 = y^2 = z^2 for random parameters, and (b);
#   Theorem 1.7: e = f = g = 4 on a grid of isosceles shapes, and the regular case.
# Prints ALL OK on success.   julia verify_morley.jl
using LinearAlgebra
using Random

setprecision(BigFloat, 256)
const B = BigFloat
Random.seed!(20261010)
failures = 0
function check(name, ok, detail = "")
    global failures
    println(ok ? "ok    " : "FAIL  ", name, isempty(detail) ? "" : "  ($detail)")
    ok || (failures += 1)
end

# parameter index of an edge: 1 = e (AB, CD), 2 = f (BC, AD), 3 = g (AC, BD)
function param_of(i, j)
    s = Set((i, j))
    s == Set((1, 2)) || s == Set((3, 4)) ? 1 : s == Set((2, 3)) || s == Set((1, 4)) ? 2 : 3
end

# inward unit normals and offsets: d_X(P) = n[X] ⋅ P + o[X]
function faces(P)
    n = Vector{Vector{B}}(undef, 4)
    o = Vector{B}(undef, 4)
    for X in 1:4
        f = [P[k] for k in 1:4 if k != X]
        m = cross(f[2] - f[1], f[3] - f[1])
        m /= norm(m)
        if dot(m, P[X] - f[1]) < 0
            m = -m
        end
        n[X] = m
        o[X] = -dot(m, f[1])
    end
    n, o
end

Rp(p, th) = sin((p - 1) * th / p) / sin(th / p)
p_of(rho, th) = th / atan(sin(th), rho + cos(th))

function morley(P, par)
    n, o = faces(P)
    M = Vector{Vector{B}}(undef, 4)
    for X in 1:4
        rows = Vector{Vector{B}}()
        rhs = B[]
        for Y in 1:4
            Y == X && continue
            # the edge F_X ∩ F_Y joins the two vertices other than X and Y
            Z1, Z2 = [k for k in 1:4 if k != X && k != Y]
            th = acos(-dot(n[X], n[Y]))
            rho = Rp(par[param_of(Z1, Z2)], th)
            push!(rows, n[Y] - rho * n[X])
            push!(rhs, rho * o[X] - o[Y])
        end
        M[X] = permutedims(hcat(rows...)) \ rhs
    end
    M
end

iso(a, b, c) = [B[a, b, c], B[a, -b, -c], B[-a, b, -c], B[-a, -b, c]]
edges(M) = [norm(M[i] - M[j]) for i in 1:4 for j in i+1:4]
spread(M) = (E = edges(M); (maximum(E) - minimum(E)) / maximum(E))
urand(lo, hi) = B(lo) + (B(hi) - B(lo)) * B(rand())
rpar() = 1 + exp(urand(-3, 3))

function params_of_point(P, Q)
    n, o = faces(P)
    d = [dot(n[X], Q) + o[X] for X in 1:4]
    th(Y) = acos(-dot(n[1], n[Y]))  # edge F_A ∩ F_Y
    # e from CD = F_A ∩ F_B, f from BC = F_A ∩ F_D, g from BD = F_A ∩ F_C
    [p_of(d[2] / d[1], th(2)), p_of(d[4] / d[1], th(4)), p_of(d[3] / d[1], th(3))]
end

# Example 1.5
let
    par = [acos(B(-23) / 49) / atan(4 * sqrt(B(13)) / 25),
           acos(B(41) / 49) / atan(20 * sqrt(B(5)) / 297),
           acos(B(31) / 49) / atan(5 * sqrt(B(10)) / 66)]
    M = morley(iso(1, 2, 3), par)
    s = B(2) / 7
    E = [s * B[-1, -1, -1], s * B[-1, 1, 1], s * B[1, -1, 1], s * B[1, 1, -1]]
    err = maximum(norm(M[i] - E[i]) for i in 1:4)
    check("Example 1.5 to 70 digits", err < B(10)^-70, string(Float64(err)))
end
# Example 1.6
let
    r = sqrt(B(5) / 21)
    par = [B(4), B(4), acos(B(13) / 21) / atan(2 * sqrt(B(17)) / (17 + 35 * r))]
    M = morley(iso(4, 2, 1), par)
    s = B(5) / 2 - B(9) / 2 * r
    E = [s * B[-1, -1, -1], s * B[-1, 1, 1], s * B[1, -1, 1], s * B[1, 1, -1]]
    err = maximum(norm(M[i] - E[i]) for i in 1:4)
    check("Example 1.6 to 70 digits", err < B(10)^-70, string(Float64(err)))
end
# Proposition 2.3 and Lemma 2.4
let
    worst_in, worst_back, worst_turn = B(Inf), B(0), B(0)
    for k in 1:300
        P = [B.(randn(3)) for _ in 1:4]
        abs(det(hcat(P[2] - P[1], P[3] - P[1], P[4] - P[1]))) < 0.3 && continue
        n, o = faces(P)
        par = [rpar(), rpar(), rpar()]
        A1 = morley(P, par)[1]
        worst_in = min(worst_in, minimum(dot(n[X], A1) + o[X] for X in 1:4))
        w = B.(rand(4)); w /= sum(w)
        Q = sum(w[i] * P[i] for i in 1:4)
        A2 = morley(P, params_of_point(P, Q))[1]
        worst_back = max(worst_back, norm(A2 - Q))
        a, b, c = urand(0.3, 3), urand(0.3, 3), urand(0.3, 3)
        M = morley(iso(a, b, c), par)
        x, y, z = M[1]
        worst_turn = max(worst_turn, norm(M[2] - [x, -y, -z]), norm(M[3] - [-x, y, -z]),
                         norm(M[4] - [-x, -y, z]))
    end
    check("Prop. 2.3: A' interior", worst_in > 0, string(Float64(worst_in)))
    check("Prop. 2.3: round trip P -> (e,f,g) -> A'", worst_back < B(10)^-60, string(Float64(worst_back)))
    check("Lemma 2.4: half-turns", worst_turn < B(10)^-60, string(Float64(worst_turn)))
end
# Theorem 1.3
let
    wrong, worst = 0, B(0)
    deltas = [B[1, 1, 1], B[1, -1, -1], B[-1, 1, -1], B[-1, -1, 1]]
    for k in 1:300
        a, b, c = urand(0.3, 3), urand(0.3, 3), urand(0.3, 3)
        M = morley(iso(a, b, c), [rpar(), rpar(), rpar()])
        x, y, z = M[1]
        online = abs(x^2 - y^2) < B(10)^-50 && abs(y^2 - z^2) < B(10)^-50
        wrong += (spread(M) < B(10)^-50) != online
        d = deltas[mod1(k, 4)]
        al, be, ga = 1 / a, 1 / b, 1 / c
        l = [dot(B[s1 * al, s2 * be, s3 * ga], d) for (s1, s2, s3) in
             ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))]
        t = urand(-1 / maximum(l), 1 / maximum(-l)) * B("0.999")
        abs(t) < 1e-4 && continue
        X = t * d
        P = iso(a, b, c)
        M = morley(P, params_of_point(P, X))
        worst = max(worst, spread(M) + norm(M[1] - X))
    end
    check("Theorem 1.3(a): regular iff A' on a line (random parameters)", wrong == 0)
    check("Theorem 1.3(b): the lines give regular tetrahedra", worst < B(10)^-60, string(Float64(worst)))
end
# Theorem 1.7
let
    worst_ratio = B(Inf)
    for lb in range(-1.2, 1.2, length = 25), lc in range(-1.2, 1.2, length = 25)
        nr = max(abs(lb), abs(lc), abs(lb - lc))
        nr < 1e-9 && continue
        M = morley(iso(1, exp(B(lb)), exp(B(lc))), B[4, 4, 4])
        x, y, z = abs.(M[1])
        off = (abs(x - y) + abs(y - z)) / (x + y + z)
        worst_ratio = min(worst_ratio, off / B(nr)^2)
    end
    check("Theorem 1.7: e=f=g=4 keeps A' off the lines unless regular (25x25 grid)",
          worst_ratio > 0.01, string(Float64(worst_ratio)))
    M = morley(iso(1, 1, 1), B[4, 4, 4])
    check("Theorem 1.7: the regular tetrahedron gives a regular M_{4,4,4}", spread(M) < B(10)^-70)
end

if failures > 0
    println(failures, " FAILED")
    exit(1)
end
println("ALL OK")
