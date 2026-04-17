using LinearAlgebra
using Random

Random.seed!(20260410)

const QUAD_BASIS = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]
const QUARTIC_BASIS = [
    (0, 0),
    (1, 0), (0, 1),
    (2, 0), (1, 1), (0, 2),
    (3, 0), (2, 1), (1, 2), (0, 3),
    (4, 0), (3, 1), (2, 2), (1, 3), (0, 4),
]

function basis_index(basis, key)
    for (i, x) in enumerate(basis)
        if x == key
            return i
        end
    end
    error("missing basis element $(key)")
end

function poly_mul_to_quartic(a::Vector{Float64}, b::Vector{Float64})
    out = zeros(Float64, length(QUARTIC_BASIS))
    for (i, ei) in enumerate(QUAD_BASIS), (j, ej) in enumerate(QUAD_BASIS)
        idx = basis_index(QUARTIC_BASIS, (ei[1] + ej[1], ei[2] + ej[2]))
        out[idx] += a[i] * b[j]
    end
    out
end

function get_Au(u::Vector{Vector{Float64}})
    cols = Vector{Vector{Float64}}()
    for i in 1:length(u), j in 1:length(QUAD_BASIS)
        basis_poly = zeros(Float64, length(QUAD_BASIS))
        basis_poly[j] = 1.0
        push!(cols, poly_mul_to_quartic(u[i], basis_poly))
    end
    reduce(hcat, cols)
end

function image_rank(u::Vector{Vector{Float64}})
    rank(get_Au(u))
end

function missing_monomials(u::Vector{Vector{Float64}})
    Au = get_Au(u)
    r = rank(Au)
    missing = Tuple{Int, Int}[]
    for (idx, m) in enumerate(QUARTIC_BASIS)
        e = zeros(Float64, length(QUARTIC_BASIS))
        e[idx] = 1.0
        if rank(hcat(Au, e)) == r + 1
            push!(missing, m)
        end
    end
    missing
end

function quad_coeffs(; a00 = 0.0, a10 = 0.0, a01 = 0.0, a20 = 0.0, a11 = 0.0, a02 = 0.0)
    [a00, a10, a01, a20, a11, a02]
end

"""
Probe determinant-zero canonical tail models.

After a basis choice in the determinant-zero mixed-affine tail branch, a
natural canonical family is
  u = [1, x0, mu*x0^2 + D, nu*x0^2 + x1]
where D is a homogeneous quadratic line. This script checks representative
choices of D and parameters (mu, nu) using only coefficient linear algebra.
"""
function det_zero_canonical_probe()
    one_poly = quad_coeffs(a00 = 1.0)
    x0 = quad_coeffs(a10 = 1.0)
    x1 = quad_coeffs(a01 = 1.0)
    dirs = [
        ("cross", quad_coeffs(a11 = 1.0)),
        ("x1sq", quad_coeffs(a02 = 1.0)),
        ("sumsq", quad_coeffs(a20 = 1.0, a02 = 1.0)),
        ("diffsq", quad_coeffs(a20 = 1.0, a02 = -1.0)),
    ]
    params = [
        (-2.0, -1.0),
        (-1.0, 1.0),
        (0.0, 1.0),
        (1.0, 1.0),
        (2.0, -1.0),
    ]
    results = NamedTuple[]
    for (name, d) in dirs
        for (mu, nu) in params
            q2 = d .+ mu .* quad_coeffs(a20 = 1.0)
            q3 = x1 .+ nu .* quad_coeffs(a20 = 1.0)
            u = [one_poly, x0, q2, q3]
            result = (
                direction = name,
                mu = mu,
                nu = nu,
                rank = image_rank(u),
                missing = missing_monomials(u),
            )
            println("mixed_affine_det_zero_canonical_probe = ", result)
            push!(results, result)
        end
    end
    results
end

det_zero_canonical_probe()
