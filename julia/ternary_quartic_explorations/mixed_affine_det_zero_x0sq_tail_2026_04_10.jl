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

function image_rank_missing(u::Vector{Vector{Float64}})
    A = get_Au(u)
    F = svd(A)
    r = sum(F.S .> 1e-9)
    U = F.U[:, 1:r]
    missing = Tuple{Int, Int}[]
    for (i, m) in enumerate(QUARTIC_BASIS)
        e = zeros(Float64, length(QUARTIC_BASIS))
        e[i] = 1.0
        if norm(e - U * (transpose(U) * e)) > 1e-8
            push!(missing, m)
        end
    end
    (rank = r, missing = missing)
end

function quad_coeffs(; a00 = 0.0, a10 = 0.0, a01 = 0.0, a20 = 0.0, a11 = 0.0, a02 = 0.0)
    [a00, a10, a01, a20, a11, a02]
end

"""
Probe the determinant-zero mixed-affine subfamily whose extracted line
`H(q2,q3)` is pure `x0^2`.

The general coefficient model is
  q2 = b2*x1 + a2*x0^2 + c*x0*x1 + d*x1^2
  q3 = b3*x1 + a3*x0^2 + (b3/b2)*c*x0*x1 + (b3/b2)*d*x1^2,
with `b2,b3 != 0`, so that
  b3*q2 - b2*q3 = (b3*a2 - b2*a3) * x0^2.

We compare:
1. the generic slice `(c,d) != (0,0)`
2. the low-affine special slice `c = d = 0`
"""
function pure_x0sq_tail_probe(samples::Int = 20)
    one_poly = quad_coeffs(a00 = 1.0)
    x0 = quad_coeffs(a10 = 1.0)

    generic_ranks = Int[]
    low_affine_ranks = Int[]
    low_affine_missing = nothing

    for _ in 1:samples
        b2 = randn()
        b3 = randn()
        if abs(b2) < 1e-6 || abs(b3) < 1e-6
            continue
        end

        a2, a3 = randn(), randn()
        c, d = randn(), randn()
        if abs(c) + abs(d) > 1e-8
            q2 = quad_coeffs(a01 = b2, a20 = a2, a11 = c, a02 = d)
            q3 = quad_coeffs(a01 = b3, a20 = a3, a11 = (b3 / b2) * c, a02 = (b3 / b2) * d)
            push!(generic_ranks, image_rank_missing([one_poly, x0, q2, q3]).rank)
        end

        a2, a3 = randn(), randn()
        q2 = quad_coeffs(a01 = b2, a20 = a2)
        q3 = quad_coeffs(a01 = b3, a20 = a3)
        low = image_rank_missing([one_poly, x0, q2, q3])
        push!(low_affine_ranks, low.rank)
        if low_affine_missing === nothing
            low_affine_missing = low.missing
        end
    end

    result = (
        samples = samples,
        generic_ranks = sort(unique(generic_ranks)),
        low_affine_ranks = sort(unique(low_affine_ranks)),
        low_affine_missing = low_affine_missing,
    )
    println("mixed_affine_det_zero_x0sq_tail_probe = ", result)
    result
end

pure_x0sq_tail_probe()
