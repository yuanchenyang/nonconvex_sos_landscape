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

function quad_coeffs(; a00 = 0.0, a10 = 0.0, a01 = 0.0, a20 = 0.0, a11 = 0.0, a02 = 0.0)
    [a00, a10, a01, a20, a11, a02]
end

"""
Probe the determinant-zero mixed-affine tail branch by homogeneous-line slice.

The canonical determinant-zero family has the form
  u = [1, x0, D + mu*x0^2, x1 + nu*x0^2]
with a homogeneous quadratic line
  D = a*x0^2 + b*x0*x1 + c*x1^2.

This script checks:
1. generic random lines D
2. the codimension-one slice c = 0
3. the slice b = 0
4. the discriminant-zero slice D = (u*x0 + v*x1)^2
using only coefficient linear algebra.
"""
function det_zero_slice_probe(samples::Int = 80)
    one_poly = quad_coeffs(a00 = 1.0)
    x0 = quad_coeffs(a10 = 1.0)
    x1 = quad_coeffs(a01 = 1.0)

    function rank_for_line(a, b, c, mu, nu)
        d = quad_coeffs(a20 = a, a11 = b, a02 = c)
        q2 = d .+ mu .* quad_coeffs(a20 = 1.0)
        q3 = x1 .+ nu .* quad_coeffs(a20 = 1.0)
        image_rank([one_poly, x0, q2, q3])
    end

    generic_ranks = Int[]
    c0_ranks = Int[]
    b0_ranks = Int[]
    disc0_ranks = Int[]

    for _ in 1:samples
        a, b, c = randn(), randn(), randn()
        mu, nu = randn(), randn()
        if abs(a) + abs(b) + abs(c) > 1e-8
            push!(generic_ranks, rank_for_line(a, b, c, mu, nu))
        end

        a, b = randn(), randn()
        mu, nu = randn(), randn()
        if abs(b) > 1e-8
            push!(c0_ranks, rank_for_line(a, b, 0.0, mu, nu))
        end

        a, c = randn(), randn()
        mu, nu = randn(), randn()
        if abs(c) > 1e-8
            push!(b0_ranks, rank_for_line(a, 0.0, c, mu, nu))
        end

        u, v = randn(), randn()
        mu, nu = randn(), randn()
        if abs(v) > 1e-8
            push!(disc0_ranks, rank_for_line(u^2, 2 * u * v, v^2, mu, nu))
        end
    end

    result = (
        samples = samples,
        generic_ranks = sort(unique(generic_ranks)),
        c0_ranks = sort(unique(c0_ranks)),
        b0_ranks = sort(unique(b0_ranks)),
        disc0_ranks = sort(unique(disc0_ranks)),
    )
    println("mixed_affine_det_zero_slice_probe = ", result)
    result
end

det_zero_slice_probe()
