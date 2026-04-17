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

function quad_coeffs(; a20 = 0.0, a11 = 0.0, a02 = 0.0)
    [0.0, 0.0, 0.0, a20, a11, a02]
end

function low_affine_hom_plane_random_probe(samples::Int = 20)
    x0 = [0.0, 1.0, 0.0, 0.0, 0.0, 0.0]
    x1 = [0.0, 0.0, 1.0, 0.0, 0.0, 0.0]
    ranks = Int[]
    missing = nothing

    for _ in 1:samples
        C = randn(2, 3)
        rank(C) < 2 && continue
        q2 = quad_coeffs(a20 = C[1, 1], a11 = C[1, 2], a02 = C[1, 3])
        q3 = quad_coeffs(a20 = C[2, 1], a11 = C[2, 2], a02 = C[2, 3])
        data = image_rank_missing([x0, x1, q2, q3])
        push!(ranks, data.rank)
        if missing === nothing
            missing = data.missing
        end
    end

    result = (
        samples = samples,
        ranks = sort(unique(ranks)),
        missing = missing,
    )
    println("low_affine_hom_plane_random_probe = ", result)
    result
end

function low_affine_hom_plane_control_probe()
    x0 = [0.0, 1.0, 0.0, 0.0, 0.0, 0.0]
    x1 = [0.0, 0.0, 1.0, 0.0, 0.0, 0.0]
    result = (
        common_factor = image_rank_missing([x0, x1, quad_coeffs(a20 = 1.0), quad_coeffs(a11 = 1.0)]),
        diagonal = image_rank_missing([x0, x1, quad_coeffs(a20 = 1.0), quad_coeffs(a02 = 1.0)]),
        split = image_rank_missing([x0, x1, quad_coeffs(a11 = 1.0), quad_coeffs(a20 = 1.0, a02 = -1.0)]),
    )
    println("low_affine_hom_plane_control_probe = ", result)
    result
end

low_affine_hom_plane_random_probe()
low_affine_hom_plane_control_probe()
