using LinearAlgebra
using Random

Random.seed!(20260411)

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

function exact_affine_dim(u::Vector{Vector{Float64}})
    H = reduce(hcat, [ui[4:6] for ui in u])
    F = svd(H)
    r = sum(F.S .> 1e-9)
    4 - r
end

function matrix_rank(M::Matrix{Float64})
    F = svd(M)
    sum(F.S .> 1e-9)
end

function quad_coeffs(; a00 = 0.0, a10 = 0.0, a01 = 0.0, a20 = 0.0, a11 = 0.0, a02 = 0.0)
    [a00, a10, a01, a20, a11, a02]
end

function rank_one_tail_family(λ::Vector{Float64}, a::Float64, b::Float64)
    [
        quad_coeffs(a10 = 1.0),
        quad_coeffs(a00 = λ[1] * a, a01 = λ[1] * b, a20 = 1.0),
        quad_coeffs(a00 = λ[2] * a, a01 = λ[2] * b, a11 = 1.0),
        quad_coeffs(a00 = λ[3] * a, a01 = λ[3] * b, a02 = 1.0),
    ]
end

function probe_rank_one_tail(; samples = 20)
    mixed = NamedTuple[]
    const_only = NamedTuple[]
    linear_only = NamedTuple[]

    while length(mixed) < samples
        λ = randn(3)
        a = randn()
        b = randn()
        abs(a) + abs(b) < 1e-6 && continue
        u = rank_one_tail_family(λ, a, b)
        push!(mixed, (;
            λ = λ,
            tail_rank = matrix_rank([λ[1] * a λ[1] * b; λ[2] * a λ[2] * b; λ[3] * a λ[3] * b]),
            exact_affine_dim = exact_affine_dim(u),
            image_rank_missing(u)...,
        ))
    end

    for _ in 1:samples
        λ = randn(3)
        u_const = rank_one_tail_family(λ, 1.0, 0.0)
        push!(const_only, (;
            λ = λ,
            tail_rank = 1,
            exact_affine_dim = exact_affine_dim(u_const),
            image_rank_missing(u_const)...,
        ))

        u_linear = rank_one_tail_family(λ, 0.0, 1.0)
        push!(linear_only, (;
            λ = λ,
            tail_rank = 1,
            exact_affine_dim = exact_affine_dim(u_linear),
            image_rank_missing(u_linear)...,
        ))
    end

    result = (
        samples = samples,
        mixed_tail_ranks = sort(unique(x.tail_rank for x in mixed)),
        mixed_exact_affine_dims = sort(unique(x.exact_affine_dim for x in mixed)),
        mixed_image_ranks = sort(unique(x.rank for x in mixed)),
        mixed_missing = sort(unique(x.missing for x in mixed)),
        const_tail_ranks = sort(unique(x.tail_rank for x in const_only)),
        const_exact_affine_dims = sort(unique(x.exact_affine_dim for x in const_only)),
        const_image_ranks = sort(unique(x.rank for x in const_only)),
        const_missing = sort(unique(x.missing for x in const_only)),
        linear_tail_ranks = sort(unique(x.tail_rank for x in linear_only)),
        linear_exact_affine_dims = sort(unique(x.exact_affine_dim for x in linear_only)),
        linear_image_ranks = sort(unique(x.rank for x in linear_only)),
        linear_missing = sort(unique(x.missing for x in linear_only)),
    )
    println("affine_dim_one_tail_rank_one_probe = ", result)
    result
end

probe_rank_one_tail()
