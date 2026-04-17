using LinearAlgebra
using Random

Random.seed!(20260412)

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

function quad_coeffs(; a00 = 0.0, a10 = 0.0, a01 = 0.0, a20 = 0.0, a11 = 0.0, a02 = 0.0)
    [a00, a10, a01, a20, a11, a02]
end

function random_common_factor_plane(vals)
    while true
        r = rand(vals)
        s = rand(vals)
        t = rand(vals)
        w = rand(vals)
        if r * w - s * t != 0.0
            q2 = quad_coeffs(a11 = r, a02 = s)
            q3 = quad_coeffs(a11 = t, a02 = w)
            return (r = r, s = s, t = t, w = w, q2 = q2, q3 = q3)
        end
    end
end

function random_tail_hom(vals)
    while true
        a20 = rand(vals)
        a11 = rand(vals)
        a02 = rand(vals)
        if !(a20 == 0.0 && a11 == 0.0 && a02 == 0.0)
            return (a20 = a20, a11 = a11, a02 = a02)
        end
    end
end

function summarize(records)
    (
        count = length(records),
        ranks = sort(unique(x.rank for x in records)),
        missing = sort(unique(x.missing for x in records)),
        exact_affine_dims = sort(unique(x.exact_affine_dim for x in records)),
    )
end

function affine_dim_one_common_factor_chart_probe(; samples = 30)
    vals = [-2.0, -1.0, 0.0, 1.0, 2.0]
    nonzero_vals = [-2.0, -1.0, 1.0, 2.0]
    x0 = quad_coeffs(a10 = 1.0)

    const_m20_nonzero = NamedTuple[]
    const_m20_zero = NamedTuple[]
    x1_m20_nonzero = NamedTuple[]
    x1_m20_zero = NamedTuple[]
    mixed_m20_nonzero = NamedTuple[]
    mixed_m20_zero = NamedTuple[]

    for _ in 1:samples
        plane = random_common_factor_plane(nonzero_vals)
        tail = random_tail_hom(vals)
        b = rand(nonzero_vals)

        u_const = [x0, quad_coeffs(a00 = 1.0, a20 = tail.a20, a11 = tail.a11, a02 = tail.a02), plane.q2, plane.q3]
        u_x1 = [x0, quad_coeffs(a01 = 1.0, a20 = tail.a20, a11 = tail.a11, a02 = tail.a02), plane.q2, plane.q3]
        u_mixed = [x0, quad_coeffs(a00 = 1.0, a01 = b, a20 = tail.a20, a11 = tail.a11, a02 = tail.a02), plane.q2, plane.q3]

        rec_const = (; plane.r, plane.s, plane.t, plane.w, tail.a20, tail.a11, tail.a02,
            exact_affine_dim = exact_affine_dim(u_const), image_rank_missing(u_const)...)
        rec_x1 = (; plane.r, plane.s, plane.t, plane.w, tail.a20, tail.a11, tail.a02,
            exact_affine_dim = exact_affine_dim(u_x1), image_rank_missing(u_x1)...)
        rec_mixed = (; plane.r, plane.s, plane.t, plane.w, b, tail.a20, tail.a11, tail.a02,
            exact_affine_dim = exact_affine_dim(u_mixed), image_rank_missing(u_mixed)...)

        if tail.a20 == 0.0
            push!(const_m20_zero, rec_const)
            push!(x1_m20_zero, rec_x1)
            push!(mixed_m20_zero, rec_mixed)
        else
            push!(const_m20_nonzero, rec_const)
            push!(x1_m20_nonzero, rec_x1)
            push!(mixed_m20_nonzero, rec_mixed)
        end
    end

    result = (
        samples = samples,
        vals = vals,
        const_m20_nonzero = summarize(const_m20_nonzero),
        const_m20_zero = summarize(const_m20_zero),
        x1_m20_nonzero = summarize(x1_m20_nonzero),
        x1_m20_zero = summarize(x1_m20_zero),
        mixed_m20_nonzero = summarize(mixed_m20_nonzero),
        mixed_m20_zero = summarize(mixed_m20_zero),
    )
    println("affine_dim_one_common_factor_chart_probe = ", result)
    result
end

affine_dim_one_common_factor_chart_probe()
