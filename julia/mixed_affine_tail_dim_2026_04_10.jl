using DynamicPolynomials
using LinearAlgebra
using MultivariatePolynomials
using Random

Random.seed!(20260410)

@polyvar x[1:2]

function coeffvec(p)
    [coefficient(p, one(x[1]^2)),
      coefficient(p, x[1]),
      coefficient(p, x[2]),
      coefficient(p, x[1]^2),
      coefficient(p, x[1] * x[2]),
      coefficient(p, x[2]^2)]
end

function coeffmat(u)
    reduce(vcat, [reshape(coeffvec(ui), 1, :) for ui in u])
end

function affdim(u)
    M = coeffmat(u)
    4 - rank(M[:, 4:6])
end

function homdim(u)
    M = coeffmat(u)
    4 - rank(M[:, 1:3])
end

function tail_dim_probe(name, P; n = 20)
    vals = NamedTuple[]
    for _ in 1:n
        tails = [randn() + randn() * x[1] + randn() * x[2] for _ in 1:2]
        u = [1, x[1], P[1] + tails[1], P[2] + tails[2]]
        push!(vals, (affdim = affdim(u), homdim = homdim(u)))
    end
    println("mixed_affine_tail_dim_probe = (case = ", name, ", samples = ", n,
        ", values = ", vals, ")")
    vals
end

tail_dim_probe("rank14_base", [x[1] * x[2], x[2]^2])
tail_dim_probe("rank13_base", [x[1]^2, x[1] * x[2]])
tail_dim_probe("rank15_base", [x[1]^2, x[2]^2])
