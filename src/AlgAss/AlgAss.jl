import Base.split

export wedderburn_decomposition

################################################################################
#
#  Basic field access
#
################################################################################

base_ring(A::AlgAss{T}) where {T} = A.base_ring::parent_type(T)

Generic.dim(A::AlgAss) = size(A.mult_table, 1)

elem_type(::Type{AlgAss{T}}) where {T} = AlgAssElem{T}

parent(::Type{AlgAssElem{T}}) where {T} = AlgAss{T}

morphism_type(::AlgAss{T}) where {T} = AlgAssMor{T, T, Generic.Mat{T}}

morphism_type(::AlgAss{fmpq}) = AlgAssMor{fmpq, fmpq, fmpq_mat}

morphism_type(::AlgAss{fq}) = AlgAssMor{fq, fq, fq_mat}

morphism_type(::AlgAss{fq_nmod}) = AlgAssMor{fq_mod, fq_nmod, fq_nmod_mat}

morphism_type(::AlgAss{nmod}) = AlgAssMor{nmod, nmod, nmod_mat}

################################################################################
#
#  Basis
#
################################################################################

function basis(A::AlgAss{T}) where {T}
  B = Vector{AlgAssElem{T}}(undef, dim(A))
  for i in 1:dim(A)
    B[i] = A[i]
  end
  return B
end

################################################################################
#
#  Commutativity
#
################################################################################

iscommutative_known(A::AlgAss{T}) where {T} = A.iscommutative != 0

function iscommutative(A::AlgAss{T}) where {T}
  if iscommutative_known(A)
    return A.iscommutative == 1
  end
  for i = 1:dim(A)
    for j = i + 1:dim(A)
      if A.mult_table[i, j, :] != A.mult_table[j, i, :]
        A.iscommutative = 2
        return false
      end
    end
  end
  A.iscommutative = 1
  return true
end

################################################################################
#
#  Associativity, Distributivity test
#
################################################################################

function check_associativity(A::AlgAss)
  for i = 1:dim(A)
    for j = 1:dim(A)
      el = A[i] * A[j]
      for k = 1:dim(A)
        if el * A[k] != A[i] * (A[j] * A[k])
          return false
        end
      end
    end
  end
  return true
end

function check_distributivity(A::AlgAss)
  for i = 1:dim(A)
    for j = 1:dim(A)
      el = A[i]*A[j]
      for k = 1:dim(A)
        if A[i] * (A[j] + A[k]) != el + A[i] * A[k]
          return false
        end
      end
    end 
  end
  return true
end

################################################################################
#
#  Construction
#
################################################################################

# This only works if base_ring(A) is a field (probably)
function find_one(A::AlgAss)
  n = dim(A)
  M = zero_matrix(base_ring(A), n^2, n)
  c = zero_matrix(base_ring(A), n^2, 1)
  for k = 1:n
    kn = (k - 1)*n
    c[kn + k, 1] = base_ring(A)(1)
    for i = 1:n
      for j = 1:n
        M[i + kn, j] = deepcopy(A.mult_table[j, k, i])
      end
    end
  end
  Mc = hcat(M, c)
  rref!(Mc)
  @assert !iszero(Mc[n, n])
  n != 1 && @assert iszero(Mc[n + 1, n + 1])
  cc = solve_ut(sub(Mc, 1:n, 1:n), sub(Mc, 1:n, (n + 1):(n + 1)))
  one = [ cc[i, 1] for i = 1:n ]
  return one
end

function AlgAss(R::Ring, mult_table::Array{T, 3}, one::Array{T, 1}) where {T}
  # checks
  return AlgAss{T}(R, mult_table, one)
end

function AlgAss(R::Ring, mult_table::Array{T, 3}) where {T}
  # checks
  A = AlgAss{T}(R)
  A.mult_table = mult_table
  A.one = find_one(A)
  return A
end

function AlgAss(R::Ring, d::Int, arr::Array{T, 1}) where {T}
  mult_table = Array{T, 3}(undef, d, d, d)
  n = d^2
  for i in 1:d
    for j in 1:d
      for k in 1:d
        mult_table[i, j, k] = arr[(i - 1) * n + (j - 1) * d + k]
      end
    end
  end
  return AlgAss(R, mult_table)
end

# Constructs the algebra R[X]/f
function AlgAss(f::PolyElem)
  R = base_ring(parent(f))
  n = degree(f)
  Rx = parent(f)
  x = gen(Rx)
  B = Array{elem_type(Rx), 1}(undef, 2*n - 1)
  B[1] = Rx(1)
  for i = 2:2*n - 1
    B[i] = mod(B[i - 1]*x, f)
  end
  mult_table = Array{elem_type(R), 3}(undef, n, n, n)
  for i = 1:n
    for j = i:n
      for k = 1:n
        mult_table[i, j, k] = coeff(B[i + j - 1], k - 1)
        mult_table[j, i, k] = coeff(B[i + j - 1], k - 1)
      end
    end
  end
  one = map(R, zeros(Int, n))
  one[1] = R(1)
  A = AlgAss(R, mult_table, one)
  A.iscommutative = 1
  return A
end

function AlgAss(O::NfOrd, I::NfOrdIdl, p::Union{Integer, fmpz})
  @assert order(I) == O

  n = degree(O)
  BO = basis(O)

  Fp = ResidueRing(FlintZZ, p, cached=false)
  BOmod = [ mod(O(v), I) for v in BO ]
  B = zero_matrix(Fp, n, n)
  for i = 1:n
    b = elem_in_basis(BOmod[i])
    for j = 1:n
      B[i, j] = Fp(b[j])
    end
  end
  r = _rref!(B)
  r == 0 && error("Cannot construct zero dimensional algebra.")
  b = Vector{fmpz}(undef, n)
  bbasis = Vector{NfOrdElem}(undef, r)
  for i = 1:r
    for j = 1:n
      b[j] = fmpz(B[i, j])
    end
    bbasis[i] = O(b)
  end

  _, p, L, U = _lu(transpose(B))

  mult_table = Array{elem_type(Fp), 3}(undef, r, r, r)

  d = zero_matrix(Fp, n, 1)

  for i = 1:r
    for j = i:r
      c = elem_in_basis(mod(bbasis[i]*bbasis[j], I))
      for k = 1:n
        d[p[k], 1] = c[k]
      end
      d = solve_lt(L, d)
      d = solve_ut(U, d)
      for k = 1:r
        mult_table[i, j, k] = deepcopy(d[k, 1])
        mult_table[j, i, k] = deepcopy(d[k, 1])
      end
    end
  end

  if isone(bbasis[1])
    one = zeros(Fp, r)
    one[1] = Fp(1)
    A = AlgAss(Fp, mult_table, one)
  else
    A = AlgAss(Fp, mult_table)
  end
  A.iscommutative = 1

  function _image(a::NfOrdElem)
    c = elem_in_basis(mod(a, I))
    for k = 1:n
      d[p[k], 1] = c[k]
    end
    d = solve_lt(L, d)
    d = solve_ut(U, d)
    e = A()
    for k = 1:r
      e.coeffs[k] = deepcopy(d[k, 1])
    end
    return e
  end

  function _preimage(a::AlgAssElem)
    return sum(fmpz(a.coeffs[i])*bbasis[i] for i = 1:r)
  end

  OtoA = NfOrdToAlgAssMor{elem_type(Fp)}(O, A, _image, _preimage)

  return A, OtoA
end

function _modular_basis(pb::Vector{Tuple{T, NfOrdFracIdl}}, p::NfOrdIdl) where T <: RelativeElement{nf_elem}
  L = parent(pb[1][1])
  K = base_ring(L)
  basis = Array{elem_type(L), 1}()
  u = L(K(uniformizer(p)))
  for i = 1:degree(L)
    v = valuation(pb[i][2], p)
    push!(basis, (u^v)*pb[i][1])
  end
  return basis
end

#=
Qx, x = QQ["x"];
f = x^2 + 12*x - 92;
K, a = number_field(f, "a");
OK = maximal_order(K);
Ky, y = K["y"];
g = y^2 - 54*y - 73;
L, b = number_field(g, "b");
OL = maximal_order(L);
p = prime_decomposition(OK, 2)[1][1]
=#

# Assume that O is relative order over OK, I is an ideal of O and p is a prime
# ideal of OK with pO \subseteq I. O/I is an OK/p-algebra.
#
# The idea is to compute pseudo-basis of O and I respectively, for which the
# coefficient ideals have zero p-adic valuation. Then we can think in the
# localization at p and do as in the case of principal ideal domains.
function AlgAss(O::NfRelOrd{T, S}, I::NfRelOrdIdl{T, S}, p::Union{NfOrdIdl, NfRelOrdIdl}) where {T, S}
  basis_pmatI = basis_pmat(I, Val{false})
  basis_pmatO = basis_pmat(O, Val{false})

  new_basis_mat = deepcopy(O.basis_mat)
  new_basis_mat_I = deepcopy(I.basis_mat)

  pi = anti_uniformizer(p)

  new_basis_coeffs = S[]

  for i in 1:degree(O)
    a = pi^valuation(basis_pmat(O).coeffs[i], p)
    push!(new_basis_coeffs, a * basis_pmatO.coeffs[i])
    mul_row!(new_basis_mat, i, inv(a))
    for j in 1:degree(O)
      new_basis_mat_I[j, i] = new_basis_mat_I[j, i] * a
    end
  end

  new_coeff_I = S[]

  for i in 1:degree(O)
    a = pi^valuation(basis_pmatI.coeffs[i], p)
    push!(new_coeff_I, a * basis_pmatI.coeffs[i])
    mul_row!(new_basis_mat_I, i, inv(a))
  end

  Fp, mF = ResidueField(order(p), p)
  mmF = extend(mF, base_ring(nf(O)))
  invmmF = inv(mmF)

  basis_elts = Int[]
  reducers = Int[]

  for i in 1:degree(O)
    v = valuation(new_basis_mat_I[i, i], p)
    v2 = valuation(new_coeff_I[i], p)
    #@show (v2, v)
    @assert v >= 0
    if v == 0
    #if valuation(basis_pmatI.coeffs[i], p) + valuation(new_basis_mat_I[i, i], p) == 0
      push!(reducers, i)
    else
      push!(basis_elts, i)
    end
  end

  reverse!(reducers)

  OLL = Order(nf(O), PseudoMatrix(new_basis_mat, new_basis_coeffs))

  newI = ideal(OLL, PseudoMatrix(new_basis_mat_I, new_coeff_I))

  new_basis = pseudo_basis(OLL)

  pseudo_basis_newI = pseudo_basis(newI)

  tmp_matrix = zero_matrix(base_ring(nf(O)), 1, degree(O))

  basis_mat_inv_OLL = basis_mat_inv(OLL)

  function _coeff(c) 
    for i in 0:degree(O) - 1
      tmp_matrix[1, i + 1] = coeff(c, i)
    end
    return tmp_matrix * basis_mat_inv_OLL
  end

  r = length(basis_elts)

  mult_table = Array{elem_type(Fp), 3}(undef, r, r, r)

  for i in 1:r
    for j in 1:r
      c = new_basis[basis_elts[i]][1] * new_basis[basis_elts[j]][1]
      coeffs = _coeff(c)

      for k in reducers
        d = -coeffs[k]//new_basis_mat_I[k, k]
        c = c + d * pseudo_basis_newI[k][1]
      end
      coeffs = _coeff(c)
      for k in 1:degree(O)
        if !(k in basis_elts)
          @assert iszero(coeffs[k])
        end
      end
      for k in 1:r
        mult_table[i, j, k] = mmF(coeffs[basis_elts[k]])
      end
    end
  end

  if isone(new_basis[basis_elts[1]][1])
    one = zeros(Fp, length(basis_elts))
    one[1] = Fp(1)
    A = AlgAss(Fp, mult_table, one)
  else
    A = AlgAss(Fp, mult_table)
  end
  A.iscommutative = 1

  function _image(a::NfRelOrdElem)
    c = a.elem_in_nf
    coeffs = _coeff(c)
    for k in reducers
      d = -coeffs[k]//new_basis_mat_I[k, k]
      c = c + d*pseudo_basis_newI[k][1]
    end
    coeffs = _coeff(c)
    for k in 1:degree(O)
      if !(k in basis_elts)
        @assert iszero(coeffs[k])
      end
    end
    b = A()
    for k in 1:r
      b.coeffs[k] = mmF(coeffs[basis_elts[k]])
    end
    return b
  end

  lifted_basis_of_A = []

  for i in basis_elts
    c = coprime_to(new_basis[i][2], p)
    b = invmmF(inv(mmF(c)))*c*new_basis[i][1]
    @assert b in O
    push!(lifted_basis_of_A, b)
  end

  function _preimage(v::AlgAssElem)
    return O(sum((invmmF(v.coeffs[i])) * lifted_basis_of_A[i] for i in 1:r))
  end

  OtoA = NfRelOrdToAlgAssMor{T, S, elem_type(Fp)}(O, A, _image, _preimage)

  return A, OtoA
end

#Given I with v_p(I) = 0, returns element a \in I such that v_p(a) = 0
function coprime_to(I::NfOrdFracIdl, p::NfOrdIdl)
  pi = anti_uniformizer(p)
  a = basis(I)[1]
  l = valuation(a, p)
  @assert l >= 0
  if l > 0
    a = pi^l * a
  end
  @assert valuation(a, p) == 0
  @assert denominator(I)*a in numerator(I)
  return a
end

function coprime_to(I::NfRelOrdFracIdl, p::NfRelOrdIdl)
  pi = anti_uniformizer(p)
  a = rand(I, 500)
  l = valuation(a, p)
  @assert l >= 0
  if l > 0
    a = pi^l*a
  end
  @assert valuation(a, p) == 0
  return a
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::AlgAss)
  compact = get(io, :compact, false)
  if compact
    print(io, "Associative algebra over ")
    print(io, A.base_ring)
  else
    print(io, "Associative algebra of dimension $(dim(A)) over ")
    print(io, A.base_ring)
  end
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(A::AlgAss{T}, dict::IdDict) where {T}
  B = AlgAss{T}(base_ring(A))
  for x in fieldnames(typeof(A))
    if x != :base_ring && isdefined(A, x)
      setfield!(B, x, Base.deepcopy_internal(getfield(A, x), dict))
    end
  end
  B.base_ring = A.base_ring
  return B
end

################################################################################
#
#  Equality
#
################################################################################

function ==(A::AlgAss{T}, B::AlgAss{T}) where {T}
  base_ring(A) != base_ring(B) && return false
  return A.one == B.one && A.mult_table == B.mult_table
end

################################################################################
#
#  Subalgebras
#
################################################################################

# This only works if base_ring(A) is a field
# Constructs the algebra e*A
function subalgebra(A::AlgAss{T}, e::AlgAssElem{T}, idempotent::Bool = false) where {T}
  @assert parent(e) == A
  R = base_ring(A)
  isgenres = (typeof(R) <: Generic.ResRing)
  n = dim(A)
  B = representation_matrix(e)
  r = _rref!(B)
  r == 0 && error("Cannot construct zero dimensional algebra.")
  basis = Vector{AlgAssElem{T}}(undef, r)
  for i = 1:r
    basis[i] = elem_from_mat_row(A, B, i)
  end

  # The basis matrix of e*A with respect to A is
  basis_mat_of_eA = sub(B, 1:r, 1:n)

  if isgenres
    _, p, L, U = _lu(transpose(B))
  else
    _, p, L, U = lu(transpose(B))
  end
  mult_table = Array{elem_type(R), 3}(undef, r, r, r)
  c = A()
  d = zero_matrix(R, n, 1)
  for i = 1:r
    for j = 1:r
      if iscommutative(A) && j < i
        continue
      end
      c = mul!(c, basis[i], basis[j])
      for k = 1:n
        d[p[k], 1] = c.coeffs[k]
      end
      d = solve_lt(L, d)
      d = solve_ut(U, d)
      for k = 1:r
        mult_table[i, j, k] = deepcopy(d[k, 1])
        if iscommutative(A) && i != j
          mult_table[j, i, k] = deepcopy(d[k, 1])
        end
      end
    end
  end
  if idempotent
    for k = 1:n
      d[p[k], 1] = e.coeffs[k]
    end
    d = solve_lt(L, d)
    d = solve_ut(U, d)
    v = Vector{elem_type(R)}(undef, r)
    for i in 1:r
      v[i] = d[i, 1]
    end
    eA = AlgAss(R, mult_table, v)
  else
    eA = AlgAss(R, mult_table)
  end

  # TODO: The following is wrong. The algebra eA may be commutative
  # even if A is not commutative.
  eA.iscommutative = A.iscommutative

  if idempotent
    # We have the map eA -> A, given by the multiplying with basis_mat_of_eA.
    # But there is also the canonical projection A -> eA, a -> ea.
    # We compute the corresponding matrix.
    B = representation_matrix(e)
    C = zero_matrix(R, n, r)
    for i in 1:n
      for k = 1:n
        d[p[k], 1] = B[i, k]
      end
      d = solve_lt(L, d)
      d = solve_ut(U, d)
      for k in 1:r
        C[i, k] = d[k, 1]
      end
    end
    eAtoA = AlgAssMor(eA, A, basis_mat_of_eA, C)
  else
    eAtoA = AlgAssMor(eA, A, basis_mat_of_eA)
  end
  return eA, eAtoA
end

function subalgebra(A::AlgAss{T}, basis::Array{AlgAssElem{T},1}) where {T}
  B=zero_matrix(base_ring(A), dim(A), length(basis))
  for i=1:dim(A)
    for j=1:length(basis)
      B[i,j]=basis[j].coeffs[i]
    end
  end
  M=Array{elem_type(base_ring(A)),3}(undef, length(basis), length(basis), length(basis))
  for i=1:length(basis)
    for j=1:length(basis)
      x=basis[i]*basis[j]
      N1=matrix(base_ring(A), dim(A), 1, x.coeffs)
      N=_solve_unique(N1,B)
      for k=1:length(basis)
        M[i,j,k]=N[k,1]
      end
    end
  end
  A1=AlgAss(base_ring(A), M)
  return A1, AlgAssMor(A1, A, B')
end

################################################################################
#
#  Splitting
#
################################################################################

issimple_known(A) = A.issimple != 0

function kernel_of_frobenius(A::AlgAss)
  F = base_ring(A)
  q = order(F)

  b = A()
  c = A()
  B = zero_matrix(F, dim(A), dim(A))
  for i = 1:dim(A)
    b.coeffs[i] = F(1)
    if i > 1
      b.coeffs[i - 1] = F()
    end
    c = b^q - b
    for j = 1:dim(A)
      B[j, i] = deepcopy(c.coeffs[j])
    end
  end

  V = right_kernel(B)
  return [ A(v) for v in V ]
end

function _issimple(A::AlgAss)
  if issimple_known(A)
    return A.issimple == 1
  else
    b = issimple(A, Val{false})
    if b
      A.issimple = 1
    else
      A.issimple = 0
    end
    return b
  end
end

@doc Markdown.doc"""
***
    decompose(A::AlgAss)
            
> Given a semisimple algebra over a field, this function 
> returns a decomposition of A as a direct sum of simple algebras.
"""
function decompose(A::AlgAss{T}) where {T}
  if isdefined(A, :decomposition)
    return A.decomposition::Vector{Tuple{AlgAss{T}, morphism_type(A)}}
  end

  if issimple_known(A) && A.issimple == 1
    res = [( A, AlgAssMor(A, A, identity_matrix(base_ring(A), dim(A)), identity_matrix(base_ring(A), dim(A))))] # and the morphism
  end

  if iscommutative(A)
    res = _dec_com(A)
  else
    res = _dec_via_center(A)
  end

  A.decomposition = res
  return res
end

function _dec_via_center(A::AlgAss{T}) where {T}
  ZA, mZA = center(A)
  Algs = _dec_com(ZA)
  res = [ subalgebra(A, mZA(BtoZA(one(B))), true) for (B, BtoZA) in Algs]
  for i in 1:length(res)
    res[i][1].issimple = 1
  end
  A.decomposition = res
  return res
end

function _dec_com(A::AlgAss)
  if characteristic(base_ring(A)) > 0
    return _dec_com_finite(A)
  else
    return _dec_com_gen(A)
  end
end

function _dec_com_gen(A::AlgAss{T}) where {T <: FieldElem}
  if dim(A) == 1
    A.issimple = 1
    return [ (A, AlgAssMor(A, A, identity_matrix(base_ring(A), dim(A)), identity_matrix(base_ring(A), dim(A)))) ]
  end

  F = base_ring(A)

  k = dim(A)

  V = elem_type(A)[A[i] for i in 1:k]

  while true
    c = elem_type(F)[ rand(F, -10:10) for i = 1:k ]
    a = dot(c, V)
    f = minpoly(a)

    if degree(f) < 2
      continue
    end

    if degree(f) == dim(A) && isirreducible(f)
      A.issimple = 1
      return [(A, AlgAssMor(A, A, identity_matrix(base_ring(A), dim(A)), identity_matrix(base_ring(A), dim(A))))]
    end

    @assert issquarefree(f)

    fac = factor(f)
    R = parent(f)
    factors = Vector{elem_type(R)}()
    for ff in keys(fac.fac)
      push!(factors, ff)
    end
    sols = Vector{elem_type(R)}()
    right_side = [ R() for i = 1:length(factors) ]
    max_deg = 0
    for i = 1:length(factors)
      right_side[i] = R(1)
      if i != 1
        right_side[i - 1] = R(0)
      end
      s = crt(right_side, factors)
      push!(sols, s)
      max_deg = max(max_deg, degree(s))
    end
    x = one(A)
    powers = Vector{elem_type(A)}()
    for i = 1:max_deg + 1
      push!(powers, x)
      x *= a
    end
    idems = Vector{elem_type(A)}()
    for s in sols
      idem = A()
      for i = 0:degree(s)
        idem += coeff(s, i)*powers[i + 1]
      end
      push!(idems, idem)
    end

    A.issimple = 2

    res = Vector{Tuple{typeof(A), morphism_type(A)}}()
    for idem in idems
      S, StoA = subalgebra(A, idem, true)
      decS = _dec_com_gen(S)
      for (B, BtoS) in decS
        BtoA = compose_and_squash(StoA, BtoS)
        push!(res, (B, BtoA))
      end
    end
    return res
  end
end


function _dec_com_finite(A::AlgAss{T}) where T
  if dim(A) == 1
    A.issimple = 1
    return [ (A, AlgAssMor(A, A, identity_matrix(base_ring(A), dim(A)), identity_matrix(base_ring(A), dim(A)))) ]
  end

  F = base_ring(A)
  @assert !iszero(characteristic(F))
  V = kernel_of_frobenius(A)
  k = length(V)

  if k == 1
    A.issimple = 1
    return [ (A, AlgAssMor(A, A, identity_matrix(base_ring(A), dim(A)), identity_matrix(base_ring(A), dim(A)))) ]
  end
  
  A.issimple = 2

  while true
    c = elem_type(F)[ rand(F) for i = 1:k ]
    a = dot(c, V)
    f = minpoly(a)

    if degree(f) < 2
      continue
    end

    @assert issquarefree(f)

    fac = factor(f)
    R = parent(f)
    factorss = collect(keys(fac.fac))
    sols = Vector{typeof(f)}(undef, length(factorss))
    right_side = typeof(f)[ zero(R) for i = 1:length(factorss) ]
    max_deg = 0
    for i = 1:length(factorss)
      right_side[i] = one(R)
      if 1 != i
        right_side[i - 1] = zero(R)
      end
      s = crt(right_side, factorss)
      sols[i] = s
      max_deg = max(max_deg, degree(s))
    end
    x = one(A)
    powers = Vector{elem_type(A)}()
    for i = 1:max_deg + 1
      push!(powers, x)
      x *= a
    end
    idems = Vector{elem_type(A)}()
    for s in sols
      idem = A()
      for i = 0:degree(s)
        idem += coeff(s, i)*powers[i + 1]
      end
      push!(idems, idem)
    end

    res = Vector{Tuple{AlgAss{T}, morphism_type(A)}}()
    for idem in idems
      S, StoA = subalgebra(A, idem, true)
      decS = _dec_com_finite(S)
      for (B, BtoS) in decS
        BtoA = compose_and_squash(StoA, BtoS)
        push!(res, (B, BtoA))
      end
    end
    return res
  end
end

#@doc Markdown.doc"""
#***
#    decomposition(A::AlgAss)
#            
#> Given a semisimple algebra over a field, this function 
#> returns a decomposition of A as a direct sum of simple algebras.
#"""
#function decomposition(A::AlgAss)
#  R = base_ring(A)
#  if characteristic(R) > 0
#    return _dec_char_p
#  else
#    return _dec_via_center
#  end
#end
#
#function _decomposition_char_p(A::AlgAss)
#  b, algebras = issimple(A)
#  if b
#    return algebras
#  end
#  result = typeof(algebras)()
#  while length(algebras) != 0
#    B, BtoA = pop!(algebras)
#    b, algebras2 = issimple(B)
#    if b
#      push!(result, (B, BtoA))
#    else
#      for (C, CtoB) in algebras2
#        CtoA = compose_and_squash(BtoA, CtoB)
#        push!(algebras, (C, CtoA))
#      end
#    end
#  end
#  return result
#end

###############################################################################
#
#  Trace Matrix
#
###############################################################################

function _assure_trace_basis(A::AlgAss{T}) where T
  if !isdefined(A, :trace_basis_elem)
    A.trace_basis_elem = Array{T, 1}(undef, dim(A))
    for i=1:length(A.trace_basis_elem)
      A.trace_basis_elem[i]=sum(A.mult_table[i,j,j] for j= 1:dim(A))
    end
  end
  return nothing
end

function trace_matrix(A::AlgAss)
  _assure_trace_basis(A)
  F = base_ring(A)
  n = dim(A)
  M = zero_matrix(F, n, n)
  for i = 1:n
    M[i,i] = tr(A[i]^2)  
  end
  for i = 1:n
    for j = i+1:n
      x = tr(A[i]*A[j])
      M[i,j] = x
      M[j,i] = x
    end
  end
  return M
end

################################################################################
#
#  Radical
#
################################################################################

@doc Markdown.doc"""
***
    radical(A::AlgAss{fq_nmod})
            
> Given an algebra over a finite field of prime order, this function 
> returns a set of elements generating the radical of A
"""

function radical(A::AlgAss{fq_nmod})

  F=A.base_ring
  p=F.p
  l=clog(fmpz(dim(A)),p)
  #First step: kernel of the trace matrix
  I=trace_matrix(A)
  k,B=nullspace(I)
  # The columns of B give the coordinates of the elements in the order.
  if k==0
    return AlgAssElem[]
  end
  C=transpose(B)
  if l==1 && dim(A)!=p
    #In this case, we can output I: it is the standard p-trace method.
    return AlgAssElem[elem_from_mat_row(A,C,i) for i=1:rows(C)]
  end
  #Now, iterate: we need to find the kernel of tr((xy)^(p^i))/p^i mod p
  #on the subspace generated by C
  #Hard to believe, but this is linear!!!!
  for i=1:l
    M=zero_matrix(F, dim(A), rows(C))
    for t=1:rows(I)
      elm=elem_from_mat_row(A,C,t)
      for s=1:dim(A)
        a=elm*A[s]
        M1=representation_matrix(a^(p^i))
        el=sum(FlintZZ(coeff(M1[k,k],0)) for k=1:dim(A))
        M[s,t]=F(divexact(el,p^i))
      end
    end
    k,B=nullspace(M)
    if k==0
      return AlgAssOrdIdl(O,MatrixSpace(FlintZZ, dim(A), dim(A), false)(p))
    end
    C=transpose(B)*C
  end
  return AlgAssElem[elem_from_mat_row(A,C,i) for i=1:rows(C)]
   
end


###############################################################################
#
#  Center
#
###############################################################################

function _rep_for_center(M::T, A::AlgAss) where T<: MatElem
  
  n=dim(A)
  for i=1:n
    for j = 1:n
      for k = 1:n
        M[k+(i-1)*n, j] = A.mult_table[i, j, k]-A.mult_table[j, i, k]
      end
    end
  end
  return nothing
end

function center(A::AlgAss{T}) where {T}
  if iscommutative_known(A) && A.iscommutative==1
    return A, AlgAssMor(A, A, identity_matrix(base_ring(A), dim(A))) 
  end
  if isdefined(A, :center)
    return A.center
  end
  n=dim(A)
  M=zero_matrix(base_ring(A), n^2, n)
  # I concatenate the difference between the right and left representation matrices.
  _rep_for_center(M,A)
  k,B=nullspace(M)
  res=Array{AlgAssElem{T},1}(undef, k)
  for i=1:k
    res[i]= A(T[B[j,i] for j=1:n])
  end
  A.center = subalgebra(A, res)
  return A.center
end

function dimension_of_center(A::AlgAss)
  C, _ = center(A)
  return dim(C)
end

################################################################################
#
#  Decomposition
#
################################################################################

################################################################################
#
#  Random elements
#
################################################################################

function rand(A::AlgAss{T}) where T
  c = [ rand(base_ring(A)) for i = 1:dim(A) ]
  return AlgAssElem{T}(A, c)
end

function rand(A::AlgAss{fmpq}, rng::UnitRange{Int} = -10:10) 
  c = [ rand(base_ring(A), rng) for i = 1:dim(A) ]
  return AlgAssElem{fmpq}(A, c)
end
################################################################################
#
#  Primitive elements
#
################################################################################

function primitive_element(A::AlgAss)
  a, _ = _primitive_element(A::AlgAss)
  return a
end

function _primitive_element(A::AlgAss)
  error("Not implemented yet")
  return nothing
end

function _primitive_element(A::AlgAss{T}) where T <: Union{nmod, fq, fq_nmod, Generic.Res{fmpz}, fmpq}
  d = dim(A)
  a = rand(A)
  f = minpoly(a)
  while degree(f) < d
    a = rand(A)
    f = minpoly(a)
  end
  return a, f
end

function _as_field(A::AlgAss{T}) where T
  d = dim(A)
  a, mina = _primitive_element(A)
  b = one(A)
  M = zero_matrix(base_ring(A), d, d)
  elem_to_mat_row!(M, 1, b)
  for i in 1:(d - 1)
    b = mul!(b, b, a)
    elem_to_mat_row!(M, i + 1, b)
  end
  if T == Generic.Res{fmpz}
    A, c = inv(M)
    B = divexact(A, c)
  elseif T == nmod
    B = inv(M)
  end
  N = zero_matrix(base_ring(A), 1, d)
  local f
  let N = N, B = B
    f = function(x)
      for i in 1:d
        N[1, i] = x.coeffs[i]
      end
      return N * B
    end
  end
  return a, mina, f
end

################################################################################
#
#  Compute generators
#
################################################################################

function _reduce(M, v)
  cur_ind = 0
  for outer cur_ind in 1:cols(M)
    if !iszero(v[cur_ind])
      break
    end
  end
end

function gens(A::AlgAss)
  d = dim(A)
  K = base_ring(A)

  b = rand(A)
  while iszero(b)
    b = rand(A)
  end

  cur_gen = elem_type(A)[b]

  current_dim = -1

  B = zero_matrix(K, d, d)

  for k in 1:d
    B[1, k] = b.coeffs[k]
  end

  cur_dim = 1

  new_dim = 0

  if d == 1
    return cur_gen
  end

  l = 0

  t_gens = copy(cur_gen)

  while true
    l = l + 1
    while true
      t_gens = copy(cur_gen)
      t = length(t_gens)
      for i in 1:t
        for j in 1:t
          c = t_gens[i] * t_gens[j]
          for k in 1:d
            B[d, k] = c.coeffs[k]
          end
          new_dim = rref!(B)
          if new_dim == d
            return cur_gen
          elseif new_dim > cur_dim
            cur_dim = new_dim
            push!(t_gens, c)
          end
        end
      end

      if cur_dim == new_dim
        break
      else
        cur_dim = new_dim
        B = new_B
      end
    end

    if cur_dim == d
      break
    else
      b = rand(A)
      while iszero(b)
        b = rand(A)
      end
      push!(cur_gen, b)
    end
    #@show length(cur_gen)
  end

  return cur_gen
end