export qAdicConj


#########################################################################################
#
#   qAdic Conj structure
#
#########################################################################################

# Honestly the thing that is needed here is a pure Julia implementation of the HenselCtx.
# Field definitions should use a "Krasner criteria" to detect if the extensions are distinct.

################################################################################
# Root contexts for lifting algorithms
################################################################################

mutable struct qAdicRootCtx
  f::fmpz_poly
  p::Int
  n::Int
  Q::Array{FlintQadicField, 1}
  H::Hecke.HenselCtx
  R::Array{qadic, 1} # These are the cached roots.
  function qAdicRootCtx(f::fmpz_poly, p::Int)
    r = new()
    r.f = f
    r.p = p
    r.H = H = Hecke.factor_mod_pk_init(f, p)
    lf = Hecke.factor_mod_pk(H, 1)
    #TODO:XXX: Careful: QadicField ONLY works, currently, in Conway range
    Q = [QadicField(p, x, 1) for x = Set(degree(y) for y = keys(lf))]
    @assert all(isone, values(lf))
    r.Q = Q

    #NOTE: Roots are not computed when initialized, as no precision has been determined.
    return r
  end
end



@doc Markdown.doc"""
    qAdicConj(K::AnticNumberField, p::Int)

Creates a data structure to compute the conjugates in a unramified splitting field
over $Q_p$.
"""
# This structure doesn't compute anything really.

# It mostly just explicitly associates a number field to a Qadic field.

# The work in the initialization is hidden in the HenselCtx step.
# It would make more sense to have some computation precomputed.

# This object doesn't know very much right now.
mutable struct qAdicConj
  K::AnticNumberField
  C::qAdicRootCtx
  cache::Dict{nf_elem, Any}

  function qAdicConj(K::AnticNumberField, p::Int)
    isindex_divisor(maximal_order(K), p) && error("cannot deal with index divisors yet")
    isramified(maximal_order(K), p) && error("cannot deal with ramification yet")

    # Check for cached data. If none, update the reference in K to set
    # `D` as the local conjugate data.
    D = _get_nf_conjugate_data_qAdic(K, false)
    if D !== nothing
      if haskey(D, p)
        Dp = D[p]
        return new(K, Dp[1], Dp[2])
      end
    else
      D = Dict{Int, Tuple{qAdicRootCtx, Dict{nf_elem, Any}}}()
      _set_nf_conjugate_data_qAdic(K, D)
    end

    # Initialize the new structure.  
    Zx = PolynomialRing(FlintZZ, cached = false)[1]
    C = qAdicRootCtx(Zx(K.pol), p)
    r = new()
    r.C = C
    r.K = K

    # cache for conjugates of a given number field element??
    r.cache = Dict{nf_elem, Any}()
    D[p] = (C, r.cache)
    return r
  end
end

# Display for conjugates data.
function Base.show(io::IO, C::qAdicConj)
  println(io, "data for the $(C.C.p)-adic completions of $(C.K)")
end



#########################################################################################
#
#   Newton lifting and root finding
#
#########################################################################################


@doc Markdown.doc"""
    roots(f::fmpz_poly, Q::FlintQadicField; max_roots::Int = degree(f)) -> Array{qadic, 1}
The roots of $f$ in $Q$, $f$ has to be square-free (at least the roots have to be simple roots).    
"""

# NOTE: Both a Hensel factorization and a newton iteration are required to refine the roots,
#       since the Hensel context only works for polynomials over ZZ.
function roots(f::fmpz_poly, Q::FlintQadicField; max_roots::Int = degree(f))
    k, mk = ResidueField(Q)
    rt = roots(f, k)
    RT = qadic[]
    for r = rt
        new_rt, cond = newton_lift(f, preimage(mk, r))
        push!(RT, new_rt)
        if length(RT) >= max_roots
            return RT
        end
    end
    return RT
end

is_splitting(C::qAdicRootCtx) = C.is_splitting

function roots(C::qAdicRootCtx, n::Int = 10)
  if isdefined(C, :R) && all(x -> x.N >= n, C.R)
    return [setprecision(x, n) for x = C.R]
  end
  lf = factor_mod_pk(Array, C.H, n)
  rt = qadic[]
  for Q = C.Q
    Q.prec_max = n
    for x = lf
      if is_splitting(C) || degree(x[1]) == degree(Q)
        append!(rt, roots(x[1], Q, max_roots = 1))
      end
    end
  end
  if isdefined(C, :R)
    st = qadic[]
    for r = C.R
      p = findfirst(x -> degree(parent(r)) == degree(parent(x)) && iszero(x-r), rt)
      push!(st, rt[p])
    end
    rt = st
  end
  C.R = rt
  return rt
end

#########################################################################################
#
#   Completion from prime ideal
#
#########################################################################################

function gens(P::NfOrdIdl)
    @assert has_2_elem(P)
    (P.gen_one, P.gen_two)
end

@doc Markdown.doc"""
    qAdicConj(K::AnticNumberField, p::Int)

Creates a data structure to compute the conjugates in a unramified splitting field
over $Q_p$.
"""
mutable struct qAdicConj
  K::AnticNumberField
  C::qAdicRootCtx
  cache::Dict{nf_elem, Any}

  function qAdicConj(K::AnticNumberField, p::Int; splitting_field::Bool = false)
    isindex_divisor(maximal_order(K), p) && error("cannot deal with index divisors yet")
    isramified(maximal_order(K), p) && error("cannot deal with ramification yet")
    if splitting_field
      Zx = PolynomialRing(FlintZZ, cached = false)[1]
      C = qAdicRootCtx(Zx(K.pol), p, splitting_field = true)
      r = new()
      r.C = C
      r.K = K
      r.cache = Dict{nf_elem, Any}()
      return r
    end
    D = _get_nf_conjugate_data_qAdic(K, false)
    if D !== nothing
      if haskey(D, p)
        Dp = D[p]
        return new(K, Dp[1], Dp[2])
      end
    else
        return [coeff_field(coeff(a,j)) for j=0:degree(k)-1]
    end
end

function coeffs(a::qadic)
    k = parent(a)
    return [coeff(a,j) for j=0:degree(k)-1]
end

function mod_sym(a,b)
    c = mod(a,b)
    return c < b/2 ? c : c-b
end

function sym_lift(a::padic)
    u = unit_part(a)
    p = prime(a.parent)
    N = precision(a)
    v = valuation(a)
    return mod_sym(u, p^(N-v))*FlintQQ(p)^v
end

@doc Markdown.doc"""
    underdetermined_solve(A,b)
Solves the equation `Ax=b`. Return the first index of the column where the last entry is non-zero.
"""
function underdetermined_solve(A,b)

    M = hcat(A,-b)
    nu,N = nullspace(M)

    display(N)

    ind = 0
    for j=1:size(N,2)
        if isone(N[size(N,1),j])
            ind=j
            break
        end
    end
    @assert !iszero(ind)

    return nu,N,ind
end

@doc Markdown.doc"""
    underdetermined_solve_first(A,b)
Return the first basis column of the solutions to Ax=b, if it exists.
"""
function underdetermined_solve_first(A,b)
    nu,N,ind = underdetermined_solve(A,b)
    return N[1:size(N,1)-1,ind]
end


## Temporary structure to record data cached so that a completion can be sharpened.
## This should somehow be remembered by the maps to/from the completion instead.

mutable struct CompletionMapData
    dixon_bn
    dixon_mat_inv_modpn
    residue_field_map
end

#########################################################################################
#
#   Embedding classes (up to equivalence) interface
#
#########################################################################################

# Return the embeddings, up to local Galois automorphisms, of a number field element `a`.
# Treatment is different in ramified versus unramified cases due to the extra structure.
# i.e, a factorization method is present in the unramified case.

function embedding_classes(a, p)    
    K = parent(a)

    if any(isramified(maximal_order(K), p))
        return embedding_classes_ramified(a,p)
    else
        return embedding_classes_unramified(a,p)
    end
end

function embedding_classes_ramified(a,p)
    K = parent(a)
    lp = prime_decomposition(maximal_order(K), p)
    prime_ideals = [P[1] for P in lp]

    completions = [Hecke.completion(K,P) for P in prime_ideals]
    embeddings_up_to_equiv = [mp(a) for (field,mp) in completions]
    return embeddings_up_to_equiv
end

# function _conjugates(a::nf_elem, C::qAdicConj, n::Int, op::Function)
function embedding_classes_unramified(a, C, precision=10)
    K = parent(a)
    #C = qAdicConj(K, Int(p))
    #TODO: implement a proper Frobenius - with caching of the frobenius_a element

    R = roots(C.C, precision)   # This seems to be the line where the roots are actually computed.
    @assert parent(a) == C.K
    Zx = PolynomialRing(FlintZZ, cached = false)[1]
    d = denominator(a)

    # The element `a` is replaced by a polynomial. It is assumed that the variable
    # in the polynomial is identified with the generator of the number field.
    f = Zx(d*a)
    res = qadic[]
    for alpha in R
        b = inv(parent(alpha)(d))*f(alpha)
        push!(res, b)
    end
    return res
end

#########################################################################################
#
#   Conjugates interface
#
#########################################################################################


#to compare to the classical conjugates
#  all = true/ false: only on of a pair of complex conjugates is returned
#  flat = true/ false: return (Re, Im) or the complex number
#TODO: not sure how this would work in the ramified, not-normal case.
@doc Markdown.doc"""
    conjugates(a::nf_elem, C::qAdicConj, n::Int = 10; flat::Bool = false, all:Bool = true) -> []

Returns an array of the q-adic conjugates of $a$: Let $p Z_K = \prod P_i$ for the maximal order
$Z_K$ of the parent of $a$. Then $K \otimes Q_p = \prod K_{P_i}$. For each of the $P_i$
a $q$-adic (unramifed) extension $K_{P_i}$ of $Q_p$ is computed, sth. $a$ has $\deg P_i = \deg K_{P_i}$
many cojugates in $K_{P_i}$.
If `all = true` and `flat = false`, the default, then all $n$ conjugates are returned.
If `all = false`, then for each $P_i$ only one conjugate is returned, the others could be 
xomputed using automorphisms (the Frobenius).
If `flat = true`, then instead of the conjugates, only the $p$-adic coefficients are returned.
"""
function conjugates(a::nf_elem, C::qAdicConj, n::Int = 10; flat::Bool = false, all::Bool = true)
  if is_splitting(C.C)
    return expand(_conjugates(a, C, n, x -> x), flat = flat, all = all, degs = degrees(C.C.H))
  else
    return expand(_conjugates(a, C, n, x -> x), flat = flat, all = all)
  end
end

function expand(a::Array{qadic, 1}; all::Bool, flat::Bool, degs::Array{Int, 1}= Int[])
  re = qadic[]
  if all
    for ix = 1:length(a)
      x = a[ix]
      push!(re, x)
      y = x
      d = degree(parent(x))
      if ix <= length(degs)
        for i=2:degs[ix]
          y = frobenius(y)
          push!(re, y)
        end
      else
        for i=2:degree(parent(x))
          y = frobenius(y)
          push!(re, y)
        end
      end
    end
  else
    re = a
  end
  if flat
    r = padic[]
    for x = re
      for i=1:degree(parent(x))
        push!(r, coeff(x, i-1))
      end
    end
    return r
  else
    return re
  end
end


#########################################################################################
#
#   Completions
#
#########################################################################################

function _log(a::qadic)
  q = prime(parent(a))^degree(parent(a))
  if iseven(q) # an error in flint
    return log((a^(q-1))^2)//2//(q-1)
  end
  return log(a^(q-1))//(q-1) # faster than the teichmuller stuff
  return log(a*inv(teichmuller(a)))
end

@doc Markdown.doc"""
    conjugates_log(a::nf_elem, C::qAdicConj, n::Int = 10; flat::Bool = false, all:Bool = true) -> []
    conjugates_log(a::FacElem{nf_elem, AnticNumberField}, C::qAdicConj, n::Int = 10; flat::Bool = false, all:Bool = true) -> []

Returns an array of the logarithms of the q-adic conjugates of $a$: Let $p Z_K = \prod P_i$ for the maximal order
$Z_K$ of the parent of $a$. Then $K \otimes Q_p = \prod K_{P_i}$. For each of the $P_i$
a $q$-adic (unramifed) extension $K_{P_i}$ of $Q_p$ is computed, sth. $a$ has $\deg P_i = \deg K_{P_i}$
many cojugates in $K_{P_i}$.
If `all = true` and `flat = false` then all $n$ logarithms of conjugates are returned.
If `all = false`, then for each $P_i$ only one logarithm of a conjugate if returned, the others could be 
xomputed using automorphisms (the Frobenius).
If `flat = true`, then instead of the conjugates, only the $p$-adic coefficients are returned.
"""
function conjugates_log(a::nf_elem, C::qAdicConj, n::Int = 10; all::Bool = false, flat::Bool = true)
  if haskey(C.cache, a)
    b = C.cache[a]
    if b[1,1].N == n
      return expand(b, all = all, flat = flat)
    end
  end
  C.cache[a] = b = _conjugates(a, C, n, _log)
  return expand(b, all = all, flat = flat)
end

function conjugates_log(a::FacElem{nf_elem, AnticNumberField}, C::qAdicConj, n::Int = 10; all::Bool = false, flat::Bool = true)
  first = true
  local res::Array{qadic, 1}
  for (k, v) = a.fac
    try 
      y = conjugates_log(k, C, n, flat = false, all = false)
      if first
        res = v .* y
        first = false
      else
        res += v .* y
      end
    catch e
      if isa(e, DivideError) || isa(e, DomainError)
        lp = prime_decomposition(maximal_order(parent(k)), C.C.p)
        @assert Base.all(x -> has_2_elem_normal(x[1]), lp)
        val = map(x -> valuation(k, x[1]), lp)
        pe = prod(lp[i][1].gen_two^val[i] for i = 1:length(lp) if val[i] != 0)
        aa = k//pe
        y = conjugates_log(aa, C, n, all = false, flat = false)
        if first
          res = v .* y
          first = false
        else
          res += v .* y
        end
      else
        rethrow(e)
      end
    end
  end

  if is_splitting(C.C)
    return expand(res, flat = flat, all = all, degs = degrees(C.C.H))
  else
    return expand(res, all = all, flat = flat)
  end
end


function special_gram(m::Array{Array{qadic, 1}, 1})
  g = Array{padic, 1}[]
  for i = m
    r = padic[]
    for j = m
      k = 1
      S = 0
      while k <= length(i)
        s = i[k] * j[k]
        for l = 1:degree(parent(s))-1
          s += i[k+l] * j[k+l]
        end
        S += coeff(s, 0)
        @assert s == coeff(s, 0)
        k += degree(parent(s))
      end
      push!(r, S)
    end
    push!(g, r)
  end
  return g
end

function special_gram(m::Array{Array{padic, 1}, 1})
  n = matrix(m)
  n = n'*n
  return [[n[i,j] for j=1:ncols(n)] for i = 1:nrows(n)]
end

@doc Markdown.doc"""
    regulator(u::Array{T, 1}, C::qAdicConj, n::Int = 10; flat::Bool = true) where {T<: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}}
    regulator(K::AnticNumberField, C::qAdicConj, n::Int = 10; flat::Bool = true)
    regulator(R::NfAbsOrd, C::qAdicConj, n::Int = 10; flat::Bool = true)

Returns the determinant of $m^t m$ where the columns of $m$ are the `conjugates_log` of the units
in either the array, or the fundamental units for $K$ (the maximal order of $K$) or $R$.
If `flat = false`, then all prime ideals over $p$ need to have the same degree.
In either case, Leopold's conjectue states that the regulator is zero iff the units are dependent.
"""
function regulator(u::Array{T, 1}, C::qAdicConj, n::Int = 10; flat::Bool = true) where {T<: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}}
  c = map(x -> conjugates_log(x, C, n, all = !flat, flat = flat), u)
  return det(matrix(special_gram(c)))
end

function regulator(K::AnticNumberField, C::qAdicConj, n::Int = 10; flat::Bool = false)
  return regulator(maximal_order(K), C, n, flat = flat)
end

function regulator(R::NfAbsOrd{AnticNumberField, nf_elem}, C::qAdicConj, n::Int = 10; flat::Bool = false)
  u, mu = unit_group_fac_elem(R)
  return regulator([mu(u[i]) for i=2:ngens(u)], C, n, flat = flat)
end

@doc Markdown.doc"""
    regulator_iwasawa(u::Array{T, 1}, C::qAdicConj, n::Int = 10) where {T<: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}} -> qadic
    regulator_iwasawa(K::AnticNumberField, C::qAdicConj, n::Int = 10) -> qadic
    regulator_iwasawa(R::NfAbsOrd, C::qAdicConj, n::Int = 10) -> qadic

For a totally real field $K$, the regulator as defined by Iwasawa: the determinant of the
matrix containing the logarithms of the conjugates, supplemented by a column containing all $1$.
"""
function regulator_iwasawa(u::Array{T, 1}, C::qAdicConj, n::Int = 10) where {T<: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}}
  k = base_ring(u[1])
  @assert istotally_real(k)
  c = map(x -> conjugates_log(x, C, n, all = true, flat = false), u)
  m = matrix(c)
  m = hcat(m, matrix(base_ring(m), nrows(m), 1, [one(base_ring(m)) for i=1:nrows(m)]))
  return det(m)//degree(k)
end

function regulator_iwasawa(K::AnticNumberField, C::qAdicConj, n::Int = 10)
  @assert istotally_real(K)
  return regulator_iwasawa(maximal_order(K), C, n)
end

function regulator_iwasawa(R::NfAbsOrd, C::qAdicConj, n::Int = 10)
  @assert istotally_real(nf(R))
  u, mu = unit_group_fac_elem(R)
  return regulator_iwasawa([mu(u[i]) for i=2:ngens(u)], C, n)
end

function matrix(a::Array{Array{T, 1}, 1}) where {T}
  return matrix(hcat(a...))
end


function eval_f_fs(f::PolyElem, x::RingElem)
  d = Int[]
  for i=1:degree(f)
    if !iszero(coeff(f, i))
      if i>0 && !((i-1) in d)
        push!(d, i-1)
      end
      push!(d, i)
    end
  end
  p = Dict{Int, typeof(x)}()
  p[0] = one(x)
  p[1] = x
  p[d[1]] = x^d[1]
    
  for i = 2:length(d)
    if haskey(p, d[i]) 
      continue
    end
    q, r = divrem(d[i], d[i-1])
    if haskey(p, r)
      xr = p[r]
    else
      xr = p[r] = x^r
    end
    p[d[i]] = p[d[i-1]]^q * xr
  end
  s1 = zero(x)
  s2 = zero(x)
  for i=0:degree(f)
    c = coeff(f, i)
    if !iszero(c)
      s1 += c*p[i]
      if i>0
        s2 += i*c*p[i-1]
      end
    end
  end
  return s1, s2
end

struct nf_elem_mod <: RingElem
  a::nf_elem
  p::fmpz
end
function *(a::fmpz, b::nf_elem_mod)
  c = a*b.a
  return nf_elem_mod(mod_sym(c, b.p), b.p)
end
function *(a::nf_elem_mod, b::nf_elem_mod)
  c = a.a*b.a
  return nf_elem_mod(mod_sym(c, a.p), a.p)
end
function one(a::nf_elem_mod)
  return nf_elem_mod(one(a.a), a.p)
end
function zero(a::nf_elem_mod)
  return nf_elem_mod(zero(a.a), a.p)
end
function +(a::nf_elem_mod, b::nf_elem_mod)
  return nf_elem_mod(a.a+b.a, a.p)
end
function ^(a::nf_elem_mod, i::Int)
  b = one(a)
  c = a
  while i > 0
    if isodd(i)
      b *= c
    end
    i >>= 1
    if !iszero(i)
      c *= c
    end
  end
  return b
end

function lift_root(f::fmpz_poly, a::nf_elem, o::nf_elem, p::fmpz, n::Int)
  #f(a) = 0 mod p, o*f'(a) = 1 mod p, want f(a) = 0 mod p^n
  k = 1
  while k < n
    p *= p
    k *= 2
    #TODO: here f wil be sparse (and possibly large degree), so
    #      this evaluation is bad.
    # in the calling cite: don't work in the large field, restrict
    # to working (mod p^k) in the field defined by the factor

    if false
      pa = [one(a)]
      while length(pa) <= degree(f)
        push!(pa, pa[end]*a)
        mod_sym!(pa[end], p)
      end
      fa  = sum(coeff(f, i-1) * pa[i] for i=1:length(pa))
      fsa = sum(coeff(f, i) * i * pa[i] for i=1:length(pa)-1)  
    else
      _fa, _fsa = eval_f_fs(f, nf_elem_mod(a, p))
      fa = _fa.a
      fsa = _fsa.a
    end
    o = o*(2-fsa*o)
    a = a - fa*o
    mod_sym!(o, p)
    mod_sym!(a, p)
  end
  return a
end


@doc Markdown.doc"""
    completion(K::AnticNumberField, P::NfOrdIdl) -> FlintQadicField, Map{AnticNumberField -> FlintQadicField}
The completion of $K$ wrt to the topology induced by the valuation at $P$. $P$ needs
to be unramifed.
The map giving the embedding of $K$ into the completion, admits a pointwise pre-image to obtain a lift.
Note, that the map is not well defined by this data: $K$ will have $\deg P$ many embeddings.
"""
function completion(K::AnticNumberField, P::NfOrdIdl)
  #non-unique!! will have deg(P) many
  p = minimum(P)
  C = qAdicConj(K, Int(p))
  g = conjugates(P.gen_two.elem_in_nf, C)
#  @show map(x->valuation(x), g)
  i = findfirst(x->valuation(x) > 0, g)
  return completion(K, p, i[1])
end

completion(K::AnticNumberField, p::Integer, i::Int) = completion(K, fmpz(p), i)

@doc Markdown.doc"""
    completion(K::AnticNumberField, p::fmpz, i::Int) -> FlintQadicField, Map

The completion corresponding to the $i$-th conjugate in the non-canonical ordering of
`conjugates`.
"""
function completion(K::AnticNumberField, p::fmpz, i::Int)
  C = qAdicConj(K, Int(p))
  @assert 0<i<= degree(K)

  ca = conjugates(gen(K), C, all = true, flat = false)[i]
  return completion(K, ca)
end

function completion(K::AnticNumberField, ca::qadic)  
  p = prime(parent(ca))
  C = qAdicConj(K, Int(p))
  r = roots(C.C, precision(ca))
  i = findfirst(x->parent(r[x]) == parent(ca) && r[x] == ca, 1:length(r))
  Zx = PolynomialRing(FlintZZ, cached = false)[1]
  function inj(a::nf_elem)
    d = denominator(a)
    pr = precision(parent(ca))
    if pr > precision(ca)
      ri = roots(C.C, precision(parent(ca)))[i]
    else
      ri = ca
    end
    return inv(parent(ca)(d))*(Zx(a*d)(ri))
  end
  # gen(K) -> conj(a, p)[i] -> a = sum a_i o^i
  # need o = sum o_i a^i
  R, mR = ResidueField(parent(ca))

  # Construct the array of powers of the primitive element.
  pa = [one(R), mR(ca)]
  d = degree(R)
  while length(pa) < d
    push!(pa, pa[end]*pa[2])
  end

  # Solve a linear system to figure out how to express the root of the
  # Conway Polynomial defining the completion in terms of the image of the
  # primitive element of the number field $K$.
  m = matrix(GF(p), d, d, [coeff(pa[i], j-1) for j=1:d for i=1:d])
  o = matrix(GF(p), d, 1, [coeff(gen(R), j-1) for j=1:d])
  s = solve(m, o)
  @hassert :qAdic 1 m*s == o

  # Construct the Conway root in the number field.
  a = K()
  for i=1:d
    _num_setcoeff!(a, i-1, lift(s[i,1]))
  end

  # Construct the derivative of the Conway root in the number field.
  f = defining_polynomial(parent(ca), FlintZZ)
  fso = inv(derivative(f)(gen(R)))
  o = matrix(GF(p), d, 1, [coeff(fso, j-1) for j=1:d])
  s = solve(m, o)
  b = K()
  for i=1:d
    _num_setcoeff!(b, i-1, lift(s[i,1]))
  end

  #TODO: don't use f, use the factors i the HenselCtx
  #seems to be slower...
#  lf = factor_mod_pk(Array, C.C.H, Int(C.C.H.N))
#  jj = findfirst(x->iszero(x[1](ca)), lf)
#  Kjj = number_field(lf[jj][1], check = false, cached = false)[1]
#  ajj = Kjj(parent(Kjj.pol)(a))
#  bjj = Kjj(parent(Kjj.pol)(b))
#  cjj = lift_root(f, ajj, bjj, p, 10)
#  c = K(parent(K.pol)(cjj))

  # Lift the data from the residue field back to Qp.
  c = lift_root(f, a, b, p, 10)
  pc = fmpz(10)
  function lif(x::qadic)
    if iszero(x)
      return K(0)
    end
    if precision(x) > pc
      #XXX this changes (c, pc) inplace as a cache
      #probably should be done with a new map type that can
      #store c, pc on the map.
      d = lift_root(f, a, b, p, precision(x))
#  Kjj = number_field(lf[jj][1], check = false, cached = false)[1]
#  ajj = Kjj(parent(Kjj.pol)(a))
#  bjj = Kjj(parent(Kjj.pol)(b))
#  djj = lift_root(f, ajj, bjj, p, 10)
#  d = K(parent(K.pol)(djj))
      ccall((:nf_elem_set, libantic), Nothing, (Ref{nf_elem}, Ref{nf_elem}, Ref{AnticNumberField}), c, d, K)
      ccall((:fmpz_set_si, libflint), Nothing, (Ref{fmpz}, Cint), pc, precision(x))
    elseif precision(x) < pc
      d = mod_sym(c, p^precision(x))
    else
      d = c
    end
    n = x.length
    r = K(lift(coeff(x, n-1)))
    pk = p^precision(x)
    while n > 1
      n -= 1
      r = mod_sym(r*d, pk) + lift(coeff(x, n-1))
    end
    return r#*K(p)^valuation(x)
  end
  return parent(ca), MapFromFunc(inj, lif, K, parent(ca))
end

####
#   Conjugates in ramified completions.
#   Galois closures
#
#########################################################################################

@doc Markdown.doc"""
    field_of_definition(a::padic)
    field_of_definition(a::qadic)
Returns the degree of the extension defining `a`.
"""
function degree_of_field_of_definition(a::qadic)
    for d in filter(x->x>0, divisors(degree(parent(a))))
        if a == frobenius(a,d)
            return d
        end
    end
    error("No power of frobenius of $a equals $a.")
end

function degree_of_field_of_definition(a::padic)
    return 1
end


@doc Markdown.doc"""
    galois_closure(K::EisensteinField)
Returns an Eisenstein field `L` such that `L/Qp` is Galois. Also return a map.
Note that the Eisenstein Field will be over a Qadic base, which might be an extension of
the base field of $K$.
"""
function galois_closure(K::EisensteinField)
    !is_tamely_ramified(K) && error("Wild ramification still not possible.")
    is_tamely_ramified(K) && return _galois_closure_tamely_ramified(K)
end

function galois_closure(K::FlintLocalField)
    return K, x->x
end

function _galois_closure_tamely_ramified(K::EisensteinField)
    L, mp_to_squash = simple_extension(K)

    # TODO: Add reference.
    # The size of the Galois closure of a tamely ramified extension is given by
    # the classification of tamely ramified extensions. (given by a poly of the form `X^e-u*p`.)
    # 
    frob_orbit_size = lcm(map(degree_of_field_of_definition, coeffs(L.pol)))

    g = change_base_ring(L, L.pol)
    X = gen(parent(g))
    h = fprimpart(g(uniformizer(L)*X))

    # Note that $h$ is guarenteed to be squarefree over the residue field by the
    # tameness assumption, since the degree of `h` is coprime to `p`.

    k,res = ResidueField(L)
    ext_degrees = map(x->degree(x[1]), factor(map_coeffs(res, h)))

    Lgal, _, mp_to_gal = unramified_extension(L, frob_orbit_size*lcm(ext_degrees))
    
    return Lgal, x->mp_to_gal(mp_to_squash(x))

end

@doc Markdown.doc"""
    is_tamely_ramified(K::NALocalField)
"""
function is_tamely_ramified(K::NALocalField)
    return gcd(prime(K), ramification_degree(K)) == 1
end

#########################################################################################
#
#   Conjugates in ramified completions.
#
#########################################################################################


#=
#1. Need to construct the ramified completion.

#2. Need to determine the unramified sub-extension of the splitting field 
#   (possible in stupid cases, but in general requires factorizations.)

# For now, give up if the splitting field is not just an unramified extension.

#3. Compute the roots in the local splitting field.

Generally, this will work so long as there is no wild ramification. The wild case is easy
to detect.
=#

