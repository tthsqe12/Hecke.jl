mutable struct LatRel
  K::AnticNumberField
  form::Mat{nf_elem}  # Gram matrix of the "basis" vectors
  inner::Mat{nf_elem} # Inner product on the ambient space?
  discriminant
  pmat::PMat{nf_elem, NfOrdFracIdl}
  pmatinv::PMat{nf_elem, NfOrdFracIdl}
  scale
  definite
  genus_symbols
  zforms

  function LatRel(K::AnticNumberField, d::Int)
    z = new()
    z.K = K
    z.form = identity_matrix(K, d)
    z.pmat = pseudo_matrix(identity_matrix(K, d))
    return z
  end

  function LatRel(K::AnticNumberField, d::Int, G::MatElem{nf_elem})
    z = new()
    z.K = K
    z.form = G
    z.pmat = pseudo_matrix(identity_matrix(K, d))
    return z
  end
end

function lattice(K::AnticNumberField, d::Int)
  return LatRel(K, d)
end

function lattice(K::AnticNumberField, d::Int, G::MatElem{nf_elem})
  return LatRel(K, d, G)
end

number_field(L::LatRel) = L.K

base_field(L::LatRel) = L.K

function Base.show(io::IO, L::LatRel)
  print(IOContext(io, :compact => true), "Lattice over ", number_field(L))
end

pseudo_matrix(L::LatRel) = L.pmat

mutable struct LatRelElem
  data::Vector{nf_elem}
  coordinates::Vector{nf_elem}
  parent::LatRel

  function LatRelElem(L::LatRel, v::Vector{nf_elem})
    z = new()
    z.parent = L
    z.data = v
    return z
  end
  
  function LatRelElem(L::LatRel, v::Vector{nf_elem}, coor::Vector{nf_elem})
    z = new()
    z.parent = L
    z.data = v
    z.coor
    return z
  end
end

function (L::LatRel)(v::Vector{nf_elem}; check::Bool = true)
  if check
    b, coo = _in_span(v, pseudo_matrix(L))
    !b && error("Vector does not yield an element in lattice")
    return LatRelElem(L, v, coo)
  end
  return LatRelElem(L, v)
end

function (L::LatRel)(v::Vector)
  w = map(base_field(L), v)
  wK = convert(Vector{nf_elem}, w)
  return L(wK)
end

