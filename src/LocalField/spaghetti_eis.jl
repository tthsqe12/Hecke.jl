


## Payani's algorithm.

eisf_elem = Hecke.eisf_elem

residue_image = Hecke.residue_image

# TODO: Various division operators and coefficient manipulations need to be implemented.

# Citation "krasner.pdf"
import Base.//
function //(f::Hecke.Generic.Poly{T}, b::T) where T <: Union{padic,eisf_elem}
    g = deepcopy(f)
    for i=1:degree(f)+1
        g.coeffs[i] = g.coeffs[i]//b
    end
    return g
end


function primitive_part(f)
    K = base_ring(f)
    val,i = findmin( valuation.(coefficients(f)) )
    return f//coefficients(f)[i-1]
end

import Markdown
@doc Markdown.doc"""
    number_of_roots(K, f)
Given an eisenstein extension `K` and a polynomial $f \in K[x]$, return the number of roots of `f` defined over `K`.
"""
function number_of_roots(K, f)

    base_ring(f) != K && error("The polynomial should be over the base ring $K.")

    x = gen(parent(f))
    pi = uniformizer(K)
    C = [primitive_part(f)]
    m = 0

    while !isempty(C)
        c = pop!(C)        
        cp = change_base_ring(c, residue_image)
        Rfp = parent(cp)
        rts = roots(cp)
        
        for rt in rts
            
            h = primitive_part( c(pi*x + K(lift(rt))) )
            hp = change_base_ring(h, residue_image)
            
            if degree( hp ) == 1
                m += 1
            elseif degree(hp) > 1
                push!(C, h)        
            end
        end

        if length(C) >= degree(f)
            error("Code has clearly gone wrong")
        end
    end
    return m
end

############################################################

# Lifting the roots looks like the next step...

my_setprecision!(f,N) = f

# Should use a precision access function rather than a "__.N".

#XXX: valuation(Q(0)) == 0 !!!!!
function newton_lift(f::Hecke.Generic.Poly{eisf_elem}, r::eisf_elem)

    # The many setprecision! calls are likely not valid for an approximately defined
    # polynomial.

    r.N = 1 # TODO: should be removed.
    
    K = parent(r)
    #n = K.prec_max
    n = 30
    
    i = n
    chain = [n]
    while i>2
        i = div(i+1, 2)
        push!(chain, i)
    end
    df  = derivative(f)
    fK  = change_base_ring(f, K)
    dfK = change_base_ring(df, K)

    @assert r.N == 1          # Ensure the residue is well-defined.
    df_at_r_inverse = K(r)    # Cache and update the values of 1/dfK(r)
    df_at_r_inverse.N = 1
    df_at_r_inverse = inv(my_setprecision!(dfK, 1)(df_at_r_inverse))
    
    #s = fK(r)

    for current_precision in reverse(chain)
        
        r.N               = current_precision
        df_at_r_inverse.N = current_precision
        #K.prec_max = r.N
        my_setprecision!(fK, r.N)
        my_setprecision!(dfK, r.N)        
        r = r - fK(r) * df_at_r_inverse
        #if r.N >= n
        #    K.prec_max = n
        #    return r
        #end

        # Update the value of the derivative.
        df_at_r_inverse = df_at_r_inverse*(2-dfK(r)*df_at_r_inverse)        
    end

    return r
end

import Hecke.roots

if false
function roots(K::Hecke.EisensteinField{padic}, f)

    base_ring(f) != K && error("The polynomial should be over the base ring $K.")

    x = gen(parent(f))
    pi = uniformizer(K)
    C = [primitive_part(f)]

    roots_out = []

    while !isempty(C)
        c = pop!(C)        
        cp = change_base_ring(c, residue_image)
        Rfp = parent(cp)
        rts = roots(cp)
        
        for rt in rts

            beta = K(lift(rt))
            
            h = primitive_part( c(pi*x + beta ) )
            hp = change_base_ring(h, residue_image)
            
            if degree( hp ) == 1
                rr = K(lift(roots(hp)[1]))
                rr.N = 1
                h_root = newton_lift(h,rr)
                push!(roots_out, h_root*pi)
            elseif degree(hp) > 1
                push!(C, h)        
            end
        end

        if length(C) >= degree(f)
            error("Code has clearly gone wrong")
        end
    end
    return roots_out
end
end # if false block

# The recursive version that actually makes sense.
#
# TODO: XXX: f is assumed to be "square-free".
#            
function integral_roots(K::Hecke.EisensteinField{padic},f)

    base_ring(f) != K && error("The polynomial should be over the base ring $K.")

    x = gen(parent(f))
    pi = uniformizer(K)
    roots_type = typeof(zero(K))
    
    fprim = primitive_part(f)
    fp = change_base_ring(fprim, residue_image)

    rts = roots(fp)

    if length(rts)==0
        # There are no roots in the padic unit disk        
        return roots_type[]
        
    elseif degree(fp) == degree(fprim) == 1
        # There is exactly one root, which can be Hensel lifted
        rr = K(lift(rts[1]))
        return [newton_lift(fprim,rr)]

    else
        # There are multiple roots in the unit disk. Zoom in on each.
        roots_out = roots_type[]
        for beta in rts
            beta_lift = K(lift(beta))
            roots_near_beta = roots_recursive( K, fprim(pi*x + beta_lift) )
            roots_out = vcat(roots_out, [pi*r + beta_lift for r in roots_near_beta] )
        end
        
        return roots_out
    end
    error("Something has gone quite wrong.")
end

function roots(K::Hecke.EisensteinField{padic},f)
    Ov_roots   = integral_roots(K,f)
    outside_Ov_roots = integral_roots(K,reverse(f))
    filter!(r->r!=K(0), outside_Ov_roots)
    return vcat(Ov_roots, [inv(rt) for rt in outside_Ov_roots])
end

nothing
