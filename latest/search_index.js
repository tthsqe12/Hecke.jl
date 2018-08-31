var documenterSearchIndex = {"docs": [

{
    "location": "index.html#",
    "page": "Hecke",
    "title": "Hecke",
    "category": "page",
    "text": ""
},

{
    "location": "index.html#Hecke-1",
    "page": "Hecke",
    "title": "Hecke",
    "category": "section",
    "text": ""
},

{
    "location": "index.html#About-1",
    "page": "Hecke",
    "title": "About",
    "category": "section",
    "text": "Hecke is a software package for algebraic number theory maintained by Claus Fieker and Tommy Hofmann. It is written in julia and is based on the computer algebra package Nemo.https://github.com/thofma/Hecke.jl (Source code)\nhttp://thofma.github.io/Hecke.jl/latest/ (Online documentation)So far, Hecke provides the following features:Orders (including element and ideal arithmetic) in number fields\nComputation of maximal orders\nVerified residue computations of Dedekind zeta functions\nClass and Unit group computation, S-units, PID testing\nLattice enumeration\nSparse linear algebra\nNormal forms for modules over maximal orders\nExtensions of number fields, non-simple extensions of number fields\nOrders and ideals in extensions of fields\nAbelian groups\nRay class groups, quotients of ray class groups\nInvariant subgroups\nDefining equations for class fields"
},

{
    "location": "index.html#Installation-1",
    "page": "Hecke",
    "title": "Installation",
    "category": "section",
    "text": "To use Hecke, a julia version of 0.6 or higher is necessary (the latest stable julia version will do). Please see http://julialang.org/downloads for instructions on how to obtain julia for your system. Once a suitable julia version is installed, use the following steps at the julia prompt to install Hecke:julia> Pkg.add(\"Hecke\")"
},

{
    "location": "index.html#Quick-start-1",
    "page": "Hecke",
    "title": "Quick start",
    "category": "section",
    "text": "Here is a quick example of using Hecke:julia> using Hecke\n...\n\nWelcome to \n\n  _    _           _        \n | |  | |         | |       \n | |__| | ___  ___| | _____ \n |  __  |/ _ \\/ __| |/ / _ \\\n | |  | |  __/ (__|   <  __/\n |_|  |_|\\___|\\___|_|\\_\\___|\n  \nVersion 0.4.0 ... \n ... which comes with absolutely no warranty whatsoever\n(c) 2015, 2016, 2017 by Claus Fieker and Tommy Hofmann\n\njulia> Qx, x = PolynomialRing(FlintQQ, \"x\");\njulia> f = x^3 + 2;\njulia> K, a = NumberField(f, \"a\");\njulia> O = maximal_order(K);\njulia> O\nMaximal order of Number field over Rational Field with defining polynomial x^3 + 2 \nwith basis [1,a,a^2]The documentation of the single functions can also be accessed at the julia prompt. Here is an example:help?> signature\nsearch: signature\n\n  ----------------------------------------------------------------------------\n\n  signature(O::NfMaximalOrder) -> Tuple{Int, Int}\n\n  |  Returns the signature of the ambient number field of \\mathcal O."
},

{
    "location": "number_fields/intro.html#",
    "page": "Number Fields",
    "title": "Number Fields",
    "category": "page",
    "text": ""
},

{
    "location": "number_fields/intro.html#Number-Fields-1",
    "page": "Number Fields",
    "title": "Number Fields",
    "category": "section",
    "text": "CurrentModule = Hecke"
},

{
    "location": "number_fields/intro.html#NumberFieldsLink-1",
    "page": "Number Fields",
    "title": "Introduction",
    "category": "section",
    "text": "This chapter deals with number fields. Number fields, in Hecke, come in several different types:AnticNumberField: a finite simple extension of the rational numbers Q\nNfAbsNS: a finite extension of Q given by several polynomials.We will refer to this as a non-simple field - even though mathematically  we can find a primitive elements.NfRel: a finite simple extension of a number field. This is   actually parametried by the (element) type of the coefficient field.  The complete type of an extension of an absolute field (AnticNumberField)  is NfRel{nf_elem}. The next extension thus will be  NfRel{NfRelElem{nf_elem}}.\nNfRel_ns: extensions of number fields given by several polynomials.  This too will be refered to as a non-simple field.The simple types AnticNumberField and NfRel are also calle simple fields in the rest of this document, NfRel and NfRel_ns are referred to as relative extensions while AnticNumberField and NfAbsNS are called absolute.Internally, simple fields are essentially just (univariate) polynomial quotients in a dense representation, while non-simple fields are multivariate quotient rings, thus have a sparse presentation. In general, simple fields allow much faster arithmetic, while  the non-simple fields give easy access to large degree fields."
},

{
    "location": "number_fields/intro.html#Absolute-Simple-Fields-1",
    "page": "Number Fields",
    "title": "Absolute Simple Fields",
    "category": "section",
    "text": "The most basic number field type is that of AnticNumberField. Internally this is essentially represented as a unvariate quotient with the arithmetic provided by the antic-c-library and implemented in Nemo."
},

{
    "location": "number_fields/intro.html#Nemo.NumberField-Tuple{fmpq_poly}",
    "page": "Number Fields",
    "title": "Nemo.NumberField",
    "category": "method",
    "text": "NumberField(f::fmpq_poly; cached::Bool = true, check::Bool = true)\n\nThe number field Q[x]/f generated by f.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.cyclotomic_field-Tuple{Int64}",
    "page": "Number Fields",
    "title": "Hecke.cyclotomic_field",
    "category": "method",
    "text": "cyclotomic_field(n::Int) -> AnticNumberField, nf_elem\n\nThe n-th cyclotomic field defined by the n-the cyclotomic polynomial.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.wildanger_field-Tuple{Int64,fmpz}",
    "page": "Number Fields",
    "title": "Hecke.wildanger_field",
    "category": "method",
    "text": "wildanger_field(n::Int, B::fmpz) -> AnticNumberField, nf_elem\nwildanger_field(n::Int, B::Integer) -> AnticNumberField, nf_elem\n\nReturns the field with defining polynomial x^n + sum_i=0^n-1 (-1)^n-iBx^i. These fields tend to have non-trivial class groups.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.pure_extension-Tuple{Int64,Integer}",
    "page": "Number Fields",
    "title": "Hecke.pure_extension",
    "category": "method",
    "text": "pure_extension(n::Int, gen::Integer; cached::Bool = true, check::Bool = true) -> AnticNumberField, nf_elem\npure_extension(n::Int, gen::fmpz; cached::Bool = true, check::Bool = true) -> AnticNumberField, nf_elem\n\nThe number field with defining polynomial x^n-gen.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Creation-1",
    "page": "Number Fields",
    "title": "Creation",
    "category": "section",
    "text": "Number fields are mostly created using NumberField, but also using number_field.Many of the constructors have arguments of type Symbol or AbstractString, if used, they define the appearance in printing, and printing only. The named parameter check can be true or false, the default beingtrue`. This parameter controlls is the polynomial defining the number field is tested for irreducibility or not. Given that this can be potentially  very time consuiming if the degree if large, one can omit this test. Note however, that the behaviour of Hecke is undefined if a reducible polynomial is used to define a \"field\".The named boolean parameter cached is inherited from the underlying Nemo system. Two number fields defined using the same polynomial from the identical polynomial ring and the same (identical) symbol/ string will be identical if cached == true and different if cached == false.NumberField(f::fmpq_poly)\ncyclotomic_field(n::Int)\n#CyclotomicField(n::Int, s::AbstractString, t; cached)\n#CyclotomicField(n::Int, s::AbstractString, t)\n#CyclotomicField(n::Int, s::AbstractString)\n#MaximalRealSubfield(n::Int, s::AbstractString)\n#MaximalRealSubfield(n::Int, s::AbstractString, t)\nwildanger_field(n::Int, B::fmpz)\npure_extension(n::Int, gen::Integer)"
},

{
    "location": "number_fields/intro.html#Example-1",
    "page": "Number Fields",
    "title": "Example",
    "category": "section",
    "text": "using Hecke # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nK, a = NumberField(x^2 - 10, \"a\");"
},

{
    "location": "number_fields/intro.html#Absolute-Non-Simple-Fields-1",
    "page": "Number Fields",
    "title": "Absolute Non-Simple Fields",
    "category": "section",
    "text": ""
},

{
    "location": "number_fields/intro.html#Nemo.NumberField",
    "page": "Number Fields",
    "title": "Nemo.NumberField",
    "category": "function",
    "text": "number_field(f::Array{fmpq_poly, 1}, s::String=\"_\\$\") -> NfAbsNS\n\nLet f = (f_1 ldots f_n) be univariate rational polynomials, then we construct \n\nK = Qt_1 ldots t_nlangle f_1(t_1) ldots f_n(t_n)rangle\n\nThe ideal bust be maximal, however, this is not tested.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Creation-2",
    "page": "Number Fields",
    "title": "Creation",
    "category": "section",
    "text": "NumberField(f::Array{fmpq_poly, 1}, s::String=\"_\\$\")"
},

{
    "location": "number_fields/intro.html#Example-2",
    "page": "Number Fields",
    "title": "Example",
    "category": "section",
    "text": "using Hecke # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nK, g = number_field([x^2-2, x^2-3, x^2-5])\ng[1]^2\nminpoly(g[1] + g[2])"
},

{
    "location": "number_fields/intro.html#Hecke.simple_extension-Tuple{NfAbsNS}",
    "page": "Number Fields",
    "title": "Hecke.simple_extension",
    "category": "method",
    "text": "simple_extension(K::NfAbsNS) -> AnticNumberField, Map\n\nFor a non-simple extension K of Q, find a primitive element and thus an isomorphic simple extension of Q. The map realises this isomorphism.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Conversion-1",
    "page": "Number Fields",
    "title": "Conversion",
    "category": "section",
    "text": "simple_extension(K::NfAbsNS)"
},

{
    "location": "number_fields/intro.html#Simple-Relative-Fields-1",
    "page": "Number Fields",
    "title": "Simple Relative Fields",
    "category": "section",
    "text": ""
},

{
    "location": "number_fields/intro.html#Nemo.NumberField-Tuple{AbstractAlgebra.Generic.Poly}",
    "page": "Number Fields",
    "title": "Nemo.NumberField",
    "category": "method",
    "text": "NumberField(f::Generic.Poly{T}, s::String; cached::Bool = false, check::Bool = false) where T\n\nGiven an irreducible polynomial f over some number field K, create the field Ktf. f must be irreducible - although this is not tested.\n\n\n\nNumberField(f::Generic.Poly{T}; cached::Bool = false, check::Bool = false) where T\n\nGiven an irreducible polynomial f over some number field K, create the field Ktf. f must be irreducible - although this is not tested.\n\n\n\nnumber_field(f::Array{Generic.Poly{T}, 1}, s::String=\"_\\$\") where T -> NfRel_ns\n\nGiven polynomials f = (f_1 ldots f_n) over some number field k, construct K = kt_1 ldots t_nlangle f_1(t_1) ldots f_n(t_n)rangle The ideal in the quotient must be maximal - although this is not tested.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Nemo.NumberField-Tuple{AbstractAlgebra.Generic.Poly,String}",
    "page": "Number Fields",
    "title": "Nemo.NumberField",
    "category": "method",
    "text": "NumberField(f::Generic.Poly{T}, s::String; cached::Bool = false, check::Bool = false) where T\n\nGiven an irreducible polynomial f over some number field K, create the field Ktf. f must be irreducible - although this is not tested.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Creation-3",
    "page": "Number Fields",
    "title": "Creation",
    "category": "section",
    "text": "NumberField(f::Generic.Poly)\nNumberField(f::Generic.Poly, s::String)"
},

{
    "location": "number_fields/intro.html#Hecke.absolute_field-Tuple{Hecke.NfRel{nf_elem}}",
    "page": "Number Fields",
    "title": "Hecke.absolute_field",
    "category": "method",
    "text": "absolute_field(K::NfRel{nf_elem}, cached::Bool = false) -> AnticNumberField, Map, Map\n\nGiven an extension KkQ, find an isomorphic extensino of Q.\n\n\n\nabsolute_field(K::NfRel{NfRelElem}, cached::Bool = false) -> NfRel, Map, Map\n\nGiven an extension EKk, find an isomorphic extension of k. In a tower, only the top-most steps are collapsed.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.absolute_field-Tuple{Hecke.NfRel{Hecke.NfRelElem}}",
    "page": "Number Fields",
    "title": "Hecke.absolute_field",
    "category": "method",
    "text": "absolute_field(K::NfRel{NfRelElem}, cached::Bool = false) -> NfRel, Map, Map\n\nGiven an extension EKk, find an isomorphic extension of k. In a tower, only the top-most steps are collapsed.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Conversion-2",
    "page": "Number Fields",
    "title": "Conversion",
    "category": "section",
    "text": "absolute_field(K::NfRel{nf_elem})\nabsolute_field(K::NfRel{NfRelElem})"
},

{
    "location": "number_fields/intro.html#Non-Simple-Relative-Fields-1",
    "page": "Number Fields",
    "title": "Non-Simple Relative Fields",
    "category": "section",
    "text": ""
},

{
    "location": "number_fields/intro.html#Nemo.NumberField-Union{Tuple{Array{Poly{T},1}}, Tuple{T}, Tuple{Array{Poly{T},1},String}} where T",
    "page": "Number Fields",
    "title": "Nemo.NumberField",
    "category": "method",
    "text": "number_field(f::Array{Generic.Poly{T}, 1}, s::String=\"_\\$\") where T -> NfRel_ns\n\nGiven polynomials f = (f_1 ldots f_n) over some number field k, construct K = kt_1 ldots t_nlangle f_1(t_1) ldots f_n(t_n)rangle The ideal in the quotient must be maximal - although this is not tested.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Creation-4",
    "page": "Number Fields",
    "title": "Creation",
    "category": "section",
    "text": "NumberField(f::Array{Generic.Poly{T}, 1}, s::String=\"_\\$\") where T"
},

{
    "location": "number_fields/intro.html#Hecke.simple_extension-Tuple{NfRel_ns}",
    "page": "Number Fields",
    "title": "Hecke.simple_extension",
    "category": "method",
    "text": "simple_extension(K::NfRel_ns{nf_elem}) -> AnticNumberField, Map, Map\n\nCompute an isomorphic field as an extension of Q together with the isomorphism  (1st map) and the embedding of the base field (2nd map).\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.simple_extension-Tuple{NfRel_ns{nf_elem},FlintRationalField}",
    "page": "Number Fields",
    "title": "Hecke.simple_extension",
    "category": "method",
    "text": "simple_extension(K::NfRel_ns{nf_elem}, FlintQQ) -> AnticNumberField, Map, Map\n\nabsolute_field(K::NfRel_ns{nf_elem}) -> AnticNumberField, Map, Map\n\nCompute an isomorphic field as an extension of Q together with the isomorphism  (1st map) and the embedding of the base field (2nd map).\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Conversion-3",
    "page": "Number Fields",
    "title": "Conversion",
    "category": "section",
    "text": "simple_extension(K::NfRel_ns)\nsimple_extension(K::NfRel_ns{nf_elem}, ::FlintRationalField)"
},

{
    "location": "number_fields/intro.html#Base.minimum-Union{Tuple{T}, Tuple{T,NfAbsOrdIdl{AnticNumberField,nf_elem}}} where T<:(Map{AnticNumberField,AnticNumberField,S,T} where T where S)",
    "page": "Number Fields",
    "title": "Base.minimum",
    "category": "method",
    "text": "minimum(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField} -> NfOrdIdl\n\nGiven an embedding mkto K of number fields and an integral ideal in K, find the  intersection I cap Z_k.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#LinearAlgebra.norm-Union{Tuple{T}, Tuple{T,NfAbsOrdIdl{AnticNumberField,nf_elem}}} where T<:(Map{AnticNumberField,AnticNumberField,S,T} where T where S)",
    "page": "Number Fields",
    "title": "LinearAlgebra.norm",
    "category": "method",
    "text": "norm(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField} -> NfOrdIdl\n\nGiven an embedding mkto K of number fields and an integral ideal in K, find the norm N_Kk(I).\n\n\n\n"
},

{
    "location": "number_fields/intro.html#LinearAlgebra.norm-Union{Tuple{T}, Tuple{T,nf_elem}} where T<:(Map{AnticNumberField,AnticNumberField,S,T} where T where S)",
    "page": "Number Fields",
    "title": "LinearAlgebra.norm",
    "category": "method",
    "text": "norm(m::T, a::nf_elem) where T <: Map{AnticNumberField, AnticNumberField} -> nf_elem\n\nGiven an embedding mkto K of number fields and an element in K, find the norm N_Kk(a).\n\n\n\n"
},

{
    "location": "number_fields/intro.html#AbstractAlgebra.Generic.discriminant-Tuple{Map,NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Number Fields",
    "title": "AbstractAlgebra.Generic.discriminant",
    "category": "method",
    "text": "discriminant(m::Map, R::NfOrd) -> NfOrdIdl\n\nThe discriminant ideal of R over the maximal order of the domain of the map m,  that is, the ideal generated by all norms of differents of elements in R.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Implicit-Relative-Extensions-1",
    "page": "Number Fields",
    "title": "Implicit Relative Extensions",
    "category": "section",
    "text": "Given two absolute fields K and k as well as an embedding phik to K we can regard K as an extension on k, hence invariante of K can be investigated relative to k rathern than over Q. Here we list functions achieving this without actually computing K as an extension of k.minimum(m::T, I::NfOrdIdl) where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)\nnorm(m::T, I::Hecke.NfAbsOrdIdl{Nemo.AnticNumberField,Nemo.nf_elem}) where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)\nnorm(m::T, a::nf_elem)  where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)\ndiscriminant(m::Map, R::NfOrd)(I::NfAbsOrdIdlSet{Nemo.AnticNumberField,Nemo.nf_elem})(mp::Map, i::NfOrdIdl)"
},

{
    "location": "number_fields/intro.html#Invariants-1",
    "page": "Number Fields",
    "title": "Invariants",
    "category": "section",
    "text": "degree(::AnticNumberField)\nbasis(::AnticNumberField)\ndiscriminant(::AnticNumberField)"
},

{
    "location": "number_fields/intro.html#Elements-1",
    "page": "Number Fields",
    "title": "Elements",
    "category": "section",
    "text": ""
},

{
    "location": "number_fields/intro.html#Creation-5",
    "page": "Number Fields",
    "title": "Creation",
    "category": "section",
    "text": "(K::)(poly)\n(K::)(Integer)"
},

{
    "location": "number_fields/intro.html#Invariants-2",
    "page": "Number Fields",
    "title": "Invariants",
    "category": "section",
    "text": "norm(a)\nnorm(a, k)\nnorm(a, phi)\ntrace\nminpoly\ncharpoly\nrepmat\ncoeffs\nlength\nt2\nconjugates\nlogs\ndenominator\nnumerator\nisunit"
},

{
    "location": "orders/introduction.html#",
    "page": "Orders of number fields",
    "title": "Orders of number fields",
    "category": "page",
    "text": ""
},

{
    "location": "orders/introduction.html#Orders-of-number-fields-1",
    "page": "Orders of number fields",
    "title": "Orders of number fields",
    "category": "section",
    "text": ""
},

{
    "location": "orders/introduction.html#Introduction-1",
    "page": "Orders of number fields",
    "title": "Introduction",
    "category": "section",
    "text": "This chapter deals with absolute number fields and orders there of. "
},

{
    "location": "orders/introduction.html#Definitions-and-vocabulary-1",
    "page": "Orders of number fields",
    "title": "Definitions and vocabulary",
    "category": "section",
    "text": "We begin by collecting the necessary definitions and vocabulary.  This is in particular important for everything related to embeddings of number fields into archimedean fields, since they are at least two (slighlty) different normalizations. "
},

{
    "location": "orders/introduction.html#Number-fields-1",
    "page": "Orders of number fields",
    "title": "Number fields",
    "category": "section",
    "text": "By an absolute number field we mean finite extensions of mathbf Q, which is of type AnticNumberField and whose elements are of type nf_elem. Such an absolute number field K is always given in the form K = mathbf Q(alpha) = mathbf QX(f), where f in mathbf QX is an irreducible polynomial. See here for more information on the different types of fields supported.We call (1alphaalpha^2dotscalpha^d-1), where d is the degree K  mathbf Q the power basis of K. If beta is any element of K, then the representation matrix of beta is the matrix representing K to K gamma mapsto beta gamma with respect to the power basis, that is,\\[ \\beta \\cdot (1,\\alpha,\\dotsc,\\alpha^{d-1}) = M_\\alpha (1, \\alpha, \\dotsc, \\alpha^{d-1}). \\]Let (rs) be the signature of K, that is, K has r real embeddings sigma_i colon K to mathbfR, 1 leq i leq r, and 2s complex embeddings sigma_i colon K to mathbfC, 1 leq i leq 2s. In Hecke the complex embeddings are always ordered such that sigma_i = overlinesigma_i+s for r + 1 leq i leq r + s. The mathbfQ-linear function \\[ K \\longrightarrow \\mathbf R^{d}, \\ \\alpha \\longmapsto (\\sigma1(\\alpha),\\dotsc,\\sigmar(\\alpha),\\sqrt{2}\\operatorname{Re}(\\sigma{r+1}(\\alpha)),\\sqrt{2}\\operatorname{Im}(\\sigma{r+1}(\\alpha)),\\dotsc,\\sqrt{2}\\operatorname{Re}(\\sigma{r+s}(\\alpha)),\\sqrt{2}\\operatorname{Im}(\\sigma{r+s}(\\alpha)) \\] is called the Minkowski map (or Minkowski embedding)."
},

{
    "location": "orders/introduction.html#Orders-1",
    "page": "Orders of number fields",
    "title": "Orders",
    "category": "section",
    "text": "If K = mathbf Q(alpha) is an absolute number field, then an order mathcal O of K is a subring of the ring of integers mathcal O_K, which is free of rank  K  mathbf Q as a mathbf Z-module. The natural order mathbf Zalpha is called the equation order of K. In Hecke orders of absolute number fields are constructed (implicitely) by specifying a mathbf Z-basis, which is refered to as the basis of mathcal O. If (omega_1dotscomega_d) is the basis of mathcal O, then the matrix B in operatornameMat_d times d(mathbf Q) with\\[ \\begin{pmatrix} \\omega1 \\\\ \\vdots \\\\ \\omegad \\end{pmatrix} = B \\begin{pmatrix} 1 \\\\ \\vdots \\\\ \\alpha^{d - 1} \\end{pmatrix} \\]is called the basis matrix of mathcal O. We call det(B) the generalized index of mathcal O.  In case mathbf Zalpha subseteq mathcal O, the determinant det(B)^-1 is in fact equal to  mathcal O  mathbf Zalpha and is called the index of mathcal O. The matrix \\[ \\begin{pmatrix}  \\sigma1(\\omega1) & \\dotsc & \\sigmar(\\omega1) & \\sqrt{2}\\operatorname{Re}(\\sigma{r+1}(\\omega1)) & \\sqrt{2}\\operatorname{Im}(\\sigma{r+1}(\\omega1)) & \\dotsc & \\sqrt{2}\\operatorname{Im}(\\sigma{r+s}(\\omega1)) \\\\\n\\sigma1(\\omega2) & \\dotsc & \\sigmar(\\omega2) & \\sqrt{2}\\operatorname{Re}(\\sigma{r+1}(\\omega2)) & \\sqrt{2}\\operatorname{Im}(\\sigma{r+1}(\\omega2)) & \\dotsc  & \\sqrt{2}\\operatorname{Im}(\\sigma{r+s}(\\omega2)) \\\\\n\\vdots & \\dotsc & \\vdots & \\vdots & \\dotsc & \\vdots & \\vdots\\\\\n\\sigma1(\\omegad) & \\dotsc & \\sigmar(\\omegad) & \\sqrt{2}\\operatorname{Re}(\\sigma{r+1}(\\omegad)) & \\sqrt{2}\\operatorname{Im}(\\sigma{r+2}(\\omegad)) & \\dotsc & \\sqrt{2}\\operatorname{Im}(\\sigma{r+s}(\\omegad)) \\end{pmatrix} \\in \\operatorname{Mat}_{d\\times d}(\\mathbf R). \\] is called the Minkowski matrix of mathcal O."
},

{
    "location": "orders/introduction.html#Ideals-1",
    "page": "Orders of number fields",
    "title": "Ideals",
    "category": "section",
    "text": ""
},

{
    "location": "orders/introduction.html#Fractional-ideals-1",
    "page": "Orders of number fields",
    "title": "Fractional ideals",
    "category": "section",
    "text": ""
},

{
    "location": "orders/introduction.html#Types-1",
    "page": "Orders of number fields",
    "title": "Types",
    "category": "section",
    "text": ""
},

{
    "location": "orders/basics.html#",
    "page": "Basics",
    "title": "Basics",
    "category": "page",
    "text": ""
},

{
    "location": "orders/basics.html#Basics-1",
    "page": "Basics",
    "title": "Basics",
    "category": "section",
    "text": "CurrentModule = Hecke"
},

{
    "location": "orders/basics.html#Hecke.Order-Tuple{AnticNumberField,Array{nf_elem,1}}",
    "page": "Basics",
    "title": "Hecke.Order",
    "category": "method",
    "text": "Order(B::Array{nf_elem, 1}, check::Bool = true) -> NfOrd\n\nReturns the order with mathbf Z-basis B. If check is set, it is checked whether B defines an order.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.Order-Tuple{AnticNumberField,FakeFmpqMat}",
    "page": "Basics",
    "title": "Hecke.Order",
    "category": "method",
    "text": "Order(K::AnticNumberField, A::FakeFmpqMat, check::Bool = true) -> NfOrd\n\nReturns the order which has basis matrix A with respect to the power basis of K. If check is set, it is checked whether A defines an order.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.Order-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Basics",
    "title": "Hecke.Order",
    "category": "method",
    "text": "Order(K::AnticNumberField, A::fmpz_mat, check::Bool = true) -> NfOrd\n\nReturns the order which has basis matrix A with respect to the power basis of K. If check is set, it is checked whether A defines an order.\n\n\n\nOrder(A::NfOrdFracIdl) -> NfOrd\n\nReturns the fractional ideal A as an order of the ambient number field.\n\n\n\n\n\n  Order(K::RelativeExtension, M::PMat) -> NfRelOrd\n\nReturns the order which has basis pseudo-matrix M with respect to the power basis of K.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.EquationOrder-Tuple{AnticNumberField}",
    "page": "Basics",
    "title": "Hecke.EquationOrder",
    "category": "method",
    "text": "EquationOrder(K::AnticNumberField) -> NfOrd\n\nReturns the equation order of the number field K.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.MaximalOrder-Tuple{AnticNumberField}",
    "page": "Basics",
    "title": "Hecke.MaximalOrder",
    "category": "method",
    "text": "maximal_order(K::AnticNumberField) -> NfOrd\nring_of_integers(K::AnticNumberField) -> NfOrd\n\nReturns the maximal order of K.\n\nExample\n\njulia> Qx, xx = FlintQQ[\"x\"];\njulia> K, a = NumberField(x^3 + 2, \"a\");\njulia> O = MaximalOrder(K);\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.MaximalOrder-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.MaximalOrder",
    "category": "method",
    "text": "\n\nmaximal_order(O::NfOrd) -> NfOrd\nMaximalOrder(O::NfOrd) -> NfOrd\n\nReturns the maximal overorder of O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.maximal_order-Tuple{AnticNumberField}",
    "page": "Basics",
    "title": "Hecke.maximal_order",
    "category": "method",
    "text": "maximal_order(K::AnticNumberField) -> NfOrd\nring_of_integers(K::AnticNumberField) -> NfOrd\n\nReturns the maximal order of K.\n\nExample\n\njulia> Qx, xx = FlintQQ[\"x\"];\njulia> K, a = NumberField(x^3 + 2, \"a\");\njulia> O = MaximalOrder(K);\n\n\n\n"
},

{
    "location": "orders/basics.html#Nemo.lll-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Nemo.lll",
    "category": "method",
    "text": "lll(M::NfOrd) -> NfOrd\n\nThe same order, but with the basis now being LLL reduced wrt. the Minkowski metric.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.maximal_order-Tuple{AnticNumberField,Array{fmpz,1}}",
    "page": "Basics",
    "title": "Hecke.maximal_order",
    "category": "method",
    "text": "\n\nMaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd\nmaximal_order(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd\nring_of_integers(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd\n\nAssuming that primes contains all the prime numbers at which the equation order mathbfZalpha of K = mathbfQ(alpha) is not maximal, this function returns the maximal order of K.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.pradical-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Basics",
    "title": "Hecke.pradical",
    "category": "method",
    "text": "pradical(O::NfOrd, p::{fmpz|Integer}) -> NfAbsOrdIdl\n\nGiven a prime number p, this function returns the p-radical sqrtpmathcal O of mathcal O, which is just  x in mathcal O mid exists k in mathbf Z_geq 0 colon x^k in pmathcal O . It is not checked that p is prime.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.ring_of_multipliers-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.ring_of_multipliers",
    "category": "method",
    "text": "\n\nring_of_multipliers(I::NfAbsOrdIdl) -> NfOrd\n\nComputes the order (I  I), which is the set of all x in K with xI subseteq I.\n\n\n\n"
},

{
    "location": "orders/basics.html#Creation-and-basic-properties-1",
    "page": "Basics",
    "title": "Creation and basic properties",
    "category": "section",
    "text": "Order(::AnticNumberField, ::Array{nf_elem, 1})\nOrder(::AnticNumberField, ::FakeFmpqMat)\nOrder(::NfOrdFracIdl)\nEquationOrder(::AnticNumberField)\nMaximalOrder(::AnticNumberField)\nMaximalOrder(::NfOrd)\nmaximal_order(::AnticNumberField)\nlll(::NfOrd)By Chistov\'s fundamental theorem, the computation of the maximal order is basically as hard as the factorisation of the discriminant. In order to help the computer, Hecke also provides the following signatures:maximal_order(::AnticNumberField, ::Array{fmpz, 1})It is also possible the execute the steps individually:pradical(::NfOrd, ::fmpz)\nring_of_multipliers(::NfOrdIdl)"
},

{
    "location": "orders/basics.html#Base.parent-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.parent",
    "category": "method",
    "text": "parent(O::NfOrd) -> NfOrdSet\n\nReturns the parent of mathcal O, that is, the set of orders of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.isequation_order-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.isequation_order",
    "category": "method",
    "text": "isequation_order(O::NfOrd) -> Bool\n\nReturns whether mathcal O is the equation order of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/basics.html#Nemo.signature-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Nemo.signature",
    "category": "method",
    "text": "signature(O::NfOrd) -> Tuple{Int, Int}\n\nReturns the signature of the ambient number field of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.nf-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.nf",
    "category": "method",
    "text": "nf(O::NfOrd) -> AnticNumberField\n\nReturns the ambient number field of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.degree-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.degree",
    "category": "method",
    "text": "degree(O::NfOrd) -> Int\n\nReturns the degree of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.basis-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.basis",
    "category": "method",
    "text": "basis(O::NfOrd) -> Array{NfOrdElem, 1}\n\nReturns the mathbf Z-basis of mathcal O.\n\n\n\n\n\nbasis(A::NfAbsOrdIdl) -> Array{NfOrdElem, 1}\n\nReturns the basis of A.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.basis-Tuple{NfAbsOrd{AnticNumberField,nf_elem},AnticNumberField}",
    "page": "Basics",
    "title": "Hecke.basis",
    "category": "method",
    "text": "basis(O::NfOrd, K::AnticNumberField) -> Array{nf_elem, 1}\n\nReturns the mathbf Z-basis elements of mathcal O as elements of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.basis_mat-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.basis_mat",
    "category": "method",
    "text": "basis_mat(O::NfOrd) -> FakeFmpqMat\n\nReturns the basis matrix of mathcal O with respect to the power basis of the ambient number field.\n\n\n\n\n\nbasismat(A::NfAbsOrdIdl) -> fmpzmat\n\nReturns the basis matrix of A.\n\n\n\n\n\n  basis_mat(O::NfRelOrd{T, S}) -> Generic.Mat{T}\n\nReturns the basis matrix of mathcal O with respect to the power basis of the ambient number field.\n\n\n\n\n\n  basis_mat(a::NfRelOrdIdl{T, S}) -> Generic.Mat{T}\n  basis_mat(a::NfRelOrdFracIdl{T, S}) -> Generic.Mat{T}\n\nReturns the basis matrix of a.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.basis_mat_inv-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.basis_mat_inv",
    "category": "method",
    "text": "basis_mat_inv(O::NfOrd) -> FakeFmpqMat\n\nReturns the inverse of the basis matrix of mathcal O.\n\n\n\n\n\nbasismatinv(A::NfAbsOrdIdl) -> fmpz_mat\n\nReturns the inverse basis matrix of A.\n\n\n\n\n\n  basis_mat_inv(O::NfRelOrd{T, S}) -> Generic.Mat{T}\n\nReturns the inverse of the basis matrix of mathcal O.\n\n\n\n\n\n  basis_mat_inv(a::NfRelOrdIdl{T, S}) -> Generic.Mat{T}\n  basis_mat_inv(a::NfRelOrdFracIdl{T, S}) -> Generic.Mat{T}\n\nReturns the inverse of the basis matrix of a.\n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.discriminant-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.discriminant",
    "category": "method",
    "text": "discriminant(O::NfOrd) -> fmpz\n\nReturns the discriminant of mathcal O.\n\n\n\n\n\ndiscriminant(B::Array{NfAbsOrdElem, 1}) -> fmpz\n\nReturns the discriminant of the family B.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.gen_index-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.gen_index",
    "category": "method",
    "text": "gen_index(O::NfOrd) -> fmpq\n\nReturns the generalized index of mathcal O with respect to the equation order of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.index-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.index",
    "category": "method",
    "text": "index(O::NfOrd) -> fmpz\n\nAssuming that the order mathcal O contains the equation order mathbf Zalpha of the ambient number field, this function returns the index  mathcal O  mathbf Z.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.isindex_divisor-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Basics",
    "title": "Hecke.isindex_divisor",
    "category": "method",
    "text": "isindex_divisor(O::NfOrd, d::fmpz) -> Bool\nisindex_divisor(O::NfOrd, d::Int) -> Bool\n\nReturns whether d is a divisor of the index of mathcal O. It is assumed that mathcal O contains the equation order of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.minkowski_mat-Tuple{NfAbsOrd{AnticNumberField,nf_elem},Int64}",
    "page": "Basics",
    "title": "Hecke.minkowski_mat",
    "category": "method",
    "text": "minkowski_mat(O::NfOrd, abs_tol::Int = 64) -> arb_mat\n\nReturns the Minkowski matrix of mathcal O.  Thus if mathcal O has degree d, then the result is a matrix in operatornameMat_dtimes d(mathbf R). The entries of the matrix are real balls of type arb with radius less then 2^-abs_tol.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.in-Tuple{nf_elem,NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.in",
    "category": "method",
    "text": "in(a::nf_elem, O::NfOrd) -> Bool\n\nChecks whether a lies in mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.denominator-Tuple{nf_elem,NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.denominator",
    "category": "method",
    "text": "denominator(a::nf_elem, O::NfOrd) -> fmpz\n\nReturns the smallest positive integer k such that k cdot a is contained in mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.norm_change_const-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.norm_change_const",
    "category": "method",
    "text": "norm_change_const(O::NfOrd) -> (Float64, Float64)\n\nReturns (c_1 c_2) in mathbf R_0^2 such that for all x = sum_i=1^d x_i omega_i in mathcal O we have T_2(x) leq c_1 cdot sum_i^d x_i^2 and sum_i^d x_i^2 leq c_2 cdot T_2(x), where (omega_i)_i is the mathbf Z-basis of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.trace_matrix-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.trace_matrix",
    "category": "method",
    "text": "trace_matrix(O::NfOrd) -> fmpz_mat\n\nReturns the trace matrix of \\mathcal O, that is, the matrix (operatornametr_Kmathbf Q(b_i cdot b_j))_1 leq i j leq d.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.:+-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.:+",
    "category": "method",
    "text": "+(R::NfOrd, S::NfOrd) -> NfOrd\n\nGiven two orders R, S of K, this function returns the smallest order containing both R and S. It is assumed that R, S contain the ambient equation order and have coprime index.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.poverorder-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Basics",
    "title": "Hecke.poverorder",
    "category": "method",
    "text": "poverorder(O::NfOrd, p::fmpz) -> NfOrd\npoverorder(O::NfOrd, p::Integer) -> NfOrd\n\nThis function tries to find an order that is locally larger than mathcal O at the prime p: If p divides the index  mathcal O_K  mathcal O, this function will return an order R such that v_p( mathcal O_K  R)  v_p( mathcal O_K  mathcal O). Otherwise mathcal O is returned.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.pmaximal_overorder-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Basics",
    "title": "Hecke.pmaximal_overorder",
    "category": "method",
    "text": "pmaximal_overorder(O::NfOrd, p::fmpz) -> NfOrd\npmaximal_overorder(O::NfOrd, p::Integer) -> NfOrd\n\nThis function finds a p-maximal order R containing mathcal O. That is, the index  mathcal O_K  R is not dividible by p.\n\n\n\n"
},

{
    "location": "orders/basics.html#Example-1",
    "page": "Basics",
    "title": "Example",
    "category": "section",
    "text": "using Hecke; # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nK, a = NumberField(x^2 - 2, \"a\");\nO = EquationOrder(K)parent(::NfOrd)\nisequation_order(::NfOrd)\nsignature(::NfOrd)\nnf(::NfOrd)\ndegree(::NfOrd)\nbasis(::NfOrd)\nbasis(::NfOrd, ::AnticNumberField)\nbasis_mat(::NfOrd)\nbasis_mat_inv(::NfOrd)\ndiscriminant(::NfOrd)\ngen_index(::NfOrd)\nindex(::NfOrd)\nisindex_divisor(::NfOrd, ::fmpz)\nminkowski_mat(::NfOrd, ::Int)\nin(::nf_elem, ::NfOrd)\ndenominator(::nf_elem, ::NfOrd)\nnorm_change_const(::NfOrd)\ntrace_matrix(::NfOrd)\n+(::NfOrd, ::NfOrd)\npoverorder(::NfOrd, ::fmpz)\npmaximal_overorder(::NfOrd, ::fmpz)"
},

{
    "location": "orders/basics.html#Elements-1",
    "page": "Basics",
    "title": "Elements",
    "category": "section",
    "text": ""
},

{
    "location": "orders/basics.html#Creation-1",
    "page": "Basics",
    "title": "Creation",
    "category": "section",
    "text": ""
},

{
    "location": "orders/basics.html#Base.parent-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.parent",
    "category": "method",
    "text": "\n\nparent(a::NfAbsOrdElem) -> NfOrd\n\nReturns the order of which a is an element.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.elem_in_nf-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.elem_in_nf",
    "category": "method",
    "text": "\n\nelem_in_nf(a::NfAbsOrdElem) -> nf_elem\n\nReturns the element a considered as an element of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.elem_in_basis-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.elem_in_basis",
    "category": "method",
    "text": "\n\nelem_in_basis(a::NfAbsOrdElem) -> Array{fmpz, 1}\n\nReturns the coefficient vector of a.\n\n\n\n\n\n  elem_in_basis(a::NfRelOrdElem{T}) -> Vector{T}\n\nReturns the coefficient vector of a.\n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.discriminant-Tuple{Array{NfAbsOrdElem{AnticNumberField,nf_elem},1}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.discriminant",
    "category": "method",
    "text": "\n\ndiscriminant(B::Array{NfAbsOrdElem, 1}) -> fmpz\n\nReturns the discriminant of the family B.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.:==-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.:==",
    "category": "method",
    "text": "\n\n==(x::NfAbsOrdElem, y::NfAbsOrdElem) -> Bool\n\nReturns whether x and y are equal.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.zero-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.zero",
    "category": "method",
    "text": "\n\nzero(O::NfOrd) -> NfAbsOrdElem\n\nReturns the zero element of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.one-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.one",
    "category": "method",
    "text": "\n\none(O::NfOrd) -> NfAbsOrdElem\n\nReturns the one element of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.iszero-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.iszero",
    "category": "method",
    "text": "\n\niszero(a::NfOrd) -> Bool\n\nTests if a is zero.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.isone-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.isone",
    "category": "method",
    "text": "\n\nisone(a::NfOrd) -> Bool\n\nTests if a is one.\n\n\n\n"
},

{
    "location": "orders/basics.html#Basic-properties-1",
    "page": "Basics",
    "title": "Basic properties",
    "category": "section",
    "text": "parent(::NfOrdElem)\nelem_in_nf(::NfOrdElem)\nelem_in_basis(::NfOrdElem)\ndiscriminant(::Array{NfOrdElem, 1})\n==(::NfOrdElem, ::NfOrdElem)\nzero(::NfOrd)\none(::NfOrd)\niszero(::NfOrdElem)\nisone(::NfOrdElem)"
},

{
    "location": "orders/basics.html#Base.:--Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.:-",
    "category": "method",
    "text": "\n\n-(x::NfAbsOrdElem) -> NfAbsOrdElem\n\nReturns the additive inverse of x.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.:+-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.:+",
    "category": "method",
    "text": "\n\n+(x::NfAbsOrdElem, y::NfAbsOrdElem) -> NfAbsOrdElem\n\nReturns x + y.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.:--Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.:-",
    "category": "method",
    "text": "\n\n-(x::NfAbsOrdElem, y::NfAbsOrdElem) -> NfAbsOrdElem\n\nReturns x - y.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.:*-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.:*",
    "category": "method",
    "text": "\n\n*(x::NfAbsOrdElem, y::NfAbsOrdElem) -> NfAbsOrdElem\n\nReturns x cdot y.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.:^-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Basics",
    "title": "Base.:^",
    "category": "method",
    "text": "\n\n^(x::NfAbsOrdElem, y::Union{fmpz, Int})\n\nReturns x^y.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.mod-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Basics",
    "title": "Base.mod",
    "category": "method",
    "text": "\n\nmod(a::NfAbsOrdElem, m::Union{fmpz, Int}) -> NfAbsOrdElem\n\nReduces the coefficient vector of a modulo m and returns the corresponding element. The coefficient vector of the result will have entries x with 0 leq x leq m.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.powermod-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},fmpz,Int64}",
    "page": "Basics",
    "title": "Base.powermod",
    "category": "method",
    "text": "\n\npowermod(a::NfAbsOrdElem, i::fmpz, m::Integer) -> NfAbsOrdElem\n\nReturns the element a^i modulo m.\n\n\n\n"
},

{
    "location": "orders/basics.html#Arithmetic-1",
    "page": "Basics",
    "title": "Arithmetic",
    "category": "section",
    "text": "-(::NfOrdElem)\n+(::NfOrdElem, ::NfOrdElem)\n-(::NfOrdElem, ::NfOrdElem)\n*(::NfOrdElem, ::NfOrdElem)\n^(::NfOrdElem, ::Int)\nmod(::NfOrdElem, ::Int)\npowermod(::NfOrdElem, ::fmpz, ::Int)"
},

{
    "location": "orders/basics.html#Nemo.representation_matrix-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Nemo.representation_matrix",
    "category": "method",
    "text": "\n\nrepresentation_matrix(a::NfAbsOrdElem) -> fmpz_mat\n\nReturns the representation matrix of the element a.\n\n\n\n\n\nrepresentation_matrix(a::NfAbsOrdElem, K::AnticNumberField) -> FakeFmpqMat\n\nReturns the representation matrix of the element a considered as an element of the ambient number field K. It is assumed that K is the ambient number field of the order of a.\n\n\n\n"
},

{
    "location": "orders/basics.html#Nemo.representation_matrix-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},AnticNumberField}",
    "page": "Basics",
    "title": "Nemo.representation_matrix",
    "category": "method",
    "text": "\n\nrepresentation_matrix(a::NfAbsOrdElem, K::AnticNumberField) -> FakeFmpqMat\n\nReturns the representation matrix of the element a considered as an element of the ambient number field K. It is assumed that K is the ambient number field of the order of a.\n\n\n\n"
},

{
    "location": "orders/basics.html#LinearAlgebra.tr-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "LinearAlgebra.tr",
    "category": "method",
    "text": "\n\ntr(a::NfAbsOrdElem) -> fmpz\n\nReturns the trace of a.\n\n\n\n"
},

{
    "location": "orders/basics.html#LinearAlgebra.norm-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "LinearAlgebra.norm",
    "category": "method",
    "text": "\n\nnorm(a::NfAbsOrdElem) -> fmpz\n\nReturns the norm of a.\n\n\n\n\n\nnorm(A::NfAbsOrdIdl) -> fmpz\n\nReturns the norm of A, that is, the cardinality of mathcal OA, where mathcal O is the order of A.\n\n\n\n\n\nnorm(a::NfRelOrdIdl) -> NfOrdIdl\n\nReturns the norm of a.\n\n\n\n\n\nnorm(a::NfRelOrdFracIdl{T, S}) -> S\n\nReturns the norm of a\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.rand-Tuple{NfAbsOrd{AnticNumberField,nf_elem},Int64}",
    "page": "Basics",
    "title": "Base.rand",
    "category": "method",
    "text": "\n\nrand(O::NfOrd, n::Union{Integer, fmpz}) -> NfAbsOrdElem\n\nComputes a coefficient vector with entries uniformly distributed in -ndotsc-101dotscn and returns the corresponding element of the order mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.minkowski_map-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Basics",
    "title": "Hecke.minkowski_map",
    "category": "method",
    "text": "\n\nminkowski_map(a::NfAbsOrdElem, abs_tol::Int) -> Array{arb, 1}\n\nReturns the image of a under the Minkowski embedding. Every entry of the array returned is of type arb with radius less then 2^-abs_tol.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.conjugates_arb-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Basics",
    "title": "Hecke.conjugates_arb",
    "category": "method",
    "text": "\n\nconjugates_arb(x::NfAbsOrdElem, abs_tol::Int) -> Array{acb, 1}\n\nCompute the the conjugates of x as elements of type acb. Recall that we order the complex conjugates sigma_r+1(x)sigma_r+2s(x) such that sigma_i(x) = overlinesigma_i + s(x) for r + 2 leq i leq r + s.Every entry y of the array returned satisfies radius(real(y)) < 2^-abs_tol, radius(imag(y)) < 2^-abs_tol respectively.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.conjugates_arb_log-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Basics",
    "title": "Hecke.conjugates_arb_log",
    "category": "method",
    "text": "\n\nconjugates_arb_log(x::NfAbsOrdElem, abs_tol::Int) -> Array{arb, 1}\n\nReturns the elements (log(lvert sigma_1(x) rvert)dotsclog(lvertsigma_r(x) rvert) dotsc2log(lvert sigma_r+1(x) rvert)dotsc 2log(lvert sigma_r+s(x)rvert)) as elements of type arb radius less then 2^-abs_tol.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.t2-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Basics",
    "title": "Hecke.t2",
    "category": "method",
    "text": "\n\nt2(x::NfAbsOrdElem, abs_tol::Int = 32) -> arb\n\nReturn the T_2-norm of x. The radius of the result will be less than 2^-abs_tol.\n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.minpoly-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.minpoly",
    "category": "method",
    "text": "minpoly(a::NfAbsOrdElem) -> fmpz_poly\n\nminpoly(a::NfAbsOrdElem, FlintZZ) -> fmpz_poly\n\nThe minimal polynomial of a.    \n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.charpoly-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.charpoly",
    "category": "method",
    "text": "charpoly(a::NfAbsOrdElem) -> fmpz_poly\n\ncharpoly(a::NfAbsOrdElem, FlintZZ) -> fmpz_poly\n\nThe characteristic polynomial of a.    \n\n\n\n"
},

{
    "location": "orders/basics.html#Miscallenous-1",
    "page": "Basics",
    "title": "Miscallenous",
    "category": "section",
    "text": "representation_matrix(::NfOrdElem)\nrepresentation_matrix(::NfOrdElem, ::AnticNumberField)\ntr(::NfOrdElem)\nnorm(::NfOrdElem)\nrand(::NfOrd, ::Int)\nminkowski_map(::NfOrdElem, ::Int)\nconjugates_arb(::NfOrdElem, ::Int)\nconjugates_arb_log(::NfOrdElem, ::Int)\nt2(::NfOrdElem, ::Int)\nminpoly(::NfOrdElem)\ncharpoly(::NfOrdElem)"
},

{
    "location": "orders/basics.html#Ideals-1",
    "page": "Basics",
    "title": "Ideals",
    "category": "section",
    "text": ""
},

{
    "location": "orders/basics.html#Hecke.ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Basics",
    "title": "Hecke.ideal",
    "category": "method",
    "text": "\n\nideal(O::NfOrd, a::fmpz) -> NfAbsOrdIdl\nideal(O::NfOrd, a::Integer) -> NfAbsOrdIdl\n\nReturns the ideal of mathcal O which is generated by a.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz_mat}",
    "page": "Basics",
    "title": "Hecke.ideal",
    "category": "method",
    "text": "\n\nideal(O::NfOrd, x::fmpz_mat, check::Bool = false, x_in_hnf::Bool = false) -> NfAbsOrdIdl\n\nCreates the ideal of mathcal O with basis matrix x. If check is set, then it is checked whether x defines an ideal (expensive). If xinhnf is set, then it is assumed that x is already in lower left HNF.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.ideal",
    "category": "method",
    "text": "\n\nideal(O::NfOrd, x::NfOrdElem) -> NfAbsOrdIdl\n\nCreates the principal ideal (x) of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz,NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.ideal",
    "category": "method",
    "text": "\n\nideal(O::NfOrd, x::fmpz, y::NfOrdElem) -> NfAbsOrdIdl\nideal(O::NfOrd, x::Integer, y::NfOrdElem) -> NfAbsOrdIdl\n\nCreates the ideal (xy) of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.:*-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.:*",
    "category": "method",
    "text": "*(O::NfOrd, x::NfOrdElem) -> NfAbsOrdIdl\n*(x::NfOrdElem, O::NfOrd) -> NfAbsOrdIdl\n\nReturns the principal ideal (x) of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.prime_decomposition-Tuple{NfAbsOrd{AnticNumberField,nf_elem},Integer}",
    "page": "Basics",
    "title": "Hecke.prime_decomposition",
    "category": "method",
    "text": "\n\nprime_decomposition(O::NfOrd,\n                    p::Integer,\n                    degree_limit::Int = 0,\n                    lower_limit::Int = 0) -> Array{Tuple{NfOrdIdl, Int}, 1}\n\nReturns an array of tuples (mathfrak p_ie_i) such that p mathcal O is the product of the mathfrak p_i^e_i and mathfrak p_i neq mathfrak p_j for i neq j.If degree_limit is a nonzero integer k  0, then only those prime ideals mathfrak p with deg(mathfrak p) leq k will be returned. Similarly if \\lower_limit is a nonzero integer l  0, then only those prime ideals mathfrak p with l leq deg(mathfrak p) will be returned. Note that in this case it may happen that pmathcal O is not the product of the mathfrak p_i^e_i.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.prime_decomposition-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Basics",
    "title": "Hecke.prime_decomposition",
    "category": "method",
    "text": "\n\nprime_decomposition(O::NfOrd,\n                    p::Integer,\n                    degree_limit::Int = 0,\n                    lower_limit::Int = 0) -> Array{Tuple{NfOrdIdl, Int}, 1}\n\nReturns an array of tuples (mathfrak p_ie_i) such that p mathcal O is the product of the mathfrak p_i^e_i and mathfrak p_i neq mathfrak p_j for i neq j.If degree_limit is a nonzero integer k  0, then only those prime ideals mathfrak p with deg(mathfrak p) leq k will be returned. Similarly if \\lower_limit is a nonzero integer l  0, then only those prime ideals mathfrak p with l leq deg(mathfrak p) will be returned. Note that in this case it may happen that pmathcal O is not the product of the mathfrak p_i^e_i.\n\n\n\n"
},

{
    "location": "orders/basics.html#Creation-2",
    "page": "Basics",
    "title": "Creation",
    "category": "section",
    "text": "ideal(::NfOrd, ::fmpz)\nideal(::NfOrd, ::fmpz_mat)\nideal(::NfOrd, ::NfOrdElem)\nideal(::NfOrd, ::fmpz, ::NfOrdElem)\n*(::NfOrd, ::NfOrdElem)\nprime_decomposition(::NfOrd, ::Integer)\nprime_decomposition(::NfOrd, ::fmpz)"
},

{
    "location": "orders/basics.html#Base.:==-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.:==",
    "category": "method",
    "text": "\n\n==(x::NfAbsOrdIdl, y::NfAbsOrdIdl)\n\nReturns whether x and y are equal.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.:+-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.:+",
    "category": "method",
    "text": "\n\n+(x::NfOrdIdl, y::NfOrdIdl)\n\nReturns x + y.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.:*-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.:*",
    "category": "method",
    "text": "*(x::NfOrdIdl, y::NfOrdIdl)\n\nReturns x cdot y.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.lcm-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.lcm",
    "category": "method",
    "text": "intersection(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl\nlcm(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl\n\nReturns x cap y.\n\n\n\n"
},

{
    "location": "orders/basics.html#Arithmetic-2",
    "page": "Basics",
    "title": "Arithmetic",
    "category": "section",
    "text": "==(::NfOrdIdl, ::NfOrdIdl)\n+(::NfOrdIdl, ::NfOrdIdl)\n*(::NfOrdIdl, ::NfOrdIdl)\nlcm(::NfOrdIdl, ::NfOrdIdl)"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.order-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.order",
    "category": "method",
    "text": "\n\norder(I::NfAbsOrdIdl) -> NfOrd\n\nReturns the order of I.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.basis-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.basis",
    "category": "method",
    "text": "basis(O::NfOrd) -> Array{NfOrdElem, 1}\n\nReturns the mathbf Z-basis of mathcal O.\n\n\n\n\n\nbasis(A::NfAbsOrdIdl) -> Array{NfOrdElem, 1}\n\nReturns the basis of A.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.basis_mat-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.basis_mat",
    "category": "method",
    "text": "basis_mat(O::NfOrd) -> FakeFmpqMat\n\nReturns the basis matrix of mathcal O with respect to the power basis of the ambient number field.\n\n\n\n\n\nbasismat(A::NfAbsOrdIdl) -> fmpzmat\n\nReturns the basis matrix of A.\n\n\n\n\n\n  basis_mat(O::NfRelOrd{T, S}) -> Generic.Mat{T}\n\nReturns the basis matrix of mathcal O with respect to the power basis of the ambient number field.\n\n\n\n\n\n  basis_mat(a::NfRelOrdIdl{T, S}) -> Generic.Mat{T}\n  basis_mat(a::NfRelOrdFracIdl{T, S}) -> Generic.Mat{T}\n\nReturns the basis matrix of a.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.basis_mat_inv-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.basis_mat_inv",
    "category": "method",
    "text": "basis_mat_inv(O::NfOrd) -> FakeFmpqMat\n\nReturns the inverse of the basis matrix of mathcal O.\n\n\n\n\n\nbasismatinv(A::NfAbsOrdIdl) -> fmpz_mat\n\nReturns the inverse basis matrix of A.\n\n\n\n\n\n  basis_mat_inv(O::NfRelOrd{T, S}) -> Generic.Mat{T}\n\nReturns the inverse of the basis matrix of mathcal O.\n\n\n\n\n\n  basis_mat_inv(a::NfRelOrdIdl{T, S}) -> Generic.Mat{T}\n  basis_mat_inv(a::NfRelOrdFracIdl{T, S}) -> Generic.Mat{T}\n\nReturns the inverse of the basis matrix of a.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.minimum-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.minimum",
    "category": "method",
    "text": "\n\nminimum(A::NfAbsOrdIdl) -> fmpz\n\nReturns the smallest nonnegative element in A cap mathbf Z.\n\n\n\n\n\n  minimum(A::NfRelOrdIdl) -> NfOrdIdl\n  minimum(A::NfRelOrdIdl) -> NfRelOrdIdl\n\nReturns the ideal A cap O where O is the maximal order of the coefficient ideals of A.\n\n\n\n"
},

{
    "location": "orders/basics.html#LinearAlgebra.norm-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "LinearAlgebra.norm",
    "category": "method",
    "text": "\n\nnorm(A::NfAbsOrdIdl) -> fmpz\n\nReturns the norm of A, that is, the cardinality of mathcal OA, where mathcal O is the order of A.\n\n\n\n\n\nnorm(a::NfRelOrdIdl) -> NfOrdIdl\n\nReturns the norm of a.\n\n\n\n\n\nnorm(a::NfRelOrdFracIdl{T, S}) -> S\n\nReturns the norm of a\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.in-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.in",
    "category": "method",
    "text": "\n\nin(x::NfOrdElem, y::NfAbsOrdIdl)\nin(x::nf_elem, y::NfAbsOrdIdl)\nin(x::fmpz, y::NfAbsOrdIdl)\n\nReturns whether x is contained in y.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.idempotents-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.idempotents",
    "category": "method",
    "text": "idempotents(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdElem, NfOrdElem\n\nReturns a tuple (e, f) consisting of elements e in x, f in y such that 1 = e + f.If the ideals are not coprime, an error is raised.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.mod-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Base.mod",
    "category": "method",
    "text": "\n\nmod(x::NfOrdElem, I::NfAbsOrdIdl)\n\nReturns the unique element y of the ambient order of x with x equiv y bmod I and the following property: If a_1dotsca_d in Z_geq 1 are the diagonal entries of the unique HNF basis matrix of I and (b_1dotscb_d) is the coefficient vector of y, then 0 leq b_i  a_i for 1 leq i leq d.\n\n\n\n"
},

{
    "location": "orders/basics.html#Nemo.isprime-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Nemo.isprime",
    "category": "method",
    "text": "\n\nisprime(A::NfOrdIdl) -> Bool\n\nReturns whether A is a prime ideal.\n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.valuation-Tuple{nf_elem,NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "\n\nvaluation(a::nf_elem, p::NfOrdIdl) -> fmpz\nvaluation(a::NfOrdElem, p::NfOrdIdl) -> fmpz\nvaluation(a::fmpz, p::NfOrdIdl) -> fmpz\n\nComputes the mathfrak p-adic valuation of a, that is, the largest i such that a is contained in mathfrak p^i.\n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.valuation-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "\n\nvaluation(a::nf_elem, p::NfOrdIdl) -> fmpz\nvaluation(a::NfOrdElem, p::NfOrdIdl) -> fmpz\nvaluation(a::fmpz, p::NfOrdIdl) -> fmpz\n\nComputes the mathfrak p-adic valuation of a, that is, the largest i such that a is contained in mathfrak p^i.\n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.valuation-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "\n\nvaluation(A::NfOrdIdl, p::NfOrdIdl) -> fmpz\n\nComputes the mathfrak p-adic valuation of A, that is, the largest i such that A is contained in mathfrak p^i.\n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.valuation-Tuple{Integer,NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "valuation(a::Integer, p::NfOrdIdl) -> fmpz\n\nComputes the mathfrak p-adic valuation of a, that is, the largest i such that a is contained in mathfrak p^i.\n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.valuation-Tuple{fmpz,NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "\n\nvaluation(a::nf_elem, p::NfOrdIdl) -> fmpz\nvaluation(a::NfOrdElem, p::NfOrdIdl) -> fmpz\nvaluation(a::fmpz, p::NfOrdIdl) -> fmpz\n\nComputes the mathfrak p-adic valuation of a, that is, the largest i such that a is contained in mathfrak p^i.\n\n\n\n"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.valuation-Tuple{Hecke.NfOrdFracIdl,NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "valuation(A::NfOrdFracIdl, p::NfOrdIdl)\n\nThe valuation of A at p.\n\n\n\n"
},

{
    "location": "orders/basics.html#Miscaellenous-1",
    "page": "Basics",
    "title": "Miscaellenous",
    "category": "section",
    "text": "order(::NfOrdIdl)\nbasis(::NfOrdIdl)\nbasis_mat(::NfOrdIdl)\nbasis_mat_inv(::NfOrdIdl)\nminimum(::NfOrdIdl)\nnorm(::NfOrdIdl)\nin(::NfOrdElem, ::NfOrdIdl)\nidempotents(::NfOrdIdl, ::NfOrdIdl)\nmod(::NfOrdElem, ::NfOrdIdl)\nisprime(::NfOrdIdl)\nvaluation(::nf_elem, ::NfOrdIdl)\nvaluation(::NfOrdElem, ::NfOrdIdl)\nvaluation(::NfOrdIdl, ::NfOrdIdl)\nvaluation(::Integer, ::NfOrdIdl)\nvaluation(::fmpz, ::NfOrdIdl)\nvaluation(::NfOrdFracIdl, ::NfOrdIdl)"
},

{
    "location": "orders/basics.html#Fractional-ideals-1",
    "page": "Basics",
    "title": "Fractional ideals",
    "category": "section",
    "text": ""
},

{
    "location": "orders/basics.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz_mat}",
    "page": "Basics",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, A::fmpz_mat, b::fmpz, A_in_hnf::Bool = false) -> NfOrdFracIdl\n\nCreates the fractional ideal of mathcal O with basis matrix Ab. If Ainhnf is set, then it is assumed that A is already in lower left HNF.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz_mat,fmpz}",
    "page": "Basics",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, A::fmpz_mat, b::fmpz, A_in_hnf::Bool = false) -> NfOrdFracIdl\n\nCreates the fractional ideal of mathcal O with basis matrix Ab. If Ainhnf is set, then it is assumed that A is already in lower left HNF.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},FakeFmpqMat}",
    "page": "Basics",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, A::FakeFmpqMat, A_in_hnf::Bool = false) -> NfOrdFracIdl\n\nCreates the fractional ideal of mathcal O with basis matrix A. If Ainhnf is set, then it is assumed that the numerator of A is already in lower left HNF.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, I::NfOrdIdl) -> NfOrdFracIdl\n\nTurns the ideal I into a fractional ideal of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem},fmpz}",
    "page": "Basics",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, I::NfOrdIdl, b::fmpz) -> NfOrdFracIdl\n\nCreates the fractional ideal Ib of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},nf_elem}",
    "page": "Basics",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, a::nf_elem) -> NfOrdFracIdl\n\nCreates the principal fractional ideal (a) of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Basics",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, a::NfOrdElem) -> NfOrdFracIdl\n\nCreates the principal fractional ideal (a) of mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Creation-3",
    "page": "Basics",
    "title": "Creation",
    "category": "section",
    "text": "frac_ideal(::NfOrd, ::fmpz_mat)\nfrac_ideal(::NfOrd, ::fmpz_mat, ::fmpz)\nfrac_ideal(::NfOrd, ::FakeFmpqMat)\nfrac_ideal(::NfOrd, ::NfOrdIdl)\nfrac_ideal(::NfOrd, ::NfOrdIdl, ::fmpz)\nfrac_ideal(::NfOrd, ::nf_elem)\nfrac_ideal(::NfOrd, ::NfOrdElem)"
},

{
    "location": "orders/basics.html#Base.:==-Tuple{Hecke.NfOrdFracIdl,Hecke.NfOrdFracIdl}",
    "page": "Basics",
    "title": "Base.:==",
    "category": "method",
    "text": "\n\n==(x::NfOrdFracIdl, y::NfOrdFracIdl) -> Bool\n\nReturns whether x and y are equal.\n\n\n\n"
},

{
    "location": "orders/basics.html#Base.inv-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Basics",
    "title": "Base.inv",
    "category": "method",
    "text": "\n\ninv(A::NfOrdFracIdl) -> NfOrdFracIdl\n\nReturns the fractional ideal B such that AB = mathcal O.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.integral_split-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Basics",
    "title": "Hecke.integral_split",
    "category": "method",
    "text": "\n\nintegral_split(A::NfOrdFracIdl) -> NfOrdIdl, NfOrdIdl\n\nComputes the unique coprime integral ideals N and D s.th. A = ND^-1\n\n\n\n"
},

{
    "location": "orders/basics.html#Arithmetic-3",
    "page": "Basics",
    "title": "Arithmetic",
    "category": "section",
    "text": "==(::NfOrdFracIdl, ::NfOrdFracIdl)\ninv(::NfOrdFracIdl)\nintegral_split(::NfOrdFracIdl)"
},

{
    "location": "orders/basics.html#AbstractAlgebra.Generic.order-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Basics",
    "title": "AbstractAlgebra.Generic.order",
    "category": "method",
    "text": "order(a::NfOrdFracIdl) -> NfOrd\n\nThe order that was used to define the ideal a.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.basis_mat-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Basics",
    "title": "Hecke.basis_mat",
    "category": "method",
    "text": "\n\nbasis_mat(I::NfOrdFracIdl) -> FakeFmpqMat\n\nReturns the basis matrix of I with respect to the basis of the order.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.basis_mat_inv-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Basics",
    "title": "Hecke.basis_mat_inv",
    "category": "method",
    "text": "\n\nbasis_mat_inv(I::NfOrdFracIdl) -> FakeFmpqMat\n\nReturns the inverse of the basis matrix of I.\n\n\n\n"
},

{
    "location": "orders/basics.html#Hecke.basis-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Basics",
    "title": "Hecke.basis",
    "category": "method",
    "text": "\n\nbasis(I::NfOrdFracIdl) -> Array{nf_elem, 1}\n\nReturns the mathbf Z-basis of I.\n\n\n\n"
},

{
    "location": "orders/basics.html#LinearAlgebra.norm-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Basics",
    "title": "LinearAlgebra.norm",
    "category": "method",
    "text": "\n\nnorm(I::NfOrdFracIdl) -> fmpq\n\nReturns the norm of I\n\n\n\n"
},

{
    "location": "orders/basics.html#Miscaellenous-2",
    "page": "Basics",
    "title": "Miscaellenous",
    "category": "section",
    "text": "order(::NfOrdFracIdl)\nbasis_mat(::NfOrdFracIdl)\nbasis_mat_inv(::NfOrdFracIdl)\nbasis(::NfOrdFracIdl)\nnorm(::NfOrdFracIdl)"
},

{
    "location": "orders/ideals.html#",
    "page": "Ideals",
    "title": "Ideals",
    "category": "page",
    "text": ""
},

{
    "location": "orders/ideals.html#Ideals-1",
    "page": "Ideals",
    "title": "Ideals",
    "category": "section",
    "text": ""
},

{
    "location": "MaximalOrders/Introduction.html#",
    "page": "Maximal Order",
    "title": "Maximal Order",
    "category": "page",
    "text": ""
},

{
    "location": "MaximalOrders/Introduction.html#Maximal-Order-1",
    "page": "Maximal Order",
    "title": "Maximal Order",
    "category": "section",
    "text": ""
},

{
    "location": "MaximalOrders/Introduction.html#Introduction-1",
    "page": "Maximal Order",
    "title": "Introduction",
    "category": "section",
    "text": "In Hecke, maximal orders (aka ring of integers), due to their special properties normal orders don\'t share, come with their own type NfMaximalOrder.  While the elements have type NfOrderElem, the ideals and fractional ideals have types NfMaximalOrderIdeal and NfMaximalOrderFracIdeal respectively.While theoretically a number field contains a unique maximal order (the set of all integral elements), for technical reasons in Hecke a number field admits multiple maximal orders, which are uniquely determined by the number field and a chosen integral basis.Let K be a number field of degree d with primitive element alpha and mathcal O a maximal order K with mathbfZ-basis (omega_1dotscomega_d). The basis matrix of mathcal O is the unique matrix M_mathcal O in operatornameMat_d times d(mathbfQ) such that \\begin{align} \\begin{pmatrix} \\omega1 \\\\ \\omega2 \\\\ \\vdots \\\\ \\omegad \\end{pmatrix} = M{\\mathcal O} \\begin{pmatrix} 1 \\\\ \\alpha \\\\ \\vdots \\\\ \\alpha^{d - 1} \\end{pmatrix}. \\end{align} If beta is an element of mathcal O, we call the unique integers (x_1dotscx_d) in mathbf Z^d with \\begin{align} \\beta = \\sum{i=1}^d xi \\omega_i \\end{align} the coefficients of beta with respect to mathcal O or just the coefficient vector.For an ideal I of mathcal O, a basis matrix of I is a matrix M in operatornameMat_d times d(mathbfZ), such that the elements (alpha_1dotscalpha_d) definied by \\begin{align} \\begin{pmatrix} \\alpha1 \\\\ \\alpha2 \\\\ \\vdots \\\\ \\alphad \\end{pmatrix} = M{\\mathcal O} \\begin{pmatrix} \\omega1 \\\\ \\omega2 \\\\ \\vdots \\\\ \\omega_d \\end{pmatrix} \\end{align} form a mathbfZ-basis of I."
},

{
    "location": "MaximalOrders/Creation.html#",
    "page": "Orders",
    "title": "Orders",
    "category": "page",
    "text": "@module{Hecke}"
},

{
    "location": "MaximalOrders/Creation.html#Orders-1",
    "page": "Orders",
    "title": "Orders",
    "category": "section",
    "text": ""
},

{
    "location": "MaximalOrders/Creation.html#Creation-1",
    "page": "Orders",
    "title": "Creation",
    "category": "section",
    "text": "@{MaximalOrder(::AnticNumberField)} @{MaximalOrder(::AnticNumberField, ::Array{fmpz, 1})}"
},

{
    "location": "MaximalOrders/Creation.html#Basic-invariants-1",
    "page": "Orders",
    "title": "Basic invariants",
    "category": "section",
    "text": "@{nf(::NfMaximalOrder)} @{degree(::NfMaximalOrder)} @{basis(::NfMaximalOrder)} @{basis(::NfMaximalOrder, ::AnticNumberField)} @{basismat(::NfMaximalOrder)} @{basismatinv(::NfMaximalOrder)} @{index(::NfMaximalOrder)} @{signature(::NfMaximalOrder)} @{isindexdivisor(::NfMaximalOrder, ::fmpz)} @{minkowski_mat(::NfMaximalOrder, ::Int)}"
},

{
    "location": "MaximalOrders/Elements.html#",
    "page": "Elements",
    "title": "Elements",
    "category": "page",
    "text": "@module{Hecke}"
},

{
    "location": "MaximalOrders/Elements.html#Elements-1",
    "page": "Elements",
    "title": "Elements",
    "category": "section",
    "text": ""
},

{
    "location": "MaximalOrders/Elements.html#Creation-1",
    "page": "Elements",
    "title": "Creation",
    "category": "section",
    "text": "@{call(::NfMaximalOrder, ::nfelem, ::Bool)} @{call(::NfMaximalOrder, ::fmpz)} @{call(::NfMaximalOrder, ::Array{fmpz, 1})} @{call(::NfMaximalOrder, ::Array{Int, 1})} @{call(::NfMaximalOrder, ::nfelem, ::Array{fmpz, 1})} @{call(::NfMaximalOrder)} @{zero(::NfMaximalOrder)} @{one(::NfMaximalOrder)}"
},

{
    "location": "MaximalOrders/Elements.html#Basic-invariants-1",
    "page": "Elements",
    "title": "Basic invariants",
    "category": "section",
    "text": "@{parent(::NfOrderElem)} @{eleminnf(::NfOrderElem)} @{eleminbasis(::NfOrderElem)} @{==(::NfOrderElem, ::NfOrderElem)} @{deepcopy(::NfOrderElem)} @{in(::nfelem, ::NfMaximalOrder)} @{denominator(::nfelem, ::NfMaximalOrder)}"
},

{
    "location": "MaximalOrders/Elements.html#Binary-and-unary-operations-1",
    "page": "Elements",
    "title": "Binary and unary operations",
    "category": "section",
    "text": "@{-(::NfOrderElem)} @{(::NfOrderElem, ::NfOrderElem)} @{+(::NfOrderElem, ::NfOrderElem)} @{-(::NfOrderElem, ::NfOrderElem)} @{(::NfOrderElem, ::fmpz)} @{+(::NfOrderElem, ::fmpz)} @{-(::NfOrderElem, ::fmpz)} @{^(::NfOrderElem, ::Int)} @{mod(::NfOrderElem, ::Int)} @{powermod(::NfOrderElem, ::Int, ::fmpz)}"
},

{
    "location": "MaximalOrders/Elements.html#Representation-matrices-1",
    "page": "Elements",
    "title": "Representation matrices",
    "category": "section",
    "text": "@{representationmatrix(::NfOrderElem)} @{representationmatrix(::NfOrderElem, ::AnticNumberField)}"
},

{
    "location": "MaximalOrders/Elements.html#Trace-and-norm-1",
    "page": "Elements",
    "title": "Trace and norm",
    "category": "section",
    "text": "@{tr(::NfOrderElem)} @{norm(::NfOrderElem)}"
},

{
    "location": "MaximalOrders/Elements.html#Random-elements-1",
    "page": "Elements",
    "title": "Random elements",
    "category": "section",
    "text": "@{rand(::NfMaximalOrder, ::UnitRange{Int})} @{rand(::NfMaximalOrder, ::Int)}"
},

{
    "location": "MaximalOrders/Elements.html#Conjugates-1",
    "page": "Elements",
    "title": "Conjugates",
    "category": "section",
    "text": "@{conjugatesarb(::NfOrderElem, ::Int)} @{minkowskimap(::NfOrderElem, ::Int)} @{conjugates_log(::NfOrderElem)}"
},

{
    "location": "MaximalOrders/Ideals.html#",
    "page": "Ideals",
    "title": "Ideals",
    "category": "page",
    "text": ""
},

{
    "location": "MaximalOrders/Ideals.html#Ideals-1",
    "page": "Ideals",
    "title": "Ideals",
    "category": "section",
    "text": "@module{Hecke}@{nf(::NfMaximalOrderIdeal)}"
},

{
    "location": "abelian/introduction.html#",
    "page": "Abelian Groups",
    "title": "Abelian Groups",
    "category": "page",
    "text": ""
},

{
    "location": "abelian/introduction.html#Abelian-Groups-1",
    "page": "Abelian Groups",
    "title": "Abelian Groups",
    "category": "section",
    "text": ""
},

{
    "location": "abelian/introduction.html#Introduction-1",
    "page": "Abelian Groups",
    "title": "Introduction",
    "category": "section",
    "text": ""
},

{
    "location": "class_fields/intro.html#",
    "page": "Class Field Theory",
    "title": "Class Field Theory",
    "category": "page",
    "text": ""
},

{
    "location": "class_fields/intro.html#Class-Field-Theory-1",
    "page": "Class Field Theory",
    "title": "Class Field Theory",
    "category": "section",
    "text": "CurrentModule = Hecke"
},

{
    "location": "class_fields/intro.html#Introduction-1",
    "page": "Class Field Theory",
    "title": "Introduction",
    "category": "section",
    "text": "This chapter deals with abelian extensions of number fields and the rational numbers.Class Field Theory, here specifically, class field theory of global number fields, deals with abelian extension, ie. fields where the group of automorphisms is abelian. For extensions of {\\Q}, the famous Kronnecker-Weber theorem classifies all such fields: a field is abelian if and only if it is contained in some cyclotomic field. For general number fields this is more involved and even for extensions of {\\Q} is is not practical.In Hecke, abelian extensions are parametrized by quotients of so called ray class groups. The language of ray class groups while dated is more applicable to algorithms than the modern language of idel class groups and quotients."
},

{
    "location": "class_fields/intro.html#Hecke.ray_class_group-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},Array{InfPlc,1}}",
    "page": "Class Field Theory",
    "title": "Hecke.ray_class_group",
    "category": "method",
    "text": "ray_class_group(m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; p_part,n_quo)\n\nGiven a modulus with finite part m and infinite part inf_plc, it returns the Ray Class Group Cl_m. If p_part is given, the function will return the  largest quotient of the Ray Class Group of p-power order. If n_quo is given,  it will return the quotient of the Ray Class Group by n\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.class_group-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Class Field Theory",
    "title": "Hecke.class_group",
    "category": "method",
    "text": "\n\nclass_group(O::NfOrd; bound = -1, method = 3, redo = false, large = 1000) -> GrpAbFinGen, Map\n\nReturns a group A and a map f from A to the set of ideals of O. The inverse of the map is the projection onto the group of ideals modulo the  group of principal ideals. \\texttt{redo} allows to trigger a re-computation, thus avoiding the cache. \\texttt{bound}, when given, is the bound for the factor base.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.class_group-Tuple{AnticNumberField}",
    "page": "Class Field Theory",
    "title": "Hecke.class_group",
    "category": "method",
    "text": "class_group(K::AnticNumberField) -> GrpAbFinGen, Map\n\nShortcut for {{{classgroup(maximalorder(K))}}}: returns the class group as an abelian group and a map from this group to the set of ideals of the maximal order.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.norm_group-Tuple{PolyElem,Hecke.MapRayClassGrp,Bool}",
    "page": "Class Field Theory",
    "title": "Hecke.norm_group",
    "category": "method",
    "text": "norm_group(f::Nemo.PolyElem, mR::Hecke.MapRayClassGrp, isabelian::Bool = true; of_closure::Bool = false) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap\n\nnorm_group(f::Array{PolyElem{nf_elem}, mR::Hecke.MapRayClassGrp, isabelian::Bool = true; of_closure::Bool = false) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap\n\nComputes the subgroup of the Ray Class Group R given by the norm of the extension generated by a/the roots of f. If {{{isabelian}}} is set to true, then the code assumes the field to be abelian, hence the algorithm stops when the quotient by the norm group has the correct order. Even though the algorithm is probabilistic by nature, in this case the result is guaranteed. If {{{of_closure}}} is given, then the norm group of the splitting field of the polynomial(s) is computed. It is the callers responsibility to ensure that the ray class group passed in is large enough.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.norm_group-Tuple{Hecke.NfRel{nf_elem},Hecke.MapRayClassGrp,Bool}",
    "page": "Class Field Theory",
    "title": "Hecke.norm_group",
    "category": "method",
    "text": "norm_group(K::NfRel{nf_elem}, mR::Hecke.MapRayClassGrp) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap\n\nnorm_group(K::NfRel_ns{nf_elem}, mR::Hecke.MapRayClassGrp) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap\n\nComputes the subgroup of the Ray Class Group R given by the norm of the extension.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Ray-Class-Groups-1",
    "page": "Class Field Theory",
    "title": "Ray Class Groups",
    "category": "section",
    "text": "Given an integral ideal m_0 le Z_K and a list of real places m_infty, the ray class group modulo (m_0 m_infty), C(m) is defined as the group of ideals coprime to m_0 modulo the elements ain K^* s.th. v_p(a-1) ge v_p(m_0) and for all vin m_infty, a^(v) 0. This is a finite abelian group. For m_0 = Z_K and m_infty =  we get C() is the class group, if m_infty contains all real places, we obtain the narrow class group, or strict class group.ray_class_group(m::Hecke.NfAbsOrdIdl{Nemo.AnticNumberField,Nemo.nf_elem}, inf_plc::Array{Hecke.InfPlc,1}; p_part, n_quo)\nclass_group(O::Hecke.NfAbsOrd{Nemo.AnticNumberField,Nemo.nf_elem}; bound, method, redo, unit_method, large)\nclass_group(K::Nemo.AnticNumberField)\nnorm_group(f::Nemo.PolyElem, mR::Hecke.MapRayClassGrp, isabelian::Bool)\nnorm_group(K::NfRel{nf_elem}, mR::Hecke.MapRayClassGrp, isabelian::Bool)"
},

{
    "location": "class_fields/intro.html#Hecke.ray_class_field-Tuple{Union{MapClassGrp, MapRayClassGrp}}",
    "page": "Class Field Theory",
    "title": "Hecke.ray_class_field",
    "category": "method",
    "text": "ray_class_field(m::MapClassGrp) -> ClassField\nray_class_field(m::MapRayClassGrp) -> ClassField\n\nCreates the (formal) abelian extension defined by the map m A to I where I is the set of ideals coprime to the modulus defining m and A  is a quotient of the ray class group (or class group). The map m must be the map returned from a call to {classgroup} or {rayclass_group}.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.ray_class_field-Tuple{Union{MapClassGrp, MapRayClassGrp},GrpAbFinGenMap}",
    "page": "Class Field Theory",
    "title": "Hecke.ray_class_field",
    "category": "method",
    "text": "ray_class_field(m::Union{MapClassGrp, MapRayClassGrp}, quomap::GrpAbFinGenMap) -> ClassField\n\nFor m a map computed by either {rayclassgroup} or {class_group} and q a canonical projection (quotient map) as returned by {quo} for q  quotient of the domain of m and a subgroup of m, create the (formal) abelian extension where the (relative) automorphism group is canonically isomorphic to the codomain of q.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.ray_class_field-Tuple{NfAbsOrdIdl}",
    "page": "Class Field Theory",
    "title": "Hecke.ray_class_field",
    "category": "method",
    "text": "ray_class_field(I::NfAbsOrdIdl; n_quo = 0) -> ClassField\n\nThe ray class field modulo I. If {{{n_quo}}} is given, then the largest subfield of exponent n is computed.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.hilbert_class_field-Tuple{AnticNumberField}",
    "page": "Class Field Theory",
    "title": "Hecke.hilbert_class_field",
    "category": "method",
    "text": "hilbert_class_field(k::AnticNumberField) -> ClassField\n\nThe Hilbert class field of k as a formal (ray-) class field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Ray-Class-Fields-1",
    "page": "Class Field Theory",
    "title": "Ray Class Fields",
    "category": "section",
    "text": "In general, the construction of a class field starts with a (ray) class group. Each quotient of a ray class group then defines a ray class field, the defining property is that the (relative) automorphism group is canonically isomorphic to the quotient of the ray class group where the isomorphism is given by the Artin (or Frobenius) map. Since, in Hecke, the (ray) class groups have no link to the field, actually this has to be specified using the maps.It should be noted that this is a {\\em lazy} construction: nothing is computed at this point.ray_class_field(m::Union{Hecke.MapClassGrp, Hecke.MapRayClassGrp})\nray_class_field(m::Union{Hecke.MapClassGrp, Hecke.MapRayClassGrp}, quomap::Hecke.GrpAbFinGenMap)\nray_class_field(I::Hecke.NfAbsOrdIdl; n_quo, p_part)\nhilbert_class_field(k::AnticNumberField)"
},

{
    "location": "class_fields/intro.html#Example-1",
    "page": "Class Field Theory",
    "title": "Example",
    "category": "section",
    "text": "using Hecke # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nK, a = NumberField(x^2 - 10, \"a\");\nc, mc = class_group(K)\nA = ray_class_field(mc)"
},

{
    "location": "class_fields/intro.html#Hecke.number_field-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.number_field",
    "category": "method",
    "text": "NumberField(f::Generic.Poly{T}, s::String; cached::Bool = false, check::Bool = false) where T\n\nGiven an irreducible polynomial f over some number field K, create the field Ktf. f must be irreducible - although this is not tested.\n\n\n\nNumberField(f::Generic.Poly{T}; cached::Bool = false, check::Bool = false) where T\n\nGiven an irreducible polynomial f over some number field K, create the field Ktf. f must be irreducible - although this is not tested.\n\n\n\nnumber_field(f::Array{Generic.Poly{T}, 1}, s::String=\"_\\$\") where T -> NfRel_ns\n\nGiven polynomials f = (f_1 ldots f_n) over some number field k, construct K = kt_1 ldots t_nlangle f_1(t_1) ldots f_n(t_n)rangle The ideal in the quotient must be maximal - although this is not tested.\n\n\n\nNumberField(CF::ClassField) -> Hecke.NfRel_ns{Nemo.nf_elem}\n\nGiven a (formal) abelian extension, compute the class field by finding defining polynomials for all prime power cyclic subfields. Note, by type this is always a non-simple extension.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.ray_class_field-Tuple{Hecke.NfRel{nf_elem}}",
    "page": "Class Field Theory",
    "title": "Hecke.ray_class_field",
    "category": "method",
    "text": "ray_class_field(K::NfRel{nf_elem}) -> ClassField\n\nFor a (relative) abelian extension, compute an abstract representation as a class field. \n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.genus_field-Tuple{Hecke.ClassField,AnticNumberField}",
    "page": "Class Field Theory",
    "title": "Hecke.genus_field",
    "category": "method",
    "text": "genus_field(A::ClassField, k::AnticNumberField) -> ClassField\n\nThe maximal extension contained in A that is the compositum of K with an abelian extension of k.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.maximal_abelian_subfield-Tuple{Hecke.ClassField,AnticNumberField}",
    "page": "Class Field Theory",
    "title": "Hecke.maximal_abelian_subfield",
    "category": "method",
    "text": "maximal_abelian_subfield(A::ClassField, k::AnticNumberField) -> ClassField\n\nThe maximal abelian extension of k contained in A. k must be a subfield of the base field of A.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.maximal_abelian_subfield-Tuple{Hecke.NfRel{nf_elem}}",
    "page": "Class Field Theory",
    "title": "Hecke.maximal_abelian_subfield",
    "category": "method",
    "text": "maximal_abelian_subfield(K::NfRel{nf_elem}; of_closure::Bool = false) -> ClassField\n\nUsing a probabilistic algorithm for the norm group computation, determine tha maximal abelian subfield in K over its base field. If {{{of_closure}}} is set to true, then the algorithm is applied to the normal closure if K (without computing it).\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Conversions-1",
    "page": "Class Field Theory",
    "title": "Conversions",
    "category": "section",
    "text": "Given a ray class field, it is possible to actually compute defining equation(s) for this field. In general, the number field constructed this way will be non-simple by type and is defined by a polynomial for each maximal cyclic quotient of prime power order in the defining group.The algorithm employed is based on Kummer-theory and requires the addition of a suitable root of unity. Progress can be monitored by setting {{{setverboselevel(:ClassField, n)}}} where 0le nle 3number_field(C::ClassField)using Hecke; # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nk, a = NumberField(x^2 - 10, \"a\");\nc, mc = class_group(k);\nA = ray_class_field(mc)\nK = number_field(A)\nZK = maximal_order(K)\nisone(discriminant(ZK))ray_class_field(K::NfRel{nf_elem})\ngenus_field(A::ClassField, k::AnticNumberField)\nmaximal_abelian_subfield(A::ClassField, k::AnticNumberField)\nmaximal_abelian_subfield(K::NfRel{nf_elem})"
},

{
    "location": "class_fields/intro.html#AbstractAlgebra.Generic.degree-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "AbstractAlgebra.Generic.degree",
    "category": "method",
    "text": "degree(A::ClassField)\n\nThe degree of A over its base field, ie. the size of the defining ideal group.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#AbstractAlgebra.Generic.base_ring-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "AbstractAlgebra.Generic.base_ring",
    "category": "method",
    "text": "base_ring(A::ClassField)\n\nThe maximal order of the field that A is defined over.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.base_field-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.base_field",
    "category": "method",
    "text": "base_field(A::ClassField)\n\nThe number field that A is defined over.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#AbstractAlgebra.Generic.discriminant-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "AbstractAlgebra.Generic.discriminant",
    "category": "method",
    "text": "discriminant(C::ClassField) -> NfOrdIdl\n\nUsing the conductor-discriminant formula, compute the (relative) discriminant of C. This does not use the defining equations.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.conductor-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.conductor",
    "category": "method",
    "text": "\n\nconductor(C::Hecke.ClassField) -> NfOrdIdl, Array{InfPlc,1}\n\nReturn the conductor of the abelian extension corresponding to C\n\n\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.defining_modulus-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.defining_modulus",
    "category": "method",
    "text": "defining_modulus(CF::ClassField)\n\nThe modulus, ie. an ideal the the set of real places, used to create the class field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.iscyclic-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.iscyclic",
    "category": "method",
    "text": "iscyclic(C::ClassField)\n\nTests if the (relative) automorphism group of C is cyclic (by checking the defining ideal group).\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.isconductor-Tuple{Hecke.ClassField,NfAbsOrdIdl{AnticNumberField,nf_elem},Array{InfPlc,1}}",
    "page": "Class Field Theory",
    "title": "Hecke.isconductor",
    "category": "method",
    "text": "\n\nisconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; check) -> NfOrdIdl, Array{InfPlc,1}\n\nChecks if m, inf_plc is the conductor of the abelian extension corresponding to C. If check is false, it assumes that the  given modulus is a multiple of the conductor. This is generically faster than computing the conductor.\n\n\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.isnormal-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.isnormal",
    "category": "method",
    "text": "isnormal(C::ClassField) -> Bool\n\nFor a class field C defined over a normal base field k, decide if C is normal over Q.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.iscentral-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.iscentral",
    "category": "method",
    "text": "iscentral(C::ClassField) -> Bool\n\nFor a class field C defined over a normal base field k, decide if C is central over Q.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Invariants-1",
    "page": "Class Field Theory",
    "title": "Invariants",
    "category": "section",
    "text": "degree(C::ClassField)\nbase_ring(A::Hecke.ClassField) \nbase_field(A::Hecke.ClassField) \ndiscriminant(C::Hecke.ClassField)\nconductor(C::Hecke.ClassField) \ndefining_modulus(C::ClassField)\niscyclic(C::ClassField)\nisconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Array{InfPlc,1})\nisnormal(C::ClassField)\niscentral(C::ClassField)"
},

{
    "location": "class_fields/intro.html#Base.:*-Tuple{Hecke.ClassField,Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Base.:*",
    "category": "method",
    "text": "*(A::ClassField, B::ClassField) -> ClassField\n\nThe compositum of a and b as a (formal) class field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.compositum-Tuple{Hecke.ClassField,Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.compositum",
    "category": "method",
    "text": "compositum(a::ClassField, b::ClassField) -> ClassField\n         *(a::ClassField, b::ClassField) -> ClassField\n\nThe compositum of a and b as a (formal) class field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Base.:==-Tuple{Hecke.ClassField,Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Base.:==",
    "category": "method",
    "text": "==(a::ClassField, b::ClassField)\n\nTests if a and b are equal.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Base.intersect-Tuple{Hecke.ClassField,Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Base.intersect",
    "category": "method",
    "text": "intersect(a::ClassField, b::ClassField) -> ClassField\n\nThe intersection of a and b as a class field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.prime_decomposition_type-Tuple{Hecke.ClassField,NfAbsOrdIdl}",
    "page": "Class Field Theory",
    "title": "Hecke.prime_decomposition_type",
    "category": "method",
    "text": "prime_decomposition_type(C::ClassField, p::NfAbsOrdIdl) -> (Int, Int, Int)\n\nFor a prime p in the base ring of r, determine the splitting type of p  in r. ie. the tuple (e f g) giving the ramification degree, the inertia and the number of primes above p.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.issubfield-Tuple{Hecke.ClassField,Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.issubfield",
    "category": "method",
    "text": "issubfield(a::ClassField, b::ClassField) -> Bool\n\nDetermines of a is a subfield of b.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.islocal_norm-Tuple{Hecke.ClassField,NfAbsOrdElem}",
    "page": "Class Field Theory",
    "title": "Hecke.islocal_norm",
    "category": "method",
    "text": "islocal_norm(r::ClassField, a::NfAbsOrdElem) -> Bool\n\nTests if a is a local norm at all finite places in the extension implictly given by r.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.islocal_norm-Tuple{Hecke.ClassField,NfAbsOrdElem,NfAbsOrdIdl}",
    "page": "Class Field Theory",
    "title": "Hecke.islocal_norm",
    "category": "method",
    "text": "islocal_norm(r::ClassField, a::NfAbsOrdElem, p::NfAbsOrdIdl) -> Bool\n\nTests if a is a local norm at p in the extension implictly given by r. Currently the conductor cannot have infinite places.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.normal_closure-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.normal_closure",
    "category": "method",
    "text": "normal_closure(C::ClassField) -> ClassField\n\nFor a ray class field C extending a normal base field k, compute the normal closure over Q.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.subfields-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.subfields",
    "category": "method",
    "text": "subfields(C::ClassField) -> Array{ClassField, 1}\n\nFind all subfields of C as class fields.     Note: this will not find all subfields over Q, but only the ones sharing the same base field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.subfields-Tuple{Hecke.ClassField,Int64}",
    "page": "Class Field Theory",
    "title": "Hecke.subfields",
    "category": "method",
    "text": "subfields(C::ClassField, d::Int) -> Array{ClassField, 1}\n\nFind all subfields of C of degree d as class fields.     Note: this will not find all subfields over Q, but only the ones sharing the same base field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Operations-1",
    "page": "Class Field Theory",
    "title": "Operations",
    "category": "section",
    "text": "*(a::Hecke.ClassField, b::Hecke.ClassField)\ncompositum(a::Hecke.ClassField, b::Hecke.ClassField)\n==(a::Hecke.ClassField, b::Hecke.ClassField)\nintersect(a::Hecke.ClassField, b::Hecke.ClassField)\nprime_decomposition_type(C::Hecke.ClassField, p::Hecke.NfAbsOrdIdl)\nHecke.issubfield(a::ClassField, b::ClassField)\nHecke.islocal_norm(r::Hecke.ClassField, a::Hecke.NfAbsOrdElem)\nHecke.islocal_norm(r::Hecke.ClassField, a::Hecke.NfAbsOrdElem, p::Hecke.NfAbsOrdIdl)\nHecke.normal_closure(r::Hecke.ClassField) \nsubfields(r::ClassField)\nsubfields(r::ClassField, d::Int)"
},

]}
