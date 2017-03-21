174,1
V,GalRep,3
T,GalRep,-,0
A,GalRep,18,K,P,p,q,co,F,f,r,G,I,ramgps,Frob,act,dimcomputed,conductor,eulerfactor,inertia,epsilon
S,Print,Print a Galois representation,0,2,0,0,1,0,0,0,0,298,,0,0,GalRep,,-38,-38,-38,-38,-38,-38
S,IsCoercible,Coerce a Galois representation,0,2,0,0,0,0,0,0,0,-1,,0,0,GalRep,,36,-1,-38,-38,-38,-38
S,in,"""in"" function for an Galois representation",0,2,0,0,0,0,0,0,0,-1,,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,SP,Galois representation SP(n) over a p-adic field K,0,2,0,0,0,0,0,0,0,148,,0,0,400,,GalRep,-38,-38,-38,-38,-38
S,ZeroRepresentation,Galois representation 0 over a p-adic field K,0,1,0,0,0,0,0,0,0,400,,GalRep,-38,-38,-38,-38,-38
S,SP,"Unramified twist U*SP(n) over a p-adic field K, with U specified by its Euler factor f",0,3,0,0,0,0,0,0,0,148,,0,0,312,,0,0,400,,GalRep,-38,-38,-38,-38,-38
S,UnramifiedRepresentation,Unique unramified Galois representation rho over K with Euler factor  det(1-Frob^-1|rho)=CharPoly,0,2,0,0,0,0,0,0,0,312,,0,0,400,,GalRep,-38,-38,-38,-38,-38
S,UnramifiedRepresentation,"Unramified Galois representation rho over K of dimension dim, with Euler factor  CharPoly computed up to and inclusive degree dimcomputed",0,4,0,0,0,0,0,0,0,312,,0,0,148,,0,0,148,,0,0,400,,GalRep,-38,-38,-38,-38,-38
S,UnramifiedCharacter,"Unique unramified character that sends a Frobenius element to c^(-1),  as a Galois representation over K. The parameter c must be a non-zero  complex number",0,2,0,0,0,0,0,0,0,-1,,0,0,400,,GalRep,-38,-38,-38,-38,-38
S,PrincipalCharacter,"Principal character of the absolute Galois group of K, as a Galois representation",0,1,0,0,0,0,0,0,0,400,,GalRep,-38,-38,-38,-38,-38
S,CyclotomicCharacter,"Cyclotomic character over K (trivial on inertia, q on Frobenius)",0,1,0,0,0,0,0,0,0,400,,GalRep,-38,-38,-38,-38,-38
S,TateTwist,Tate twist A(n) of a Galois representation,0,2,0,0,0,0,0,0,0,148,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,Factorization,"Returns the list of tuples <chi_i,n_i,rho_i>, where A is the direct sum over i of twists by SP(n_i) by unramified representations with characteristic polynomial of  Frobenius chi_i, and a finite Weil representation given by a character rho_i of Group(A)",0,1,0,0,0,0,0,0,0,GalRep,,168,GalRep,-38,-38,-38,-38
S,IsSemisimple,true if a Galois representation A is semisimple,0,1,0,0,0,0,0,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,Semisimplification,Semisimplification of a Galois representation A,0,1,0,0,0,0,0,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,GaloisRepresentations,"For a polynomial f over a p-adic field K and splitting field F, returns irreducible representations of Gal(F/K)",1,0,1,312,0,400,1,0,0,0,0,0,0,0,312,,82,-38,-38,-38,-38,-38
S,PermutationCharacter,"For a p-adic extension F/K, compute C[Gal(Kbar/K)/Gal(Kbar/F)] as a Galois representation over K of degree [F:K]",0,2,0,0,0,0,0,0,0,400,,0,0,400,,GalRep,-38,-38,-38,-38,-38
S,GaloisRepresentations,"For a p-adic extension F/K, compute all irreducible Galois representations that factor through the (Galois closure of) F/K",0,2,0,0,0,0,0,0,0,400,,0,0,400,,82,-38,-38,-38,-38,-38
S,Precision,Precision of the base field of a Galois representation,0,1,0,0,0,0,0,0,0,GalRep,,148,-38,-38,-38,-38,-38
S,Group,"Finite Galois group Gal(F/K) that computes the finite part of a Galois representation; F=Field(A), K=BaseField(A)",0,1,0,0,0,0,0,0,0,GalRep,,224,-38,-38,-38,-38,-38
S,GaloisGroup,"Finite Galois group Gal(F/K) that computes the finite part of a Galois representation; F=Field(A), K=BaseField(A)",0,1,0,0,0,0,0,0,0,GalRep,,224,-38,-38,-38,-38,-38
S,BaseField,Base field of the Galois representation,0,1,0,0,0,0,0,0,0,GalRep,,400,-38,-38,-38,-38,-38
S,Field,p-adic field F such that the finite part of A factors through Gal(F/K),0,1,0,0,0,0,0,0,0,GalRep,,400,-38,-38,-38,-38,-38
S,Automorphism,The automorphism of Field(A)/BaseField(A) given by g,0,2,0,0,0,0,0,0,0,222,,0,0,GalRep,,175,-38,-38,-38,-38,-38
S,FrobeniusElement,Frobenius element of Group(A) for a Galois representation A,0,1,0,0,0,0,0,0,0,GalRep,,222,-38,-38,-38,-38,-38
S,InertiaGroup,Inertia subgroup of the finite part of a Galois representation,0,1,0,0,0,0,0,0,0,GalRep,,224,175,-38,-38,-38,-38
S,InertiaGroup,nth (lower) ramification subgroup of the finite part of a Galois representation,0,2,0,0,0,0,0,0,0,148,,0,0,GalRep,,224,175,-38,-38,-38,-38
S,IsUnramified,True if a Galois representation is unramified,0,1,0,0,0,0,0,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,IsRamified,True if a Galois representation is ramified,0,1,0,0,0,0,0,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,IsTamelyRamified,True if a Galois representation is tamely ramified,0,1,0,0,0,0,0,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,IsWildlyRamified,True if a Galois representation is wildly ramified,0,1,0,0,0,0,0,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,ConductorExponent,Conductor exponent of a Galois representation,0,1,0,0,0,0,0,0,0,GalRep,,148,-38,-38,-38,-38,-38
S,Conductor,Conductor of a Galois representation,0,1,0,0,0,0,0,0,0,GalRep,,401,-38,-38,-38,-38,-38
S,DefiningPolynomial,The polynomial whose roots Group(A) permutes,0,1,0,0,0,0,0,0,0,GalRep,,312,-38,-38,-38,-38,-38
S,Degree,Degree (=dimension) of a Galois representation,0,1,0,0,0,0,0,0,0,GalRep,,148,-38,-38,-38,-38,-38
S,Dimension,Degree (=dimension) of a Galois representation,0,1,0,0,0,0,0,0,0,GalRep,,148,-38,-38,-38,-38,-38
S,IsIndecomposable,True if the Galois representation A is indecomposable,0,1,0,0,0,0,0,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,IsIrreducible,True if the Galois representation A is irreducible,0,1,0,0,0,0,0,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,Character,Character of a Galois representation A. To be defined A must have one component,0,1,0,0,0,0,0,0,0,GalRep,,39,-38,-38,-38,-38,-38
S,EulerFactor,"Euler factor of a Galois representation. The coefficient field  (rational, complex or cyclotomic field) may be specified with the  optional parameter R",0,1,0,0,0,0,0,0,0,GalRep,,312,-38,-38,-38,-38,-38
S,InertiaInvariants,Inertia invariants of a Galois representation A (an unramified Galois representation),0,1,0,0,0,0,0,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,IsZero,True if A is the Galois representation 0,0,1,0,0,0,0,0,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,IsOne,True if A is the trivial 1-dimensional Galois representation,0,1,0,0,0,0,0,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,!!,"Change a Galois representation by a finite representation with character chi, which must be a character of Group(A)",0,2,0,0,0,0,0,0,0,39,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,!!,"Change a Galois representation by a finite representation with character chi, a character of Group(A)  represented as a sequence of values",0,2,0,0,0,0,0,0,0,82,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,Minimize,"Replace Group(A) by its smallest possible quotient through which all  components of A factor. If To is specified, instead replace Group(A) by  Group(To), assuming the A factors through it",0,1,0,0,0,0,0,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,ChangePrecision,Change precision of the base field of a Galois representation,0,2,0,0,1,0,0,0,0,148,,1,1,GalRep,,-38,-38,-38,-38,-38,-38
S,ChangePrecision,Change precision of the base field of a Galois representation,0,2,0,0,0,0,0,0,0,148,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,BaseChange,Base change (restriction) of a Galois representation A over K over a finite extension E/K,0,2,0,0,0,0,0,0,0,400,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,Restriction,Restriction (base change) of a Galois representation A over K over a finite extension E/K,0,2,0,0,0,0,0,0,0,400,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,Induction,"Induction of a Galois representation A over K to K0, a subfield of K",0,2,0,0,0,0,0,0,0,400,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,*,Tensor product of two Galois representations,0,2,0,0,0,0,0,0,0,GalRep,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,/,"Tensor A1 with A2^(-1), for 1-dimensional A2",0,2,0,0,0,0,0,0,0,GalRep,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,/,"Tensor A1 with A2^(-1), for 1-dimensional A2",0,2,0,0,0,0,0,0,0,GalRep,,0,0,148,,GalRep,-38,-38,-38,-38,-38
S,+,Direct sum of two Galois representations,0,2,0,0,0,0,0,0,0,GalRep,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,^,Tensor power of a Galois representation,0,2,0,0,0,0,0,0,0,-1,,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,Decomposition,Decompose $A$ into indecomposable (for semisimple representations  same as irreducible) consituents,0,1,0,0,0,0,0,0,0,GalRep,,82,-38,-38,-38,-38,-38
S,Determinant,Determinant of a Galois representation (a 1-dimensional Galois representation),0,1,0,0,0,0,0,0,0,GalRep,,GalRep,-38,-38,-38,-38,-38
S,-,"Assuming A2 is a Galois subrepresentation of A1, compute A1-A2",0,2,0,0,0,0,0,0,0,GalRep,,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,eq,True if the two Galois representations are equal,0,2,0,0,0,0,0,0,0,GalRep,,0,0,GalRep,,36,-38,-38,-38,-38,-38
S,GaloisRepresentation,Local Galois representation of an elliptic curve over a p-adic field,1,0,1,334,0,400,1,0,0,0,0,0,0,0,334,,GalRep,-38,-38,-38,-38,-38
S,GaloisRepresentation,Local Galois representation of an elliptic curve over Q at p,1,0,1,334,0,262,2,0,0,0,0,0,0,0,148,,0,0,334,,GalRep,-38,-38,-38,-38,-38
S,GaloisRepresentation,Local Galois representation of an elliptic curve E over a number field F at a given prime ideal P,1,0,1,334,0,27,2,0,0,0,0,0,0,0,217,,0,0,334,,GalRep,-38,-38,-38,-38,-38
S,GaloisRepresentation,Galois representation associated to (H^1 of) a hyperelliptic curve C/Q at p,1,0,1,338,0,262,2,0,0,0,0,0,0,0,148,,0,0,338,,GalRep,-38,-38,-38,-38,-38
S,GaloisRepresentation,Galois representation associated to (H^1 of) a hyperelliptic curve C over a p-adic field,1,0,1,338,0,400,1,0,0,0,0,0,0,0,338,,GalRep,-38,-38,-38,-38,-38
S,GaloisRepresentation,Galois representation associated to (H^1 of) a hyperelliptic curve C over a number field at a prime ideal P,1,0,1,338,0,27,2,0,0,0,0,0,0,0,217,,0,0,338,,GalRep,-38,-38,-38,-38,-38
S,GaloisRepresentation,Local Galois representation at p of the dual of an Artin representation A,0,2,0,0,0,0,0,0,0,148,,0,0,ArtRep,,GalRep,-38,-38,-38,-38,-38
S,GaloisRepresentation,Local Galois representation at p of a Dirichlet character chi,0,2,0,0,0,0,0,0,0,148,,0,0,GrpDrchElt,,GalRep,-38,-38,-38,-38,-38
S,GaloisRepresentation,Local Galois representation at p of a modular form f,0,2,0,0,0,0,0,0,0,148,,0,0,ModFrmElt,,GalRep,-38,-38,-38,-38,-38
