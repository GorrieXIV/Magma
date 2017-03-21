//$Id:: basics.m 3187 2016-04-19 10:05:00Z eobr007                         $:

freeze;

// Structure for storing a matrix and its SLP
MatSLP := recformat<mat : GrpElt, slp : GrpSLPElt>;
EltSLP := recformat<elt : GrpElt, slp : GrpSLPElt>;

intrinsic SwapElements(~S :: SeqEnum, i :: RngIntElt, j :: RngIntElt)
    { Swap elements at indices i and j in S. }
    require i le #S and j le #S and i gt 0 and j gt 0 and
	IsDefined(S, i) and IsDefined(S, j) : "Could not sequence elements";
    
    temp := S[i];
    S[i] := S[j];
    S[j] := temp;
end intrinsic;

intrinsic RandomConjugate(G :: GrpPerm) -> GrpPerm
    { Return random conjugate of G in Generic(G) }
    return G^Random(Generic(G));
end intrinsic;

intrinsic RandomConjugate(G :: GrpMat) -> GrpMat
    { Return random conjugate of G in Generic(G) }
    return G^Random(Generic(G));
end intrinsic;

intrinsic UserGenerators(V :: ModTupRng) -> SeqEnum
    { Return the sequence of generators that defined V. }

    return [V.i : i in [1 .. NumberOfGenerators(V)]];
end intrinsic;

intrinsic UserGenerators(W :: GrpSLP) -> SeqEnum
    { Return the sequence of generators that defined W. }

    return [W.i : i in [1 .. NumberOfGenerators(W)]];
end intrinsic;

intrinsic UserGenerators(G :: GrpLie) -> SeqEnum
    { Return the sequence of generators that defined G. }

    return Generators(G);
end intrinsic;

intrinsic UserGenerators (G :: GrpMat) -> SeqEnum
{Return supplied or defining generators of G}
   if assigned G`UserGenerators then return G`UserGenerators; 
   else return [G.i: i in [1..Ngens (G)]]; end if;
end intrinsic;                                                                  

intrinsic UserGenerators (G :: GrpPC) -> SeqEnum
{Return supplied or defining generators of G}
   if assigned G`UserGenerators then return G`UserGenerators; 
   else return [G.i: i in [1..NPCgens (G)]]; end if;
end intrinsic;                                                                  

intrinsic UserGenerators (G :: GrpAb) -> SeqEnum
{Return supplied or defining generators of G}
   if assigned G`UserGenerators then return G`UserGenerators; 
   else return [G.i: i in [1..Ngens (G)]]; end if;
end intrinsic;                                                                  

intrinsic UserGenerators(F :: GrpFP) -> []
    { Return the sequence of generators that defined F. }

    return [F.i : i in [1 .. NumberOfGenerators(F)]];
end intrinsic;

intrinsic UserGenerators(G :: GrpGPC) -> []
    { Return the sequence of generators that defined G. }
    if assigned G`UserGenerators then return G`UserGenerators; 
    else return [G.i : i in [1 .. NumberOfGenerators(G)]]; end if;
end intrinsic;

intrinsic Generic(G :: GrpPC) -> GrpPC
    { The generic version of G, ie G itself. }

    return G;
end intrinsic;

intrinsic Generic(G :: GrpAb) -> GrpAb
    { The generic version of G, ie G itself. }

    return G;
end intrinsic;

intrinsic WordGroup(A :: GrpAb) -> GrpAb
    { An SLP group on the same number of generators as A. }

    return SLPGroup(NumberOfGenerators(A));
end intrinsic;

intrinsic WordGroup(A :: GrpPC) -> GrpSLP
    { An SLP group on the same number of generators as A. }
    return SLPGroup(NumberOfGenerators(A));
end intrinsic;

intrinsic WordGroup(A :: GrpGPC) -> GrpSLP
    { An SLP group on the same number of generators as A. }
    return SLPGroup(NumberOfGenerators(A));
end intrinsic;

intrinsic IsIdentity (g:: GrpSLPElt) -> BoolElt 
{True iff g is the identity element}
   return g eq Parent (g).0;
end intrinsic;

intrinsic IsIdentity (x :: AlgMatElt) -> BoolElt
{True iff x is the identity matrix}
  return x^0 eq x;
end intrinsic;    

intrinsic InnerProduct(V :: ModTupFld) -> Mtrx
    { Return the inner product matrix of V. }

    return Matrix([[(u, v) : v in Basis(V)] : u in Basis(V)]);
end intrinsic;

function elementFrobeniusTwist(element, r)
    char := Characteristic(CoefficientRing(element));
    return Generic(Parent(element)) ! [e^(char^r) :
	e in ElementToSequence(element)];
end function;

function structFrobeniusTwist(struct, r)
    return sub<Generic(struct) | [FrobeniusImage(struct.i, r) :
	i in [1 .. NumberOfGenerators(struct)]]>;
end function;

intrinsic FrobeniusImage(G :: GrpMat, r :: RngIntElt) -> GrpMat
    { Frobenius twist of matrix group G, i.e. returns the matrix group where
    each generator of G has been FrobeniusTwist'ed. Also returns
    inclusion homomorphism into the general linear group. }
    return structFrobeniusTwist(G, r);
end intrinsic;

intrinsic FrobeniusImage(v :: ModTupFldElt[FldFin], r :: RngIntElt) ->
    ModTupFldElt
    { Frobenius twist of vector v, i.e. returns the vector where the entries
    have been raised to the power p^r, where p is the characteristic of the
    underlying field. }
    return elementFrobeniusTwist(v, r);
end intrinsic;

intrinsic FrobeniusImage(V :: ModTupFld[FldFin], r :: RngIntElt) ->
    ModTupFld, Map
    { Frobenius twist of vector space V, i.e. returns the vector space where
    each basis element of V has been FrobeniusTwist'ed. Also returns
    inclusion homomorphism into the full vector space. }
    return structFrobeniusTwist(V, r);
end intrinsic;

intrinsic FrobeniusImage(v :: ModGrpElt, r :: RngIntElt) ->
    ModGrpElt
    { Frobenius twist of vector v, i.e. returns the vector where the entries
    have been raised to the power p^r, where p is the characteristic of the
    underlying field. }
    return elementFrobeniusTwist(v, r);
end intrinsic;

intrinsic FrobeniusImage(M :: ModRng, r :: RngIntElt) -> ModRng
    { Frobenius twist of module M, i.e. returns the module where
    each generator of M has been FrobeniusTwist'ed. }
    return RModule([FrobeniusImage(g, r) : g in ActionGenerators(M)]);
end intrinsic;

intrinsic FrobeniusImage(M :: ModGrp, G :: GrpMat, r :: RngIntElt) -> ModGrp
    { Frobenius twist of module M, i.e. returns the module where
    each generator of M has been FrobeniusTwist'ed. }
    return GModule(G, [FrobeniusImage(g, r) : g in ActionGenerators(M)]);
end intrinsic;

intrinsic KroneckerDelta(i :: RngIntElt, j :: RngIntElt) -> RngIntElt
    {Return 1 if i = j and 0 otherwise.}
    return i eq j select 1 else 0;
end intrinsic;

ClassicalVerify := function (G, E, W, CB)
   assert #E eq #W;
   flag := [E[i] eq CB * G`SLPGroupHom (W[i]) * CB^-1: i in [1..#W]];
   return Set(flag) eq {true};
end function;

// Error during constructive recognition
RecognitionError := recformat<
    Description : MonStgElt,
    Error : Any>;

UserWords := function (G)
   if Type(G) eq GrpMat and assigned G`UserWords then
      return G`UserWords;
   else
      return false;
   end if;
end function;

/* rewrite wg, a word in generators of G, as word in user generators of G */

WordToUser := function (G, wg)
   index := [Position (G`UserGenerators, G.i): i in [1..Ngens (G)]];
   W := Parent (wg); WW := G`SLPGroup;
   gamma := hom <W -> WW | [WW.i: i in index]>;
   return gamma (wg);
end function;

/* get a random element of G and return it both as a
   straight-line program and as an element */

intrinsic RandomWord (G:: Grp) -> GrpMatElt, GrpSLPElt
{construct a random element of G and return it both as a
 element and as straight-line program}

   if not assigned G`SLPGroup and not assigned G`SLPGroupHom then
      "Input group must have associated SLPGroup and homomorphism";
      return false, _;
   end if;

   B := G`SLPGroup;

   if not assigned B`RandomProcess then
      P := RandomProcess (B: Scramble := 100);
      B`RandomProcess := P;
   else
      P := B`RandomProcess;
   end if;

   w := Random (P);
   gamma := G`SLPGroupHom;
   g := gamma (w);
   return g, w;
end intrinsic;


/* set up hom from B -> G where U is the list of images of
   generators of B; do it in this way to  ensure that it
   does not force membership testing in G */

MyHom := function (G, B, U)
   d := Degree (G);
   F := BaseRing (G);
   gens := [GL (d, F) ! G.i : i in [1..Ngens (G)]];
   pos := [Position (gens, U[i]) : i in [1..#U]];
   return hom <B -> G | [G.i : i in pos]>;
end function;

procedure InitialiseGroup (G)
   if not assigned G`UserGenerators then 
      U := [G.i : i in [1..Ngens (G)]];
      G`UserGenerators := U;
   else 
      U := UserGenerators (G);
   end if;
   W := SLPGroup (#U);
   G`SLPGroup := W;
   G`SLPGroupHom := MyHom (G, W, U);
   G`UserWords := [W.i: i in [1..Ngens (W)]];
end procedure;

/* given words (as straightline programs) in G;
   return image of these in H, whose generators
   are in 1-1 correspondence with those of G */

ImagesOfWords := function (G, H, words)
   BG := G`SLPGroup;
   BH := H`SLPGroup;
   assert Ngens (BG) eq Ngens (BH);
   m := Ngens (BH);
   //print G, H, Ngens (BG), Ngens (BH);
   //assert Ngens (BG) ge Ngens (BH);
   //m := Ngens (BG);
   alpha := hom <BG -> BH | [BH.i : i in [1..m]]>;
   return [alpha (w): w in words];
end function;

// Get composed Function on a composition of Maps    
function getMapFunction(mapping)
    local f;

    f := func<x | x>;
    for g in Components(mapping) do
	f := func<x | Function(g)(f(x))>;
    end for;

    return f;
end function;

intrinsic Normalise(g :: Mtrx) -> Mtrx
    { Multiply g by the scalar which makes the first non-zero entry 1.}
    
    G := Generic(Parent(g));
    M := MatrixAlgebra(CoefficientRing(G), Degree(G));
    
    a := rep{g[i, j] : i in [1 .. NumberOfRows(g)],
	j in [1 .. NumberOfColumns(g)] | not IsZero(g[i, j])};
    return Generic(G) ! ((M ! g) / a), a;
end intrinsic;

/* decide if disrete log computation is practical in Magma

  If the field characteristic is 2, then Magma uses the
  fast Coppersmith algorithm which works pretty quickly
  up to about GF(2^300).

  For GF(p^n) for small p > 2, Magma uses the Pollard-Rho algorithm.  
  This involves (very roughly) about S field operations,
  where S = the square root of the largest prime dividing p^n - 1.
 
  Feedback from Allan Steel 2004 */

function CanApplyDiscreteLog(F : Limit := 10^9, Large := false)
   n := Degree(F);
   p := Characteristic(F);

   // additional databases installed for discrete log?
   if Large then 
      if p eq 2 then return n le 440; end if;
      if p eq 3 then return n le 261; end if;
      if p eq 5 then return n le 203; end if;
      if p eq 7 then return n le 150; end if;
      return n le 97;
   else 
      if p eq 2 then return n le 300; end if;
      if p eq 3 then return n le 127; end if;
      if p eq 5 then return n le 88; end if;
      if p eq 7 then return n le 78; end if;
   end if;
    
   // if p gt 10 and n gt 50 then return false; end if;
    
   estimate := Isqrt(Maximum(PrimeBasis(#F - 1)));
   return estimate lt Limit;
end function;


intrinsic WriteOverLargerField(G :: GrpMat, e :: RngIntElt :
    Scalars := false) -> GrpMat
    { Return the embedding H of G <= GL(d, q) inside GL(d, q^e).
    If Scalars is true, then return Z.H where Z = Centre(GL(d, q^e)).}
    
    E := ext<BaseRing(G) | e>;
    H := ExtendField(G, E);
    
    if Scalars then 
	return RandomConjugate(sub<Generic(H) | H,
	    ScalarMatrix(Degree(H), PrimitiveElement(E))>);
    else
	return RandomConjugate(H);
    end if;
end intrinsic;

function DiagonaliseMatrix(M : OrderEigenvalues := func<x | Sym(#x) ! 1>)
    /* Diagonalise matrix M, assuming it can be diagonalised. Returns a
    diagonal matrix D and a change of basis matrix C such that C^(-1) D C = M.
    Hence C consists of basis vectors of the eigenspaces, and each basis vector
    is normalised.
    
    The function OrderEigenvalues is used to order the eigenvalues of M. It
    should return a permutation on the eigenvalues. The default is the identity
    permutation, which corresponds to the order given by JordanForm(M).
    */
    local eigenvalues, eigenvectors, eigenspaces, field;

    form, conj, list := JordanForm(M);
    assert conj^(-1) * form * conj eq M;

    if not IsDiagonal(form) then
	error "DiagonaliseMatrix: M cannot be diagonalised";
    end if;

    assert {e[1] : e in Eigenvalues(M)} eq SequenceToSet(Diagonal(form));
    
    field := CoefficientRing(M);
    perm := PermutationMatrix(field, OrderEigenvalues(Diagonal(form)));
    
    // Diagonal matrix with eigenvalues
    d := perm^(-1) * form * perm;
    x := Matrix(field, NumberOfRows(d), NumberOfColumns(d),
	[Normalise(Vector(r)) : r in RowSequence(perm^(-1) * conj)]);
    assert x^(-1) * d * x eq M;
    
    return d, x;
end function;

function EvaluateMatTup(M, l)
    /* Given a matrix M with entries in a FldFunRat or RngMPol R with
    Rank(R) = n, and a sequence l of n elements from the coefficient ring of
    R, return the matrix N computed from M by evaluating every entry in
    M on l. N will have the same coefficient ring as R. */

    if Degree(Parent(M)) eq 0 then
	error "Matrix must not be empty";
    end if;
    
    A := Parent(M);    
    R := CoefficientRing(A);
    F := CoefficientRing(R);
    
    if not forall{x : x in l | IsCoercible(F, x)} then
	error "All elements of l must be coercible into the coefficient ring",
	    "of the rational function field of M";
    end if;

    // Construct evaluation homomorphisms
    MA := MatrixAlgebra(F, Degree(A));
    eval_hom := hom<R -> F | [l[i] : i in [1 .. #l]]>;
    mat_hom := hom<A -> MA | eval_hom>;

    // Evaluate matrix
    return mat_hom(M);
end function;

intrinsic Embed(G :: GrpMat[FldFin]) -> GrpMat
    {return isomorphic copy of G defined over standard copy of defining field}

    K := CoefficientRing(G);
    F := GF(Characteristic(K), Degree(K) : Check := false);
    return Embed(G, F);
end intrinsic;

intrinsic Embed(G :: GrpMat[FldFin], F :: FldFin) -> GrpMat
    {return isomorphic copy of G defined over F}
    
    K := CoefficientRing(G);
    require #K eq #F : "Field sizes must match";
    Embed(K, F);
    return sub<GL(Degree(G), F) | [G.i : i in [1 .. NumberOfGenerators(G)]]>;
end intrinsic;

intrinsic Embed(g :: GrpMatElt[FldFin]) -> GrpMatElt
    {return copy of g defined over standard copy of defining field}

    K := CoefficientRing(g);
    F := GF(Characteristic(K), Degree(K) : Check := false);
    return Embed(g, F);
end intrinsic;

intrinsic Embed(g :: GrpMatElt[FldFin], F :: FldFin) -> GrpMatElt
    {return copy of g defined over F}

    K := CoefficientRing(g);
    require #K eq #F : "Field sizes must match";
    Embed(K, F);
    return GL(Degree(g), F) ! g;
end intrinsic;

intrinsic IsStandardGF (F :: FldFin) -> BoolElt 
{if F is standard copy of this field return true, else false}
    p := Characteristic(F);
    d := Degree(F);
    S := GF(p, d : Check := false, Optimize := false);
    return F cmpeq S;
end intrinsic;

intrinsic HasBSGS (G :: GrpMat[FldFin]) -> BoolElt 
{does G already know a BSGS? if so, return true and basic orbit lengths, else false}
   try
      return true, BasicOrbitLengths (G);
   catch e
      return false, _;
   end try;
end intrinsic;

