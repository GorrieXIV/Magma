freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//                Various Constructions for Lattices              //
//                 By Bernd Souvignier, Allan Steel               // 
//                     Modified by David Kohel                    //
//                         January 2000                           // 
//                                                                //
////////////////////////////////////////////////////////////////////

//  (With some items added by MW and Steve)                       

ZZ := IntegerRing();
QQ := RationalField();

///////////////// Embedding spaces for lattices ////////////////////

intrinsic AmbientSpace(L::Lat) -> ModTupFld, Map
   {The ambient space of the lattice L, i.e. the tensor 
   product of L with the rationals}
   K := FieldOfFractions(BaseRing(L));
   MatK := MatrixAlgebra(K,Degree(L)); 
   V := VectorSpace(K,Degree(L),MatK!InnerProductMatrix(L));
   return V, map< L -> V | x :-> V!Eltseq(x) >; 
end intrinsic;

intrinsic CoordinateSpace(L::Lat) -> ModTupFld, Map
   {The coordinate space of the lattice L, i.e. the tensor 
   product of the coordinate lattice of L with the rationals}
   K := FieldOfFractions(BaseRing(L));
   MatK := MatrixAlgebra(K,Rank(L)); 
   V := VectorSpace(K,Rank(L),MatK!GramMatrix(L));
   return V, map< L -> V | x :-> V!Coordinates(L,x) >; 
end intrinsic;

////////////////////// Standard attributes  ////////////////////////////

intrinsic BaseExtend(L::Lat,S::Rng) -> Lat
   {Change ring of L to S}
   return ChangeRing(L,S);
end intrinsic;

intrinsic Content(L::Lat) -> RngIntElt
   {The content of the lattice L.}

   require IsExact(L) : "Argument 1 must be an exact lattice";
   S := Eltseq(GramMatrix(L));
   if Type(Universe(S)) eq RngInt then
      return GCD(S);
   else
      return GCD([ Numerator(x) : x in S ])
         / LCM([ Denominator(x) : x in S ]);
   end if;
end intrinsic;

intrinsic IsExact(L::Lat) -> BoolElt
   {Returns true if and only if the lattice has coordinates 
   and inner product specified in the exact rings Z or Q.}
   R := BaseRing(L);
   return R cmpeq ZZ or R cmpeq QQ;
end intrinsic;

// Banal? Not true for real lattices:

intrinsic CoordinateRing(L::Lat) -> Rng
    {The ring of coefficients of the lattice L}
    return ZZ;
end intrinsic;

///////////////// The associated quadratic form  /////////////////

intrinsic QuadraticForm(L::Lat : PolyRing:=0) -> RngMPolElt
{The quadratic form associated to the lattice L.}

   if PolyRing cmpne 0 then
       P := PolyRing;
       require ISA(Type(P), RngMPol) and 
               BaseRing(P) eq BaseRing(L) and Rank(P) eq Rank(L) 
               : "Bad optional argument 'PolyRing'";
   else
      P := PolynomialRing(BaseRing(L),Rank(L));
      AssignNames(~P, ["x" cat IntegerToString(i): i in [1..Rank(L)]]);
   end if;
   return &+[ (L.i,L.j)*P.i*P.j : i,j in [1..Rank(L)] ];
end intrinsic;

intrinsic QuadraticForm(M::Mtrx : PolyRing:=0) -> RngMPolElt
{The quadratic form associated to the symmetric matrix M.}

   assert IsSymmetric(M); 
   d:=Nrows(M);
   if PolyRing cmpne 0 then
       P := PolyRing;
       require ISA(Type(P), RngMPol) and 
               BaseRing(P) eq BaseRing(M) and Rank(P) eq d 
               : "Bad optional argument 'PolyRing'";
   else
       P := PolynomialRing(BaseRing(M),d);
       AssignNames(~P, ["x" cat IntegerToString(i): i in [1..d]]);
   end if;
   return &+[ M[i][j]*P.i*P.j : i,j in [1..d] ]; 
end intrinsic;

////////////////// Inner product scaling of lattices  //////////////////

intrinsic ScaledLattice(L::Lat,n::RngIntElt) -> Lat
   {The coordinate lattice similar to L with Gram matrix scaled by n}
   require n gt 0 : "Argument 2 must be positive.";
   return LatticeWithGram(n*GramMatrix(L));
end intrinsic;

intrinsic ScaledLattice(L::Lat,n::FldRatElt) -> Lat
   {The coordinage lattice similar to L with Gram matrix scaled by n}
   require n gt 0 : "Argument 2 must be positive.";
   return LatticeWithGram(n*GramMatrix(L));
end intrinsic;

///////////////////// Access standard attributes ///////////////////////

function GetR(L)
    if BaseRing(L) cmpeq ZZ then
	return QQ;
    else
	return BaseRing(L);
    end if;
end function;

function MatrixR(X)
    if BaseRing(Parent(X)) cmpeq ZZ then
	return ChangeRing(Parent(X), QQ) ! X;
    else
	return X;
    end if;
end function;

function MatrixZ(X)
    return ChangeRing(Parent(X), ZZ) ! X;
end function;

function BasisMatrixR(L)
    return MatrixR(BasisMatrix(L));
end function;

function InnerProductMatrixR(L)
    return MatrixR(InnerProductMatrix(L));
end function;

function IntegralMatrix(X)
    d := LCM([Denominator(x): x in Eltseq(X)]);
    return MatrixZ(d * X), d;
end function;

function PrimitiveMatrix(X)
    g := GCD(Eltseq(X));
    if g ne 1 then
	X := Parent(X) ! [x div g: x in Eltseq(X)];
    end if;
    return X, g;
end function;

function ReduceBasis(B)
    R := BaseRing(Parent(B));
    B := LLL(B);
    B := Submatrix(B, 1, 1, 
       rep{i: i in [Nrows(B)..1 by -1] | not IsZero(B[i])}, Ncols(B) );
    return B;
end function;

function IsCompatibleR(L1, L2)
    R1 := BaseRing(L1);
    R2 := BaseRing(L2);
    return (R1 cmpeq ZZ or R1 cmpeq QQ) and 
           (R2 cmpeq ZZ or R2 cmpeq QQ) or R1 cmpeq R2;
end function;

function IsCompatibleDegree(L1, L2)
    return Degree(L1) eq Degree(L2);
end function;

function IsCompatibleRDegree(L1, L2)
    return IsCompatibleR(L1, L2) and IsCompatibleDegree(L1, L2);
end function;

/////////////////////////// Internal sum ///////////////////////////////

intrinsic '+'(L1::Lat, L2::Lat)[~] -> Lat
    {The sum of lattices L1 and L2}
    require IsCompatibleR(L1, L2):
	"Arguments 1 and 2 have incompatible coefficient rings";
    require IsCompatibleDegree(L1, L2):
	"Arguments 1 and 2 have incompatible degrees";
    B := VerticalJoin(BasisMatrixR(L1), BasisMatrixR(L2));
    return Lattice(B, InnerProductMatrixR(L1));
end intrinsic;

///////////////////////////// DirectSum ////////////////////////////////

intrinsic DirectSum(L1::Lat, L2::Lat) -> Lat
    {The orthogonal direct sum of lattices L1 and L2.}
    require IsCompatibleR(L1, L2):
	"Arguments 1 and 2 have incompatible coefficient rings";
    return LatticeWithBasis(
	DiagonalJoin(BasisMatrixR(L1), BasisMatrixR(L2)),
	DiagonalJoin(InnerProductMatrixR(L1), InnerProductMatrixR(L2))
    );
end intrinsic;

intrinsic OrthogonalSum(L1::Lat, L2::Lat) -> Lat
    {The orthogonal direct sum of lattices L1 and L2.}
    require IsCompatibleR(L1, L2):
	"Arguments 1 and 2 have incompatible coefficient rings";
    return LatticeWithBasis(
	DiagonalJoin(BasisMatrixR(L1), BasisMatrixR(L2)),
	DiagonalJoin(InnerProductMatrixR(L1), InnerProductMatrixR(L2))
    );
end intrinsic;

intrinsic DirectSum(Q::[Lat]) -> Lat
    {The orthogonal direct sum of the lattices in Q.}
    B := BasisMatrixR(Q[1]);
    M := InnerProductMatrixR(Q[1]);
    for i := 2 to #Q do
	require IsCompatibleR(Q[1], Q[i]):
	    "Elements of sequence have incompatible coefficient rings";
	B := DiagonalJoin(B, BasisMatrixR(Q[i]));
	M := DiagonalJoin(M, InnerProductMatrixR(Q[i]));
    end for;
    return LatticeWithBasis(B, M);
end intrinsic;

intrinsic OrthogonalSum(Q::[Lat]) -> Lat
    {The orthogonal direct sum of the lattices in Q.}
    B := BasisMatrixR(Q[1]);
    M := InnerProductMatrixR(Q[1]);
    for i := 2 to #Q do
	require IsCompatibleR(Q[1], Q[i]):
	    "Elements of sequence have incompatible coefficient rings";
	B := DiagonalJoin(B, BasisMatrixR(Q[i]));
	M := DiagonalJoin(M, InnerProductMatrixR(Q[i]));
    end for;
    return LatticeWithBasis(B, M);
end intrinsic;

/////////////////////// TensorProduct //////////////////////////////////

intrinsic TensorProduct(L1::Lat, L2::Lat) -> Lat
    {The tensor product of lattices L1 and L2}
    require IsCompatibleR(L1, L2):
	"Arguments 1 and 2 have incompatible coefficient rings";
    R := GetR(L1);
    m1 := Rank(L1);
    m2 := Rank(L2);
    n1 := Degree(L1);
    n2 := Degree(L2);
    V1 := RSpace(R, n1);
    V2 := RSpace(R, n2);
    B := [
	TensorProduct(V1!Eltseq(b1), V2!Eltseq(b2)):
	    b2 in Basis(L2), b1 in Basis(L1)
    ];
    B := RMatrixSpace(R, #B, n1 * n2) ! &cat [Eltseq(v): v in B];
    M := TensorProduct(
	MatrixRing(R, n1) ! InnerProductMatrix(L1),
	MatrixRing(R, n2) ! InnerProductMatrix(L2)
    );
    return LatticeWithBasis(B, M);
end intrinsic;

intrinsic ExteriorSquare(L::Lat) -> Lat
    {The exterior square of lattice L}
    R := GetR(L);
    m := Rank(L);
    n := Degree(L);
    V := RSpace(R, n);
    B := [
	TensorProduct(v1, v2) - TensorProduct(v2, v1) where
	    v1 is V!Eltseq(L.i) where v2 is V!Eltseq(L.j):
	j in [1 .. i - 1], i in [1 .. m]
    ];
    B := RMatrixSpace(R, #B, n * n) ! &cat [Eltseq(v): v in B];
    B := ReduceBasis(B);
    M := MatrixRing(R, n) ! InnerProductMatrix(L);
    M := 1/1 * TensorProduct(M, M);
    return LatticeWithBasis(B, M);
end intrinsic;

intrinsic SymmetricSquare(L::Lat) -> Lat
    {The symmetric square of lattice L}
    R := GetR(L);
    m := Rank(L);
    n := Degree(L);
    V := RSpace(R, n);
    B := [
	TensorProduct(v1, v2) + TensorProduct(v2, v1) where
	    v1 is V!Eltseq(L.i) where v2 is V!Eltseq(L.j):
	j in [1 .. i - 1], i in [1 .. m]
    ] cat [
	TensorProduct(v, v) where v is V!Eltseq(L.i): i in [1 .. m]
    ];
    B := RMatrixSpace(R, #B, n * n) ! B;
    B := ReduceBasis(B);
    M := MatrixRing(R, n) ! InnerProductMatrix(L);
    M := 1/1 * TensorProduct(M, M);
    return LatticeWithBasis(B, M);
end intrinsic;

/////////////////////////// Dual stuff /////////////////////////////////

intrinsic Dual(L::Lat: Rescale := true) -> Lat
    {The dual lattice of L}
 if Determinant(L) eq 1 and IsIntegral(L) then return L; end if; // MW 26-05-09
    require Type(Rescale) cmpeq BoolElt:
	"Parameter 'Rescale' must be a logical";
    if not Rescale or not IsExact(L) then
	return InternalDualUnscaled(L);
    end if;
    B := MatrixR(BasisMatrix(L));
    M := MatrixR(InnerProductMatrix(L));
    F := MatrixR(GramMatrix(L));
    B := F^-1 * B;
    B := PrimitiveMatrix(IntegralMatrix(B));
    B := MatrixR(B);
    F := B * M * Transpose(B);
    F, d := IntegralMatrix(F);
    F, g := PrimitiveMatrix(F);
    M := (d/g) * M;
    return Lattice(B, M);
end intrinsic;

intrinsic DualQuotient(L::Lat) -> GrpAb, Lat, Map
    {The dual quotient Q := L#/L of L, together with the dual L# and 
    the natural epimorphism f:L# -> Q}
    require IsIntegral(L): "Argument 1 must be integral";
    D := Dual(L: Rescale := false);
    G, f := D / L;
    return G, D, f;
end intrinsic;


intrinsic Level(L::Lat) -> RngIntElt
{The level of the integral lattice L.  By definition this is the smallest
 integer k such that k*(v,v) is an even integer for each v in the dual 
 lattice L*.}
    require IsIntegral(L): "The lattice must be integral";
    M := ChangeRing(GramMatrix(L), Rationals()) ^ -1;
    g := LCM([Denominator(x) : x in Eltseq(M)] cat 
             [Denominator(x/2) : x in Diagonal(M)]); 
    return g; 
end intrinsic;


intrinsic EvenSublattice(L::Lat) -> Lat, Map
{The even sublattice of the integral lattice L together with the inclusion map.}
  require IsIntegral(L): "The lattice must be integral";
  B:= Basis(L);
  for i in [1..#B] do
    b:= B[i];
    if IsOdd(ZZ ! (b, b)) then
      L, h:= sub< L | B[1..i-1], 2*b, [ IsEven(ZZ ! (x,x)) select x else x+b : x in B[i+1..#B] ] >;
      if IsGLattice(L) and not IsEven(L) then
        error "The even sublattice is not G-invariant";
      end if;
      return L, h;
    end if;
  end for;
  return L, IdentityHomomorphism(L);
end intrinsic;


function q_qprime_split(n, q)
 q := &*[Integers()| ff[1]^ff[2] : ff in Factorization(n) | q mod ff[1] eq 0];
 qq := n div q; assert q*qq eq n and GCD(q,qq) eq 1; return q,qq; end function;

intrinsic PartialDual(L::Lat, n::RngIntElt : Rescale:=true) -> Lat
{Compute the n-th partial dual of the lattice L, where n divides
 the exponent of the dual quotient}
 require n gt 0 : "Argument 2 must be positive.";
 require IsIntegral(L): "The lattice must be integral";
 G,D,f:=DualQuotient(L); e:=Exponent(G);
 require e mod n eq 0: "Argument 2 must divide the exponent of DualQuotient";

/* TO DO: decide what input make sense ...
 require e mod n eq 0 and Gcd(n, e div n) eq 1 : 
        "Argument 2 must be an integer n dividing e with (n,e/n) = 1, "
       *"where e =", e, "is the exponent of the dual quotient of L";
 // one possibility is to dualize wrt the full Sylow part for all primes in n
 // (I don't think we want to be bothered with the 'partial' partial duals)
 n := q_qprime_split(e, n);  assert e mod n eq 0 and Gcd(n, e div n) eq 1;
*/

 I:=[((e div n)*x)@@f : x in Generators(G)];
 S:=sub<D|I cat Basis(L)>; if not Rescale then n:=1; end if;
 return Lattice(BasisMatrix(S),n*InnerProductMatrix(S)); end intrinsic;

intrinsic RescaledDual(L::Lat) -> Lat
{An integral lattice which is a multiple of the dual lattice of L}
    N := Exponent(DualQuotient(L));
    LD := Dual(L : Rescale:=false);
    M := ChangeRing( N*GramMatrix(LD), Integers());
    return LatticeWithGram(M);
end intrinsic;

intrinsic RescaledDual(L::Lat, q::RngIntElt) -> Lat
{An integral lattice which is a multiple of the q-partial dual lattice of L}
    level := Exponent(DualQuotient(L));
    qpart := q_qprime_split(level, q);
    LD := PartialDual(L, qpart : Rescale:=false);
    M := ChangeRing( q*GramMatrix(LD), Integers());
    return LatticeWithGram(M);
end intrinsic;

///////////////////// Density of Lattice Packings //////////////////////

intrinsic CentreDensity(L::Lat : Proof := true, Prune := [1.0: i in [1..Dimension(L)]]) -> RngElt
    {The centre density of L.}
    return CenterDensity(L, GetDefaultRealField(): Proof:=Proof, Prune:=Prune);
end intrinsic;

intrinsic CentreDensity(L::Lat, K::FldRe : Proof := true, Prune := [1.0: i in [1..Dimension(L)]]) -> RngElt
    {The centre density of L, in real field K.}
    return CenterDensity(L, K: Proof:=Proof, Prune:=Prune);
end intrinsic;

intrinsic CenterDensity(L::Lat, K::FldRe : Proof := true, Prune := [1.0: i in [1..Dimension(L)]]) -> RngElt
    {The center density of L, in real field K.}
    m := Rank(L);
    rho := Sqrt(K!Minimum(L: Proof:=Proof, Prune:=Prune))/2;
    return rho^m/Sqrt(Determinant(L));
end intrinsic;

intrinsic Density(L::Lat, K::FldRe : Proof := true, Prune := [1.0: i in [1..Dimension(L)]]) -> RngElt
    {The density of L, i.e. the density of the lattice packing 
    of L, returned in real field K.}
    m := Rank(L);
    if m mod 2 eq 0 then
        m2 := m div 2;
        Vn := Pi(K)^m2/Factorial(m2);
    else
        m2 := (m-1) div 2;
        Vn := 2^m*Pi(K)^m2*(K!Factorial(m2)/K!Factorial(m));
    end if;
    rho := Sqrt(K!Minimum(L: Proof:=Proof, Prune:=Prune))/2;
    return Vn*rho^m/Sqrt(Determinant(L));
end intrinsic;

intrinsic Density(L::Lat: Proof := true, Prune := [1.0: i in [1..Dimension(L)]]) -> RngElt
    {The density of L, i.e. the density of the lattice packing of L.}
    return Density(L, GetDefaultRealField(): Proof:=Proof, Prune:=Prune);
end intrinsic;

////////////////// Rational and integral multiples  ////////////////////

intrinsic '*'(s::RngIntElt, L::Lat) -> Lat
    {Return s * L}
    return LatticeWithBasis(s * BasisMatrix(L), InnerProductMatrix(L));
end intrinsic;

intrinsic '*'(L::Lat, s::RngIntElt) -> Lat
    {Return L * s}
    return s * L;
end intrinsic;

intrinsic '*'(s::FldRatElt, L::Lat) -> Lat
    {Return s * L}
    return LatticeWithBasis(s * BasisMatrixR(L), InnerProductMatrixR(L));
end intrinsic;

intrinsic '*'(L::Lat, s::FldRatElt) -> Lat
    {Return L * s}
    return s * L;
end intrinsic;

intrinsic '/'(L::Lat, s::RngIntElt) -> Lat
    {Return L / s}
    require s ne 0: "Argument 2 must be nonzero";
    return LatticeWithBasis((1/s) * BasisMatrixR(L), InnerProductMatrixR(L));
end intrinsic;

intrinsic '/'(L::Lat, s::FldRatElt) -> Lat
    {Return L / s}
    require s ne 0: "Argument 2 must be nonzero";
    return LatticeWithBasis((1/s) * BasisMatrixR(L), InnerProductMatrixR(L));
end intrinsic;

///////////////// Reduction algorithms on lattices  ////////////////////

intrinsic Seysen(L::Lat) -> Lat, AlgMatElt
    {Apply Seysen reduction to L, returning a new lattice and the 
    transformation matrix T};
    require IsExact(L): "Argument 1 must be an exact lattice";
    R := BaseRing(L);
    F := GramMatrix(L);
    if R cmpeq QQ then
	D := LCM([Denominator(x): x in Eltseq(F)]);
	F := ChangeRing(Parent(F), ZZ) ! (D * F);
    end if;
    F, T := SeysenGram(F);
    return LatticeWithBasis(
	MatrixRing(BaseRing(L),Rank(L)) !
           T*BasisMatrix(L), InnerProductMatrix(L) ), T;
end intrinsic;


//intrinsic HKZ(L::Lat) -> Lat, AlgMatElt
//    {Apply HKZ reduction to L, returning a new lattice and the 
//    transformation matrix T};
//    require IsExact(L): "Argument 1 must be an exact lattice";
//    R := BaseRing(L);
//    F := GramMatrix(L);
//    if R cmpeq QQ then
//	D := LCM([Denominator(x): x in Eltseq(F)]);
//	F := ChangeRing(Parent(F), ZZ) ! (D * F);
//    end if;
//    F, T := HKZGram(F);
//    return LatticeWithBasis(
//	MatrixRing(BaseRing(L),Rank(L)) !
//           T*BasisMatrix(L), InnerProductMatrix(L) ), T;
//end intrinsic;

intrinsic PairReduce(L::Lat) -> Lat, AlgMatElt
    {Apply pair-reduction to L, returning a new lattice and the 
    transformation matrix T};
    require IsExact(L): "Argument 1 must be an exact lattice";
    F := GramMatrix(L);
    F, T := PairReduceGram(F);
    return LatticeWithBasis(
	MatrixRing(BaseRing(L),Rank(L)) ! T*BasisMatrix(L), 
           InnerProductMatrix(L) ), T;
end intrinsic;

///////////////////// Orthogonal decomposition /////////////////////////

////////////////////////////////////////////////////////////////////////
//                      ORTHOGONAL DECOMPOSITION                      //
////////////////////////////////////////////////////////////////////////
  
intrinsic OrthogonalDecomposition(L::Lat) -> SeqEnum
    {The sequence of orthogonal components.
     This decomposition will also be orthogonal wrt. all additional forms in F if given.}

    // Gabi Nebe, March 2006
    // Previous code by David Kohel (2000) replaced by Allan Steel, March 2006

    LL,T:=LLL(L); //F=TGT^{tr}
    F:=GramMatrix(LL);
    max:=Max([F[i][i] : i in [1..NumberOfRows(F)]]);

    // m:=Min([F[i][i] : i in [1..NumberOfRows(F)]]);
    // if M/m le 10 then // Lattice is well reduced
    // this is just an idea, one could try to work with less
    // long vectors say up to length 10m and check whether
    // one already gets the lattice, or at least a sublattice of
    // full rank. If so, it might be better to go through the
    // classes of L/M and find indecomposable vectors there   
    // if not, one might try to speed up the SV by choosing a 
    // basis (b1,..bm) of the pure sublattice of L generated by M   
    // and completing it to a basis of L (b1..bn)
    // The interesting (not in M) short vectors are only those of
    // the form \sum ai bi with ai ne 0 for some i in {m+1..n}  
    // so one may stop the backtracking in SV when  *^m 0^{n-m}
    // is reached
      
    SV:=ShortVectors(L,max); //This List is sorted by length. 
    v:=SV[1][1];
    M:=sub<L | v>; //orthogonally decomposable sublattice
    comps:=[[v]];
    for s in [2..#SV] do
	    v:=SV[s][1];
	    if not v in M then  //v is indecomposable since it is not
	// the sum of smaller vectors
		    M:=sub<L | M,v >;
		    // join all components which contain a vector
		    // w with (v,w) neq 0
		    C:=[v];
		    for c in comps do
			    for w in c do
				    if (v,w) ne 0 then
					    C cat:= c;
					    Exclude(~comps,c);
					    break w;
				    end if;
			    end for;
		    end for;
	    Append(~comps,C);
	    if M eq L then break s; end if;
	    end if;
    end for;
    return [ sub< L | C > : C in comps ];

end intrinsic;

intrinsic OrthogonalDecomposition(L::Lat, F::SeqEnum) -> SeqEnum
  {"} // "
  if IsEmpty(F) then return OrthogonalDecomposition(L); end if; 
  require (ISA(Type(F[1]), Mtrx) and {Ncols(F[1]), Nrows(F[1])} eq {Degree(L)}):
    "The forms in F are incompatible with the lattice L.";
  comps:= OrthogonalDecomposition(L);
  R:= BaseRing(F[1]);
  i:= 1;
  while i le #comps do
    B:= ChangeRing(BasisMatrix(comps[i]), R);
    Indices:= [j: j in [i+1..#comps] | exists{f: f in F | 
      not IsZero(B * f * Transpose(ChangeRing(BasisMatrix(comps[j]), R)))} ];
    if IsEmpty(Indices) then
      i +:= 1;
    else
      comps[i] +:= &+ comps[Indices];
      for j in Reverse(Indices) do Remove(~comps, j); end for;
    end if;
  end while;
  return comps;
end intrinsic;

intrinsic OrthogonalDecomposition(F::SeqEnum: Optimize:= false) -> List, List
  {The orthogonal decomposition of Z^n wrt. the bilinear forms in F.}
  require not IsEmpty(F) : "The sequence of forms is empty.";
  R:= BaseRing(F[1]);
  require Type(R) in {FldRat, RngInt, FldRe} : "The forms must be over the integers, rationals or reals.";
  require IsPositiveDefinite(F[1]) : "The first form must be totally definite.";
  Lats:= OrthogonalDecomposition(LatticeWithGram(F[1]), F[2..#F]);
  if Optimize then
    Lats:= [LLL(l): l in Lats];
  end if; 
  Bases:= [* BasisMatrix(l): l in Lats *];
  Forms:= [* [ bR * f * Transpose(bR): f in F ] where bR:= ChangeRing(b, R): b in Bases *];
  return Bases, Forms;
end intrinsic;

/////////////// Base orthogonalization and Diagonalization /////////////

intrinsic Diagonalization(M::MtrxSpcElt) -> MtrxSpcElt, AlgMatElt, RngIntElt
    {The diagonalization of a symmetric matrix over an integral domain.
     In some cases (p-adics), the result could lose precision}
    require IsSymmetric(M) : "Argument 1 must be symmetric";
    BR:=BaseRing(Parent(M));
    require IsIntegralDomain(BR): "Base ring must be an integral domain";
    return OrthogonalizeGram(ChangeRing(M,FieldOfFractions(BR)));
end intrinsic;

intrinsic Orthogonalize(L::Lat) -> Lat, AlgMatElt
    {A lattice with Gram matrix equal to that of L, embedded in an 
    ambient space with a diagonal inner product matrix; the second 
    return value is the transformation matrix.}
    M, T := OrthogonalizeGram(InnerProductMatrix(L));
    C := MatrixR(BasisMatrix(L)) * MatrixR(T)^-1;
    return LatticeWithBasis(C, MatrixR(M)), T;
end intrinsic;

intrinsic Orthonormalize(L::Lat, K::FldRe) -> Lat
    {A lattice with Gram matrix equal to that of L embedded in the 
    Euclidean ambient space over the real field K}
    T := Orthonormalize(GramMatrix(L), K);
    return LatticeWithBasis(T);
end intrinsic;

intrinsic Orthonormalize(L::Lat) -> Lat
    {A lattice with Gram matrix equal to that of L embedded in the 
    Euclidean ambient space over the default real field}
    return Orthonormalize(L, GetDefaultRealField());
end intrinsic;

/* Not necessary to define Cholesky as identical to Orthonormalize,
   since they are defined to be the same in bind/o.b */

function ScaledMinkowskiVector(x,r,s : Precision:=167)
    S := Conjugates(x : Precision:=Precision);
    sq2 := Sqrt(RealField(Universe(S))!2);
    return [ Real(S[k]) : k in [1..r] ] cat
       &cat[ [ sq2*Real(S[k]), sq2*Imaginary(S[k]) ] 
                    : k in [r+1..r+2*s by 2] ]; 
end function;

/* For compatibility with previous function? */

intrinsic Lattice(R::RngOrd : Precision:=167) -> Lat, Map
   {The real lattice L given by the image of R under the Minkowski 
   map, with inner product given by the T2-norm on the number field, 
   followed by the isomorphism R -> L.}
   require Type(BaseRing(R)) eq RngInt :
      "Base ring of argument must be the integers";
   return MinkowskiLattice(R : Precision:=Precision);
end intrinsic;

intrinsic Lattice(I::RngOrdIdl : Precision:=167) -> Lat, Map
   {The real lattice L given by the image of I under the Minkowski 
   map, with inner product given by the T2-norm on the number field, 
   followed by the isomorphism I -> L.}
   require Type(BaseRing(Order(I))) eq RngInt :
      "Base ring of argument must be the integers";
   return MinkowskiLattice(I : Precision:=Precision);
end intrinsic;

intrinsic MinkowskiLattice(R::RngOrd : Precision:=167) -> Lat, Map
   {The real lattice L given by the image of R under the Minkowski 
   map, with inner product given by the T2-norm on the number field, 
   followed by the isomorphism R -> L.}
   require Type(BaseRing(R)) eq RngInt :
      "Base ring of argument must be the integers";
   r, s := Signature(R); 
   n := r+2*s;
   L := LatticeWithBasis( 
      Matrix(n,&cat[ ScaledMinkowskiVector(R!x,r,s : Precision:=Precision) : x in Basis(R) ]) );
   /*
   // Embedding in space RR^r x CC^(2*s) = RR^(r+4*s) of T_2-norm
   L := LatticeWithBasis( 
      Matrix(r+4*s,&cat[ ScaledMinkowskiVector(R!x,r,s) : x in Basis(R) ]) );
   */
   return L, hom< R -> L | x :-> 
      &+[ S[i]*L.i : i in [1..n] ] where S is Eltseq(x) >;
end intrinsic;

intrinsic MinkowskiLattice(I::RngOrdIdl : Precision:=167) -> Lat, Map
   {The real lattice L given by the image of I under the Minkowski 
   map, with inner product given by the T2-norm on the number field, 
   followed by the isomorphism I -> L.}
   R := Order(I);
   require Type(BaseRing(R)) eq RngInt :
      "Base ring of argument must be the integers";
   r, s := Signature(R); 
   n := r+2*s;
   L := LatticeWithBasis( 
      Matrix([ ScaledMinkowskiVector(R!x,r,s : Precision:=Precision) : x in Basis(I) ]) );
   f := function(x) 
      error if x notin I, "Argument is not in domain";
      return &+[ S[i]*L.i : i in [1..n] ] where S is 
          Eltseq(Solution(MatrixAlgebra(QQ,n)!
              BasisMatrix(I),Vector(QQ,n,Eltseq(x))));
   end function; 
   return L, hom< R -> L | x :-> f(x) >;
end intrinsic;

intrinsic MinkowskiSpace(F::FldAlg) -> Lat, Map
   {The Minkowski vector space V of F, as a real vector space, with 
   inner product given by the T2-norm on F, followed by the embedding 
   F -> V.}
   require Type(BaseField(F)) eq FldRat :
      "Base field of argument must be the rationals";
   r, s := Signature(F); 
   n := r+2*s;
   V := KSpaceWithBasis(
      Matrix([ ScaledMinkowskiVector(k,r,s) : k in Basis(F) ]) );
   return V, hom< F -> V | x :-> 
      &+[ S[i]*V.i : i in [1..n] ] where S is Eltseq(x) >;
end intrinsic;

intrinsic IsAutomorphism(L::Lat, x::Mtrx) -> BoolElt
   {Test if the integer matrix x is an autmorphism of L}
    if Type(BaseRing(Parent(x))) ne RngInt then return false; end if;
    r := Rank(L);
    if Nrows(x) ne r or Ncols(x) ne r then return false; end if;
    F := GramMatrix(L);
    y := Matrix(x);
    return y*F*Transpose(y) eq F;
end intrinsic;
