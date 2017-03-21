freeze;

///////////////////////////////////////////////////////////////////
//     Intrinsics for computing random non-singular surfaces  	 //
//  in P^4 from some of the special families described in	 //
//   Decker, Ein, Schreyer (J. Alg Geom 2, 1993, 185-237	 //
//             mch - 10/2012                                     //
///////////////////////////////////////////////////////////////////

////////////////// Some helper functions ////////////////////

function RandomMatrix(v,w,R,N)
// produces a random matrix of polys in R of degrees given by
// v[i]-w[j] in the (i,j)th place. [v,w are sequences of ints]
    return Matrix(R,[[Random(i-j,R,N): j in w] : i in v]);
end function;

function MyRandom(K,N)
 if Type(K) eq FldFin then return Random(K);
 else return K!Random(-N,N); end if;
end function;

function LeftKernel(M)
// returns a sequence of sequences, s,  s.t. the s give a
//  basis for the left kernel of polynomial matrix M
//  (seq s gives the coordinates of a kernel vector)
   Mmod := Module(BaseRing(M),Ncols(M));
   S := sub<Mmod|[M[i]:i in [1..Nrows(M)]]>;
   return [Eltseq(b): b in Basis(SyzygyModule(S))];
end function;

function RightKernel(M)
// returns a sequence of sequences, s,  s.t. the s give a
//  basis for the right kernel of polynomial matrix M
//  (seq s gives the coordinates of a kernel vector)
    return LeftKernel(Transpose(M));
end function;

function KoszulComplex(R)
// Lazy implementation using MinFreeRes! Should do directly!
    I := ideal<R|[R.i : i in [1..Rank(R)]]>;
    Mk := QuotientModule(I);
    return MinimalFreeResolution(Mk);
end function;

function Omega_i(R,i)
// creates the twisted sheaf of order i differentials Omega^i(i)
// on Proj(R)
    kc := KoszulComplex(R);
    if i eq #Terms(kc)-4 then
	return Term(kc,#Terms(kc)-3);
    end if;
    mat := BoundaryMap(kc,i+2);
    N := Ncols(mat);
    F := RModule(R,N);
    return quo<F|[F!r : r in RowSequence(mat)]>,[1: j in [1..N]];
end function;

function mat_space(U,V)
// U is an l*m matrix and V a n*k matrix over R. Return
// a basis for the module of m*n matrices M over R s.t.
// UMV=0

  R := BaseRing(U);
  l := Nrows(U); m := Ncols(U);
  n := Nrows(V); k := Ncols(V);

  P := PolynomialRing(R,n*m);
  M := Matrix(P,m,n,[P.i : i in [1..n*m]]);
  UMV := ChangeRing(U,P)*M*ChangeRing(V,P);
  rels := [[MonomialCoefficient(f,P.i) : i in [1..n*m]] :
		f in Eltseq(UMV)];
  M := Transpose(Matrix(R,rels));
  S := sub<F|[F!r : r in RowSequence(M)]> where 
	F is Module(R,Ncols(M));
  S := SyzygyModule(S);
  B := [Matrix(R,m,n,Eltseq(b)) : b in MinimalBasis(S)];
  return B;

end function;

function get_weights(B,wr,wc)
// find the gradings of the m*n matrices in B which represent
// maps between a graded module M1 with column weights wr and
// graded module M2 with column weights wc.
// Assumed that each element of B is homogeneous as an elt of
// Hom(M1,M2) and is non-zero

   wts := [Integers()|];
   if #B eq 0 then return wts; end if;
   m := #wr; n := #wc;
   for b in B do
     i :=1;
     while b[i] eq 0 do i +:= 1; end while;
     j := Representative(Support(b[i]));
     Append(~wts,LeadingTotalDegree(b[i,j])+wc[j]-wr[i]);
   end for;
   return wts;

end function;

/// Rational Ranestad surfaces with degree 10 and sectional genus 9 ///

function homGdFd(kc)

    R := BaseRing(Term(kc,1));
    K := BaseRing(R);
    gens := RowSequence(Matrix(BoundaryMap(kc,2)));
    dg := #gens;
    
    V := KSpace(K,25);
    W := sub<V|[V!&cat[[MonomialCoefficient(g[j],R.i) : i in [1..5]]
		: j in [1..5]] : g in gens]>;

    mats := KSpace(K,125);
    mps := [hom<V->mats| [mats.(j+25*i): j in [1..25]]> : i in [0..4]];
    W5 := sub<mats| [mp(b) : b in Basis(W), mp in mps]>;

    tr_inds := Eltseq(Transpose(Matrix(Integers(),5,5,[0..24])));
    tr_inds := [5*i+j: j in [1..5], i in tr_inds];
    transp := hom<mats->mats| [mats.i : i in tr_inds]>;
    hom_sp1 := W5 meet transp(W5);
    d := Dimension(hom_sp1);

    hm_mats := [Matrix(R,5,5,[&+[e[i+5*j]*R.i : i in [1..5]] :
	j in [0..24]]) where e is Eltseq(b): b in Basis(hom_sp1)];

    homs_big := KSpace(K,4*d+2*dg);
    to_mat := hom< homs_big->RMatrixSpace(R,11,10) |
	x :-> VerticalJoin(BlockMatrix(2,2,
	[&+[e[i+j*d]*hm_mats[i] : i in [1..d]]:j in [0..3]]),
	 HorizontalJoin(&+[e[i+4*d]*Matrix(1,5,gens[i]) : i in [1..dg]],
	  &+[e[i+4*d+dg]*Matrix(1,5,gens[i]) : i in [1..dg]]))
	 where e is Eltseq(x) >;
    return homs_big,to_mat;

end function;

intrinsic RandomRationalSurface_d10g9(P::Prj : RndP := 2, Check := true) -> Srfc
{ P is ordinary projective 4-space over the rationals or a finite field.
  Returns a random smooth rational surface in P from the Ranestad family
  with degree 10 and sectional genus 9. If the Check parameter is set to false,
  doesn't check the result for non-singularity or irreducibility.}

    K := BaseRing(P);
    require IsAmbient(P) and IsOrdinaryProjective(P) and
	(Dimension(P) eq 4) and (ISA(Type(K),FldRat) or
	  ISA(Type(K),FldFin)):
	"P must be 4-dimensional projective space over the rationals",
	"or a finite field";
    R := CoordinateRing(P);

    /* 
       if I = ideal of X then have 0 -> F -> G -> I(4) -> 0 where
	F=2*Omega3(3) G= 2*Omega1(1)+R and F->G is a random map.
       Get I from G*->F*.
       Have F*=2*Omega1(2) and 0->Omega1->K1->K0 &
	 G*=2*Omega3(4)+R and 0->K5->K4->Omega3->0 where
	  0->K5->K4->K3->K2->K1->K0->0 is the Koszul complex
		which is self-dual (up to twist)
    */

    kc := KoszulComplex(R);

    //let mat := BoundaryMap(kc,1);
    // m_ker := DiagonalJoin(mat,mat); gives 2*K1 -> 2*K0
    // m_im := HorizontalJoin(DiagonalJoin(mt,mt),ZeroMatrix(R,2,1))
    //     where mt is Transpose(mat);
    //       gives 2*K5->2*K4+R
    //
    // Elements of Hom(G*,F*) are given by 11x10
    // matrices M with entries homogeneous of degree 1 in R
    //   s.t. m_im*M=M*m_ker=0
    //
    // This <=> M is a blockmatrix [M1 M2; M3 M4; v1 v2]
    //  where the Mi are 5x5 matrices satisfying 
    //  Mi*mat=transpose(Mi)*mat=0 and vi are 5x1 vectors
    //  satisfying vi*mat=0.
    // The linear conditions that this puts on rows+columns
    // gives a 10-d subspace of {linear forms in R}^5 which
    // is generated by the syzygies in K2

    V,mp := homGdFd(kc);
    tries := 0;
    while tries lt 10 do
      tries +:= 1;
      M := mp(&+[MyRandom(K,RndP)*V.i : i in [1..Dimension(V)]]);

      // Now, with M the 11x10 matrix representing the map G*->F*
      //  can recover I as the ideal generated by all components
      //  of a basis for f(left kernel of M) where f is
      //   f: 2*K4+R -> 2*K3+R.
      B := LeftKernel(M);
      f_mat := Transpose(DiagonalJoin(DiagonalJoin(g,g),ScalarMatrix(1,R!1)))
    	where g is Matrix(BoundaryMap(kc,2));
      B := [Eltseq(Vector(b)*f_mat) : b in B];
      I := ideal<R|&cat[[e : e in Eltseq(b) | e ne 0] : b in B]>;
      B := MinimalBasis(I);
      if (#B ne 11) or (Sort([LeadingTotalDegree(b) : b in B]) ne
	([4] cat [5 : i in [1..10]])) then continue; end if;
      if Check then
        if not IsPrime(I) then continue; end if;
      end if;
      X := Surface(P,B : Check := false, Saturated := true);
      if Check then
	if IsSingular(X) then continue; end if;
      end if;
      return X;
    end while;
    error "Failed to generate non-singular surface in 10 tries.";

end intrinsic;

/// Enriques surfaces with degree 9 and sectional genus 6 ///
 
intrinsic RandomEnriquesSurface_d9g6(P::Prj : RndP := 2, Check := true) -> Srfc
{ P is ordinary projective 4-space over the rationals or a finite field.
  Returns a random Enriques surface in P from the family
  with degree 9 and sectional genus 6. If the Check parameter is set to false,
  doesn't check the result for non-singularity or irreducibility.}

    K := BaseRing(P);
    require IsAmbient(P) and IsOrdinaryProjective(P) and
	(Dimension(P) eq 4) and (ISA(Type(K),FldRat) or
	  ISA(Type(K),FldFin)):
	"P must be 4-dimensional projective space over the rationals",
	"or a finite field";
    R := CoordinateRing(P);

    //R<[x]> := PolynomialRing(K,5,"grevlex");
    tries := 0;
    while tries lt 10 do
      tries +:= 1;
      mat := RandomMatrix([2],[0:i in [1..12]],R,RndP);
      M := QuotientModule(ideal<R|Eltseq(mat)>);
      res := MinimalFreeResolution(M);

      //res should have betti table
      //[ 1  0  0  0  0  0]
      //[ 0 12 25 15  0  0]
      //[ 0  0  0  6 10  3]
      if not (Matrix(BettiTable(res)) eq
	Matrix(3,6,\[1,0,0,0,0,0,0,12,25,15,0,0,0,0,0,6,10,3])) then
	  continue;
      end if;

      mat := Matrix(BoundaryMap(res,3));
      M := quo<F|[F!r : r in RowSequence(mat)]> where F is RModule(R,25);
      res := MinimalFreeResolution(M);

      //res should have betti resolution
      //[25 15  0  0]
      //[ 0  6 10  3]
      if not (Matrix(BettiTable(res)) eq
	Matrix(2,4,\[25,15,0,0,0,6,10,3])) then
	  continue;
      end if;

      mat := Matrix(BoundaryMap(res,2));
      mat1 := Matrix([r : r in RowSequence(Transpose(mat)) |
		&and[(e eq 0) or (TotalDegree(e) eq 1) : e in r] ]);
      B := RightKernel(mat1);

      vec := Vector(B[#B]);
      // components of vec should be cubics
      vec1 := vec*mat;
      I := ideal<R | [e : e in Eltseq(vec1) | e ne 0]>;
      B := MinimalBasis(I);
      if (#B ne 15) or &or[LeadingTotalDegree(b) ne 5 : b in B] then
	continue;
      end if;
      if Check then
        if not IsPrime(I) then continue; end if;
      end if;
      X := Surface(P,B : Check := false, Saturated := true);
      if Check then
	if IsSingular(X) then continue; end if;
      end if;
      return X;
    end while;
    error "Failed to generate non-singular surface in 10 tries.";

    // res := MinimalFreeResolution(QuotientModule(I))
    //  should have betti resolution
    //[ 1  0  0  0  0]
    //[ 0  0  0  0  0]
    //[ 0  0  0  0  0]
    //[ 0  0  0  0  0]
    //[ 0 15 25 12  0]
    //[ 0  0  0  0  1]

end intrinsic;

//// Torus of degree 10 and sectional genus 6 ///

intrinsic RandomAbelianSurface_d10g6(P::Prj : RndP := 5, Check := true) -> Srfc
{ P is ordinary projective 4-space over the rationals or a finite field.
  Returns a 2-dimensional torus in P which is the zero subscheme of a random
  section of the Horrocks-Mumford bundle. If the Check parameter is set to false,
  doesn't check the result for non-singularity or irreducibility.}

    K := BaseRing(P);
    require IsAmbient(P) and IsOrdinaryProjective(P) and
	(Dimension(P) eq 4) and (ISA(Type(K),FldRat) or
	  ISA(Type(K),FldFin)):
	"P must be 4-dimensional projective space over the rationals",
	"or a finite field";
    R := CoordinateRing(P);

    S := HorrocksMumfordBundle(P);
    M := S`M;
    tries := 0;
    while tries lt 10 do
      s := M!([R!MyRandom(K,RndP) : i in [1..4]] cat [0 : i in [1..15]]);
      X := ZeroSubscheme(S,s);
      I := Ideal(X);
      if Check then
        if not IsPrime(I) then continue; end if;
      end if;
      B := MinimalBasis(I);
      X := Surface(P,B : Check := false, Saturated := true);
      if Check then
	if IsSingular(X) then continue; end if;
      end if;
      return X;	
    end while;
    error "Failed to generate non-singular surface in 10 tries.";

end intrinsic;

/// Minimal elliptic fibrations of kod dim 1 -
//  degree 7, sectional genus 6 and pg=2, q=0

intrinsic RandomEllipticFibration_d7g6(P::Prj : RndP := 2, Check := true) -> Srfc
{P is ordinary projective 4-space over the rationals or a finite field.
  Returns a random minimal Kodaira dimension 1 surface in P from a family with
  degree 7 and sectional genus 6. If the Check parameter is set to false,
  doesn't check the result for non-singularity or irreducibility.}

    K := BaseRing(P);
    require IsAmbient(P) and IsOrdinaryProjective(P) and
	(Dimension(P) eq 4) and (ISA(Type(K),FldRat) or
	  ISA(Type(K),FldFin)):
	"P must be 4-dimensional projective space over the rationals",
	"or a finite field";
    R := CoordinateRing(P);

    tries := 0;
    while tries lt 10 do
      mat := RandomMatrix([3,1,1],[0,0],R,RndP);
      M := quo<F|[F!r : r in RowSequence(mat)]> where F is
		RModule(R,2);
      res := MinimalFreeResolution(M);
      B := Eltseq(Matrix(BoundaryMap(res,2)));
      if Check then
        if not IsPrime(ideal<R|B>) then continue; end if;
      end if;
      X := Surface(P,B : Check := false, Saturated := true);
      if Check then
	if IsSingular(X) then continue; end if;
      end if;
      return X;	
    end while;
    error "Failed to generate non-singular surface in 10 tries.";
    
end intrinsic;

/// Minimal elliptic fibrations of kod dim 1 -
//  degree 8, sectional genus 7 and pg=2, q=0

intrinsic RandomEllipticFibration_d8g7(P::Prj : RndP := 2, Check := true) -> Srfc
{P is ordinary projective 4-space over the rationals or a finite field.
  Returns a random minimal Kodaira dimension 1 surface in P from a family with
  degree 8 and sectional genus 7. If the Check parameter is set to false,
  doesn't check the result for non-singularity or irreducibility.}

    K := BaseRing(P);
    require IsAmbient(P) and IsOrdinaryProjective(P) and
	(Dimension(P) eq 4) and (ISA(Type(K),FldRat) or
	  ISA(Type(K),FldFin)):
	"P must be 4-dimensional projective space over the rationals",
	"or a finite field";
    R := CoordinateRing(P);

    tries := 0;
    while tries lt 10 do
      mat := RandomMatrix([2,2,1],[0,0],R,RndP);
      M := quo<F|[F!r : r in RowSequence(mat)]> where F is
		RModule(R,2);
      res := MinimalFreeResolution(M);
      B := Eltseq(Matrix(BoundaryMap(res,2)));
      if Check then
        if not IsPrime(ideal<R|B>) then continue; end if;
      end if;
      X := Surface(P,B : Check := false, Saturated := true);
      if Check then
	if IsSingular(X) then continue; end if;
      end if;
      return X;	
    end while;
    error "Failed to generate non-singular surface in 10 tries.";
    
end intrinsic;

/// Minimal elliptic fibrations of kod dim 1 -
//  degree 9, sectional genus 7 and pg=1, q=0

intrinsic RandomEllipticFibration_d9g7(P::Prj : RndP := 2, Check := true) -> Srfc
{P is ordinary projective 4-space over the rationals or a finite field.
  Returns a random minimal Kodaira dimension 1 surface in P from a family with
  degree 9 and sectional genus 7. If the Check parameter is set to false,
  doesn't check the result for non-singularity or irreducibility.}

    K := BaseRing(P);
    require IsAmbient(P) and IsOrdinaryProjective(P) and
	(Dimension(P) eq 4) and (ISA(Type(K),FldRat) or
	  ISA(Type(K),FldFin)):
	"P must be 4-dimensional projective space over the rationals",
	"or a finite field";
    R := CoordinateRing(P);

    // construct the space of dual homs between G=2R+3Omega^1(1) and
    // F = R(-1)+2Omega^2(2)
    Ko := KoszulComplex(R);
    M2 := Matrix(BoundaryMap(Ko,2)); //10x5
    M3 := Matrix(BoundaryMap(Ko,3)); //10x10
    M4 := Matrix(BoundaryMap(Ko,4)); //5x10

    U := DiagonalJoin(IdentityMatrix(R,2),DiagonalJoin(M2t,
	DiagonalJoin(M2t,M2t))) where M2t is Transpose(M2);
    V := DiagonalJoin(ZeroMatrix(R,1,1),
	DiagonalJoin(M4t,M4t)) where M4t is Transpose(M4);
    B := mat_space(U,V);
    wts := get_weights(B,[1,1] cat [0 : i in [1..30]],[0 : i in [1..21]]);
    // wts should all be 0 or -1
    inds := [i : i in [1..#wts] | wts[i] le 0];
    ga := VerticalJoin(ZeroMatrix(R,2,30),DiagonalJoin(M3t,
	DiagonalJoin(M3t,M3t))) where M3t is Transpose(M3);   

    tries := 0;
    while tries lt 10 do
      mat := &+[((wts[i] eq 0) select R!MyRandom(K,RndP)
	else Random(1,R,RndP))*B[i] : i in inds];
      MK := HorizontalJoin(mat,ga);
      F := Module(R,[1 : i in [1..21]] cat [0 : i in [1..30]]);
      Mrel := sub<F|[F!r : r in RowSequence(MK)]>;
      S := SyzygyModule(Mrel);
      B1 := MinimalBasis(S);
      if #B1 ne 1 then continue; end if;
      I := ideal<R|Eltseq(B1[1])>;
      if Check then
        if not IsPrime(I) then continue; end if;
      end if;
      X := Surface(P,MinimalBasis(I) : Check := false, Saturated := true);
      if Check then
	if IsSingular(X) then continue; end if;
      end if;
      return X;	
    end while;
    error "Failed to generate non-singular surface in 10 tries.";
    // res := MinimalFreeResolution(QuotientModule(I))
    //  should have betti resolution
    //[ 1  0  0  0  0]
    //[ 0  0  0  0  0]
    //[ 0  0  0  0  0]
    //[ 0  2  0  0  0]
    //[ 0  9 20 13  3]
    
end intrinsic;

/// Non-minimal elliptic fibrations of kod dim 1 -
//  degree 10, sectional genus 10 and pg=2, q=0 and K^2=-2

intrinsic RandomEllipticFibration_d10g10(P::Prj : RndP := 2, Check := true) -> Srfc
{P is ordinary projective 4-space over the rationals or a finite field.
  Returns a random non-minimal Kodaira dimension 1 surface in P from a family with
  degree 10 and sectional genus 10. If the Check parameter is set to false,
  doesn't check the result for non-singularity or irreducibility.}

    K := BaseRing(P);
    require IsAmbient(P) and IsOrdinaryProjective(P) and
	(Dimension(P) eq 4) and (ISA(Type(K),FldRat) or
	  ISA(Type(K),FldFin)):
	"P must be 4-dimensional projective space over the rationals",
	"or a finite field";
    R := CoordinateRing(P);

    // construct the space of dual homs between G=3R+Omega^1(1) and
    // F = 2R(-1)+Omega^3(3)
    Ko := KoszulComplex(R);
    M2 := Matrix(BoundaryMap(Ko,2)); //10x5
    M3 := Matrix(BoundaryMap(Ko,3)); //10x10
    M5 := Matrix(BoundaryMap(Ko,5)); //1x5

    U := DiagonalJoin(IdentityMatrix(R,3),Transpose(M2));
    V := DiagonalJoin(ZeroMatrix(R,2,2),Transpose(M5));
    B := mat_space(U,V);
    wts := get_weights(B,[1,1,1] cat [0 : i in [1..10]],[0 : i in [1..7]]);
    // wts should all be 0 or -1
    inds := [i : i in [1..#wts] | wts[i] le 0];
    ga := VerticalJoin(ZeroMatrix(R,3,10),Transpose(M3));   

    tries := 0;
    while tries lt 10 do
      mat := &+[((wts[i] eq 0) select R!MyRandom(K,RndP)
	else Random(1,R,RndP))*B[i] : i in inds];
      MK := HorizontalJoin(mat,ga);
      F := Module(R,[1 : i in [1..7]] cat [0 : i in [1..10]]);
      Mrel := sub<F|[F!r : r in RowSequence(MK)]>;
      S := SyzygyModule(Mrel);
      B1 := MinimalBasis(S);
      if #B1 ne 1 then continue; end if;
      I := ideal<R|Eltseq(B1[1])>;
      if Check then
        if not IsPrime(I) then continue; end if;
      end if;
      X := Surface(P,MinimalBasis(I) : Check := false, Saturated := true);
      if Check then
	if IsSingular(X) then continue; end if;
      end if;
      return X;	
    end while;
    error "Failed to generate non-singular surface in 10 tries.";
    // res := MinimalFreeResolution(QuotientModule(I))
    //  should have betti resolution
    //[ 1  0  0  0  0]
    //[ 0  0  0  0  0]
    //[ 0  0  0  0  0]
    //[ 0  3  0  0  0]
    //[ 0  3  9  5  1]
    
end intrinsic;
