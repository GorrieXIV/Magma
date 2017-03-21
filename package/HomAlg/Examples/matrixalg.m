freeze;

//  Jon F. Carlson, 2008, revised June 2012

//********************************************************************

intrinsic BasicAlgebra(A::AlgMat: Rand := 0) -> AlgBas
{Returns the split basic algebra of the matrix algebra A. In the 
event that the field of coefficients of A is not a splitting field for A, 
then the returned basic algebra is defined over the minimal extension 
that is a splitting field.}

  if assigned A`BasicAlgebra then
      return A`BasicAlgebra;
  end if;
  F := CoefficientRing(A);
  t := Cputime(0);
  B := CondensedAlgebra(A: Rand := Rand);
//  printf "In BasicAlgebra time for CondensedAlgebra(A) is %o.\n", Cputime(t);
  sqa := SimpleQuotientAlgebras(B);
  deg := LCM(sqa`DegreesOfCenters);
  if deg gt 1 then
     K := GF(#F^deg);
     B := ExtendField(B, K);
     t := Cputime(0);
     B := CondensedAlgebra(B: Rand := Rand);
  end if;
  K := CoefficientRing(B);
  t := Cputime(0);
  P, I, phi  := Presentation(B);
  CE := MatrixAlgebra<K,Nrows(phi(I.1))|[phi(I.j): j in [1 .. Rank(P)]]>;	
  nigx := #SimpleQuotientAlgebras(CE)`DegreesOverCenters;
  corx := [[j : j in K|P.i^2 - j*P.i in I][1]:i in [1 .. nigx]];
  PP := FreeAlgebra(K, Rank(P));
  theta := hom<P -> PP|[corx[i]*PP.i: i in [1 .. #corx]]
               cat [PP.i: i in [#corx+1 .. Rank(PP)]]>;
  II := ideal<PP|[theta(x): x in Basis(I)]>;
  t := Cputime(0);
  Groebner(II);
  vertxlst :=
  [<[i: i in [1 .. nigx]|CE.i*CE.(j+nigx) eq corx[i]*CE.(j+nigx)][1],
      [i: i in [1 .. nigx]|CE.(j+nigx)*CE.i eq corx[i]*CE.(j+nigx)][1]>:
                  j in [1 .. Rank(PP)-nigx]];
  BA := BasicAlgebra(PP,Basis(II),nigx,vertxlst);
  A`BasicAlgebra := BA;

  return BA;

end intrinsic;

//***********************************************************************

intrinsic BasicAlgebraOfMatrixAlgebra(A::AlgMat) -> AlgBas
{Returns the split basic algebra of the matrix algebra A. In the
event that the field of coefficients of A is not a splitting field for A,
then the returned basic algebra is defined over the minimal extension
that is a splitting field.}

return BasicAlgebra(A);

end intrinsic;


//***********************************************************************

intrinsic BasicAlgebraOfGroupAlgebra(G::GrpPerm, F::FldFin) -> AlgBas
{Returns the basic algebra of the group algebra FG. If F is not a splitting
field for the simple FG-modules, then the base ring of the returned 
algebra is the minimal extension of F that is a splitting field for FG. }

prj := ProjectiveIndecomposables(G,F);
A := BasicAlgebra(Action(DirectSum(prj)));

     return ChangeIdempotents(A,Reverse([1 .. NumberOfProjectives(A)]));

end intrinsic;

//***********************************************************************

intrinsic BasicAlgebraOfGroupAlgebra(G::GrpPC, F::FldFin) -> AlgBas
{Returns the basic algebra of the group algebra FG. If F is not a splitting
field for the simple FG-modules, then the base ring of the returned
algebra is the minimal extension of F that is a splitting field for FG.}

prj := ProjectiveIndecomposables(G,F);
A := BasicAlgebra(Action(DirectSum(prj)));

     return ChangeIdempotents(A,Reverse([1 .. NumberOfProjectives(A)]));

end intrinsic;

//***********************************************************************

intrinsic BasicAlgebraOfGroupAlgebra(G::GrpAb, F::FldFin) -> AlgBas
{Returns the basic algebra of the group algebra FG. If F is not a splitting
field for the simple FG-modules, then the base ring of the returned
algebra is the minimal extension of F that is a splitting field for FG.}

prj := ProjectiveIndecomposables(G,F);
A := BasicAlgebra(Action(DirectSum(prj)));

     return ChangeIdempotents(A,Reverse([1 .. NumberOfProjectives(A)]));

end intrinsic;

//**********************************************************************

intrinsic BasicAlgebra(S::SeqEnum: Rand := 0) -> AlgBas
{Returns the basic algebra of the action algebra on the module which is 
the directs sum of the modules in the sequence S. In the event that the 
irreducible composition factors of the modules in S are not absolutely 
irreducible, then the returned basic algebra is defined over the splitting 
field for the irreducible modules.}

        return BasicAlgebra(Action(DirectSum(S)): Rand := 0);

end intrinsic;

//***********************************************************************

intrinsic BasicAlgebraOfBlockAlgebra(S::SeqEnum) -> AlgBas
{Returns the basic algebra of the block algebra, the projective modules
of which are given in the sequence S. In the event that the irreducible
composition factors of the modules in S are not absolutely irreducible,
then the returned basic algebra is defined over the splitting field for
the irreducible modules.}

B := BasicAlgebra(Action(DirectSum(S)));
C := ChangeIdempotents(B, Reverse([1 .. NumberOfProjectives(B)]));

	return C;

end intrinsic;

//*********************************************************************

intrinsic BasicAlgebraOfPrincipalBlock(G::GrpPerm, k::FldFin)
                        -> AlgBas
{Returns the basic algebra of the principal block of the group algebra
of G.  If the simple modules in the principal kG block are all absolutely
simple, then the ordering of the projective modules for the returned
basic algebra is exactly the same as the ordering of the projectives
in the principal block returned by the function IndecomposableProjectives.
Otherwise, the base ring of the returned basic algebra is the least
extension of k, necessary to split the simple modules in the principal
block and the simple modules of the returned algebra are ordered by
increasing dimension of the corresponding simples of kG. }

prj := ProjectiveIndecomposables(G,k);
bks := Blocks(prj);
A := Action(DirectSum(bks[1]));
SQ := SimpleQuotientAlgebras(A);
C := BasicAlgebra(A);
if BaseRing(C) eq BaseRing(A) then
   U := [quo<x|JacobsonRadical(x)>: x in bks[1]];
   algs := [Codomain(f): f in SQ`SimpleQuotients];
   nord := [[i: i in [1 .. #algs]|
         IsIsomorphic(RModule(algs[i]), U[j])][1]: j in [1 .. #algs]];
   B := ChangeIdempotents(C,nord);
else
   B := ChangeIdempotents(C, Reverse([1 .. NumberOfProjectives(C)]));
end if;

        return B;

end intrinsic;
