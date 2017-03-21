freeze;

declare attributes AlgBas: RightRegularModule;

ListSummandIndices := function(alst);

nll := [];
for i := 1 to #alst do
if alst[i] ne 0 then
n:= alst[i];
nll := nll cat [i:j in [1 .. n]];
end if;
end for;
return nll;

end function;

intrinsic MapToMatrix(theta::Map) -> ModMatFldElt 
{The matrix representing the map theta}
   l, A := HasMatrix(theta);
   if l then
    return A;
   end if;

   vv1 := Domain(theta);
   vv2 := Codomain(theta);
   return Hom(vv1,vv2)!Matrix(theta(Basis(vv1)));

   /*
   mat := RMatrixSpace(vv1,vv2)!0;
   for i := 1 to Nrows(mat) do
       mat[i] := RSpace(CoefficientRing(vv1),Ncols(mat))!theta(Basis(vv1)[i]);
   end for;
   return mat;
   */

//"vv1:", vv1;

"vv1:", vv1;
"vv2:", vv2;
   l, A := HasMatrix(theta);
l;

   time mat := RMatrixSpace(vv1,vv2)!Matrix(theta(Basis(vv1)));
   assert not l or mat eq A;

   return mat;

end intrinsic;
			// Note: This function should be standard in magma.


intrinsic JacobsonRadicalAlgBas(M::ModAlgBas) -> ModAlgBas
{The Jacobson radical of M}
    /*
    UU := &+[RowSpace(Action(M).i):i in 
	       [NumberOfProjectives(Algebra(M))+1 .. Ngens(Algebra(M))]];
    J, phi := sub<M|Basis(UU)>;
    */

    if Dimension(M) eq 0 then return M, Coercion(M, M); end if;

//"Get RS gens"; time
    L := [ActionGenerator(M, i):
	i in [NumberOfProjectives(Algebra(M))+1 .. Ngens(Algebra(M))]];

    if #L eq 0 then
	J, phi := sub<M|>;
    else
	UU := RowSpace(VerticalJoin(L));
	J, phi := sub<M|Basis(UU)>;
    end if;
    return J, phi;
end intrinsic;

intrinsic LiftHomomorphism(x::ModAlgBasElt, n::RngIntElt) -> ModMatFldElt
{Given an element  x in a module over a basic algebra, creates the homomorphism
from the nth projective module for the algebra to the module with the property
that the idempotent e of the projective module maps to x*e}

mmd := Parent(x);
alg := Algebra(mmd);
pmod := ProjectiveModule(alg,n);
ff := BaseRing(alg);
hhh := RMatrixSpace(pmod, mmd)!0;
te := PathTree(alg,n);
hhh[1] := VectorSpace(ff,Dimension(mmd))!x*Action(mmd).te[1][2];
if #te gt 1 then
//"#te:", #te; "te:", {* t[2]: t in te *}; mmd; time
    V := VectorSpace(ff,Dimension(mmd));
    for j := 2 to #te do
	hhh[j] := V!hhh[te[j][1]]*Action(mmd).te[j][2];
    end for;
end if;
return hhh;

end intrinsic;

intrinsic ProjectiveModule(A::AlgBas,S::SeqEnum) -> ModAlgBas, SeqEnum, SeqEnum
{Given a sequence S = [s_1,s_2, ... ], the function returns a projective 
module which is the direct sum of s_1 copies
of the first projective of the algebra A, s_2 copies of the second,
etc.  It also returns the sequences of inclusions and projections
onto the incecomposable projecitves.}

   T := [];
   for i := 1 to #S do
   if S[i] ne 0 then
   T := T cat [ProjectiveModule(A,i):j in [1 .. S[i]]];
   end if;
   end for;
   DS,ilst,plst := DirectSum(T);
   return DS,ilst,plst;

end intrinsic;

intrinsic LiftHomomorphism(X::SeqEnum, N::SeqEnum) -> ModMatFldElt
{Given an sequence X of elements in a module over a basic algebra
and a sequence N of nonnegative integers, the function creates the 
homomorphism from the projective module that is a direct sum of N[i]
copies of the ith projective module for the algebra to the module of X
with the property that the idempotent e of the projective module maps 
to X[i]*e.}

mmd := Parent(X[1]);
alg := Algebra(mmd);
pmod,inc,prj := ProjectiveModule(alg,N);
a := ListSummandIndices(N);
hhh := &+[RMatrixSpace(pmod,mmd)!(MapToMatrix(prj[t])*
	LiftHomomorphism(X[t],a[t])):t in [1..#a]];
return hhh;

end intrinsic;

intrinsic ProjectiveCover(M::ModAlgBas) -> 
		ModAlgBas, ModMatFldElt, SeqEnum, SeqEnum, SeqEnum
{The projective cover of M given as the projective module P, the 
surjective homomorphism of P onto M, the sequences of inclusion 
and projection homomorphism of P from and to its indecomposable
direct summands and the isomorphism type of P in the form of a list 
of the number of copies of the projective modules of algebra of
each type that make up P.} 

    alg := Algebra(M);
    radm := JacobsonRadical(M);		
    qqq, theta := quo<M|radm>;
    corad := [];
    for i := 1 to NumberOfProjectives(alg) do
    bbb := Basis(RowSpace(Action(qqq).i));
    if bbb ne [] then
    bbb := [<i,x@@theta>: x in bbb];
    corad := corad cat bbb;
    end if;
    end for;
    ncr := [#[x:x in corad|x[1] eq i]:i in [1 .. NumberOfProjectives(alg)]];
    pmlst := [];
    for i := 1 to NumberOfProjectives(alg) do
    if ncr[i] ne 0 then
    pmlst := pmlst cat [<i,ProjectiveModule(alg,i)>: j in [1 .. ncr[i]]];
    end if;
    end for;
    corad1 := [corad[i][2]: i in [1 .. #corad]];
    proj,incl,prjl := DirectSum([pmlst[i][2]: i in [1 .. #pmlst]]);
    gamma := &+[MapToMatrix(prjl[i])*
	LiftHomomorphism(corad1[i],pmlst[i][1]):i in [1 .. #corad1]];
    ggg := hom<proj -> M| gamma>;       	// should not be necessary
    gamma := MapToMatrix(ggg);      	 	// should not be necessary

return proj, gamma, incl, prjl,ncr;

end intrinsic;

intrinsic IsProjective(M::ModAlgBas) -> BoolElt, SeqEnum
{Returns true if the module is projective and returns a list of how many 
projective modules of each type are direct summands of the projective cover
of the module.}

   alg := Algebra(M);
   n := NumberOfProjectives(alg);
   rad := JacobsonRadical(M);
   qqq := quo<M|rad>;
   ccr := [Dimension(RowSpace(Action(qqq).i)):i in [1 .. n]];
   if Dimension(M) eq 
	&+[ccr[j]*Dimension(ProjectiveModule(alg,j)):j in [1..n]] then 
   flag := true;
   else 
   flag := false;
   end if;
   return flag,ccr;
   
end intrinsic;

intrinsic IsInjective(M::ModAlgBas) -> BoolElt, SeqEnum
{Returns true if the module is injective and returns a list of how many 
injective modules of each type are direct summands of the injective hull
of the module.}

   DM := Dual(M);
   a,b := IsProjective(DM);
   return a,b;

end intrinsic;

intrinsic Pushout(D::ModAlgBas, fc1::ModMatFldElt, M1::ModAlgBas, 	
	fc2::ModMatFldElt, M2::ModAlgBas) -> ModAlgBas, ModMatFldElt, ModMatFldElt
{Returns the pushout of the diagram [ M1 <-- fc1 -- D  --- fc2 --> M1 ]
as an AModule together with homomorphisms from M1 and M2}

   mdd, incl := DirectSum([M1,M2]);
	f1 := hom<D -> M1| fc1>;
	f2 := hom<D -> M2| fc2>;
   qqq, theta := quo<mdd|[incl[1](f1(x)) - incl[2](f2(x)):x in Basis(D)]>;
   phi1 := MapToMatrix(incl[1]*theta);
   phi2 := MapToMatrix(incl[2]*theta);
   return qqq, phi1,phi2;

end intrinsic;

intrinsic Pullback(M1::ModAlgBas, fc1::ModMatFldElt, M2::ModAlgBas,
	fc2::ModMatFldElt, N::ModAlgBas) -> ModAlgBas, ModMatFldElt, ModMatFldElt
{Returns the pullback of the diagram [ M1 -- fc1 --> N <-- fc2 -- M2 ]
as an AModule together with homomorphisms to M1 and M2.}

    mdd, incl, prjl := DirectSum([M1,M2]);
    uuu := Kernel(MapToMatrix(prjl[1])*fc1 - MapToMatrix(prjl[2])*fc2);
    sss, rho := sub<mdd|uuu>;
    phi1 := rho*prjl[1];
    phi2 := rho*prjl[2];
	f1 := MapToMatrix(phi1);
	f2 := MapToMatrix(phi2);
   return sss, f1, f2;

end intrinsic;

intrinsic IrreducibleModule(A::AlgBas, n::RngIntElt) -> ModAlgBas
{The nth irreducible module of the algebra. The module is the
quotient of the nth projective module by its radical.}

   ff := BaseRing(A);
   mlst := [MatrixAlgebra(ff,1)!0:i in [1 .. Ngens(A)]];
   mlst[n] := MatrixAlgebra(ff,1)!1;
   mdd := AModule(A,mlst);
   return mdd;

end intrinsic;

intrinsic SimpleModule(A::AlgBas, n::RngIntElt) -> ModAlgBas
{The nth irreducible module of the algebra. The module is the
quotient of the nth projective module by its radical.}

   ff := BaseRing(A);
   mlst := [MatrixAlgebra(ff,1)!0:i in [1 .. Ngens(A)]];
   mlst[n] := MatrixAlgebra(ff,1)!1;
   mdd := AModule(A,mlst);
   return mdd;

end intrinsic;

intrinsic RegularRepresentation(v::AlgBasElt) -> AlgMatElt
{If $v$ is an element of a basic algebra given as a vector in the 
underlying space, then the function computes the matrix of the action 
by right multiplication of the element on the algebra.}

   alg := Parent(v);
   vvv := VectorSpace(alg);
   mmm := MatrixAlgebra(BaseRing(alg),Dimension(vvv))!0;
   BB := Basis(vvv);
   for i := 1 to Dimension(vvv) do
   mmm[i] := vvv!((alg!BB[i])*v);
   end for;
   return mmm;

end intrinsic;

intrinsic RightRegularModule(A::AlgBas) -> ModAlgBas
{Tht algebra $A$ as a right module over itself. 
The module is the direct sum of the projectives modules 
of $A$.}

if assigned A`RightRegularModule then
	return A`RightRegularModule;
end if;

mm := DirectSum([ProjectiveModule(A,i)
	:i in [1 .. NumberOfProjectives(A)]]); 
A`RightRegularModule := mm;

	   return mm;

end intrinsic;


intrinsic DimensionsOfProjectiveModules(A::AlgBas) -> SeqEnum
{The sequence of the dimensions of the projective modules 
of the basic algebra $A$.}

   aa := [Dimension(ProjectiveModule(A,i)):
	i in [1 .. NumberOfProjectives(A)]];
   return aa;

end intrinsic;

intrinsic DimensionsOfInjectiveModules(A::AlgBas) -> SeqEnum
{The sequence of the dimensions of the injective modules 
of the basic algebra $A$.}

   n := NumberOfProjectives(A);
   aa := [&+[Rank(Action(ProjectiveModule(A,i)).j):
	i in [1 .. n]]:j in [1 .. n]];
   return aa;

end intrinsic;

intrinsic IsSemisimple(M::ModAlgBas) -> BoolElt, SeqEnum
{True if the module M is a semisimple module and false otherwise. 
If true, then the function also returns a list of the ranks of the 
primitive idempotents of the algebra. This is also a list of the 
multiplicities of the simple modules of the algebra as composition 
factors in a composition series for the module.}

   n := NumberOfProjectives(Algebra(M));
   m := Ngens(Algebra(M));
   aa := [Rank(Action(M).i):i in [1 .. n]];
   bb := [Rank(Action(M).i):i in [n+1 .. m]];
   flag := true;
   if &+bb ne 0 then
   flag := false;
   end if;
   return flag,aa;

end intrinsic;

intrinsic IsModuleHomomorphism(f::ModMatFldElt) -> BoolElt
{True if the map f is a homomorphism of modules over the algebra.}

   flag := true;
   M := Domain(f);
   N := Codomain(f);
   AM := Action(M);
   AN := Action(N);
   require Ngens(AM) eq Ngens(AN):
       "Actions of domain and codomain incompatible";
   for i := 1 to Ngens(AM) do
   if AM.i*f ne f*AN.i then
   flag := false;
   break;
   end if;
   end for;
   return flag;

end intrinsic;









