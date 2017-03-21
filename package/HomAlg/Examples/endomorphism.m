freeze;

MinimalGeneratingSetA := function(A);
// A must be a matrix algebra

n := 2;
r := Dimension(A);
flag := true;
B := A;
while flag do
n := n+1;
for j := 1 to 3 do
   B := MatrixAlgebra<CoefficientRing(A), Nrows(A.1)|
		      [Random(A): i in [1 ..n]]>;
   if Dimension(B) eq r
       then flag := false;
       return B;
       break;
   end if;
end for;
end while;

return B;

end function;

//********************************************************************

intrinsic BasicAlgebraOfEndomorphismAlgebra(M::ModRng) -> AlgBas
{Returns the split basic algebra of the endomorphism ring of the 
modules M. If the field of coefficients of M is not a splitting field 
for M, then the returned basic algebra is defined over the minimal 
extension that is a splitting field.}

A := Action(M);
F := CoefficientRing(A);
B := CondensedAlgebra(A);
N := RModule(B);
E := AHom(N,N);
TE := MatrixAlgebra<F,Nrows(E.1)|[E.i: i in [1 .. Ngens(E)]]>;
TE := MinimalGeneratingSetA(TE);
sqa := SimpleQuotientAlgebras(TE);
deg := LCM(sqa`DegreesOfCenters);
if deg gt 1 then
   K := GF(#F^deg);
   TE := ExtendField(TE,K);
end if;
K := CoefficientRing(TE);
p := #K;
EE := CondensedAlgebra(TE);
P, I, phi  := Presentation(EE);
CE := MatrixAlgebra<K,Nrows(phi(I.1))|[phi(I.j): j in [1 .. Rank(P)]]>;	
nigx := #SimpleQuotientAlgebras(CE)`DegreesOverCenters;
corx := [[j : j in K|P.i^2 - j*P.i in I][1]:i in [1 .. nigx]];
PP := FreeAlgebra(K, Rank(P));
theta := hom<P -> PP|[corx[i]*PP.i: i in [1 .. #corx]]
               cat [PP.i: i in [#corx+1 .. Rank(PP)]]>;
II := ideal<PP|[theta(x): x in Basis(I)]>;
Groebner(II);
vertxlst :=
  [<[i: i in [1 .. nigx]|CE.i*CE.(j+nigx) eq corx[i]*CE.(j+nigx)][1],
      [i: i in [1 .. nigx]|CE.(j+nigx)*CE.i eq corx[i]*CE.(j+nigx)][1]>:
                  j in [1 .. Rank(PP)-nigx]];
BA := BasicAlgebra(PP,Basis(II),nigx,vertxlst);

          return BA;

end intrinsic;

//***********************************************************************

intrinsic BasicAlgebraOfHeckeAlgebra(G::GrpPerm, H::GrpPerm, F::FldFin) ->
AlgBas 
{Returns the basic algebra of the Hecke algebra which is the algebra of 
endomorphisms of the permutation module over G with point stabilizer H 
and field of coefficients F. In the event that F is not a splitting field
then the returned basic algebra is defined over the minimal extension 
of F that is a splitting field.}


M := PermutationModule(G, H, F);
BA := BasicAlgebraOfEndomorphismAlgebra(M);

     return BA;

end intrinsic;

//*********************************************************************

intrinsic BasicAlgebraOfHeckeAlgebra(G::GrpPC, H::GrpPC, F::FldFin) ->
AlgBas 
{Returns the basic algebra of the Hecke algebra which is the algebra of 
endomorphisms of the permutation module over G with point stabilizer H 
and field of coefficients F. In the event that F is not a splitting field
then returned basic algebra is defined over the minimal extension 
of F that is a splitting field.}


M := PermutationModule(G, H, F);
BA := BasicAlgebraOfEndomorphismAlgebra(M);

     return BA;

end intrinsic;

//**********************************************************************

intrinsic BasicAlgebraOfHeckeAlgebra(G::GrpAb, H::GrpAb, F::FldFin) ->
AlgBas 
{Returns the basic algebra of the Hecke algebra which is the algebra of 
endomorphisms of the permutation module over G with point stabilizer H 
and field of coefficients F. In the event that F is not a splitting field
then the returned basic algebra is defined over the minimal extension 
of F that is a splitting field.}


M := PermutationModule(G, H, F);
BA := BasicAlgebraOfEndomorphismAlgebra(M);

     return BA;

end intrinsic;


//***********************************************************************

intrinsic BasicAlgebraOfSchurAlgebra(n::RngIntElt,r::RngIntElt,F::FldFin) 
        -> AlgBas
{Creates the basic algebra of the schur algebra S(n,r) over the field F.
The Schur algebra is the algebra of endomorphisms of module over the 
symmetric group Sym(r) that is the tensor product of r copies of a 
vector space V over F of dimension n, the group Sym(r) acting by permuting 
the copies.}


xxx := [x:x in Partitions(r)|#x le n];
p := Characteristic(F);
k := GF(p);
M := DirectSum([PermutationModule(Sym(r),
                                  YoungSubgroup(x),GF(p)):x in xxx]);
A := Action(M);
p := Characteristic(k);
B := CondensedAlgebra(A);
N := RModule(B);
E := AHom(N,N);
TE := MatrixAlgebra<GF(p),Nrows(E.1)|[E.i: i in [1 .. Ngens(E)]]>;
TE := MinimalGeneratingSetA(TE);
EE := CondensedAlgebra(TE);
P, I, phi  := Presentation(EE);
CE := MatrixAlgebra<GF(p),Nrows(phi(I.1))|[phi(I.j): j in [1 .. Rank(P)]]>;
nigx := #SimpleQuotientAlgebras(CE)`DegreesOverCenters;
corx := [[j : j in [1 .. p-1]|P.i^2 - j*P.i in I][1]:i in [1 .. nigx]];
PP := FreeAlgebra(k, Rank(P));
theta := hom<P -> PP|[corx[i]*PP.i: i in [1 .. #corx]]
               cat [PP.i: i in [#corx+1 .. Rank(PP)]]>;
II := ideal<PP|[theta(x): x in Basis(I)]>;
Groebner(II);
vertxlst :=
    [<[i: i in [1 .. nigx]|CE.i^(p-1)*CE.(j+nigx) eq CE.(j+nigx)][1],
      [i: i in [1 .. nigx]|CE.(j+nigx)*CE.i^(p-1) eq CE.(j+nigx)][1]>:
                  j in [1 .. Rank(PP)-nigx]];
BA := BasicAlgebra(PP,Basis(II),nigx,vertxlst);
if k ne F then
   BA := ChangeRing(BA,F);
end if;

          return BA;

end intrinsic;
