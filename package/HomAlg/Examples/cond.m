freeze;

intrinsic BasicAlgebraFG(G::GrpPerm, F::FldFin) -> AlgBas
{Returns the basic algebra of the group algebra FG.}

p := Characteristic(F);
prj := ProjectiveIndecomposables(G,GF(p));
A:= Action(DirectSum(prj));
SS := SimpleQuotientAlgebras(A, [quo<x|JacobsonRadical(x)>:x in prj]);
B := CondensedAlgebra(A);
SSS := CondensedAlgebraSimpleModules(A,B);
if Maximum(SS`DegreesOfCenters) eq 1 then
   EE := B;
   SS := SimpleQuotientAlgebras(EE,SSS);
   K := GF(p);
else
   K := GF(p^LCM(SS`DegreesOfCenters));
   EE := ExtendField(B,K);
   SS := SimpleQuotientAlgebras(EE,
                 &cat[CompositionFactors(ExtendField(x,K)):x in SSS]);
end if;
P, I, phi  := Presentation(EE);
CEE := MatrixAlgebra(K,Nrows(phi(I.1)));
CE := sub<CEE|[phi(I.j): j in [1 .. Rank(P)]]>;
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
if not F subset K then
   L := GF(p^(LCM(Factorization(#F)[1][2],Factorization(#K)[1][2])));
   BA := ExtendField(BA,L);
end if;

A`BasicAlgebra := BA;

return BA;

end intrinsic;

