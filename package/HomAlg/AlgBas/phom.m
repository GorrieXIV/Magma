freeze;

SpaceOfMatrices := function(lst);

rr := Nrows(lst[1]);
cc := Ncols(lst[1]);
ff := Parent(CoefficientRing(lst[1]));
V,inn,ppj := DirectSum([VectorSpace(ff,rr):i in [1 .. cc]]);
www := sub<V|[&+[inn[j](lst[i][j]):j in [1 .. cc]]: i in [1 .. #lst]]>;
return www, [Parent(lst[1])!xx:xx in Basis(www)];

end function;

intrinsic PHom(M::ModAlgBas,N::ModAlgBas) -> ModMatFld
{Finds the space of projective homomorphisms from M to N.}

P,theta := ProjectiveCover(N);
homMP := AHom(M,P);
homMN := AHom(M,N);
sss := sub<homMN|[homMP.i*theta:i in [1 .. Dimension(homMP)]]>;
return sss;

end intrinsic;

