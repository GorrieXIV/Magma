freeze;
 
/*
Jon Carlson.
Installed by Allan Steel, July 2003.
*/

ListMonomials := function(A, B, I);
// A is the beginning list, B is the list of variables that we will
// multiply times the elements of A and I is the filter, the ideal
// of elements that we are not interested in.

    N := {@ x*y: x in A,y in B|x*y notin I @}
		join {@ y*x: x in A,y in B|y*x notin I @};

    return N;

end function;

ListGradedMonomialBasis := function(F,I,n);

    II := LeadingMonomialIdeal(I);
    AM := {@ F.i: i in [1 .. Rank(F)] @};
    BM := AM;
    if n gt 1 then 
    for j := 2 to n do   
     BM := ListMonomials(BM, AM, II);
    end for;
    end if;

    return BM;

end function;

ExteriorAlgebra := function(R,n);

    F := FreeAlgebra(R,n);
    if n eq 1 then 
    rel := [F.1^2];
    else 
    rel := [F.i*F.j+F.j*F.i:i in [2 .. n], j in [1 .. n-1]|i gt j]
	      cat [F.i^2: i in [1 ..n]];
    end if;
    I := ideal<F|rel>;

    return F,I;

end function;


ActionOnGradedModule := function(F,I,r,M);

    n := Nrows(M);
    theta := hom<F -> F|[&+[F.i*M[j,i]:i in [1 .. n]]:j in [1 .. n]]>;
    Wn := ListGradedMonomialBasis(F,I,r);
    // Wn := [x:x in W|Degree(x) eq r]; 
    V := VectorSpace(BaseRing(F),#Wn);
    B := Basis(V);
    M := Matrix(BaseRing(F),#Wn,#Wn, [0:i in [1 .. #Wn^2]]);
    for i := 1 to #Wn do 
     w := NormalForm(theta(Wn[i]),I);
    U := Monomials(w);
    v := Coefficients(w);
     M[i] := &+[V|v[j]*B[Index(Wn,U[j])]:j in [1 .. #U]];
    end for;

    return M;

end function;

							       
intrinsic ExteriorPower(A::AlgMatElt, n::RngIntElt) -> ModGrp
{The n-th exterior power of A}

    ff := BaseRing(Parent(A));
    r := Nrows(A);
    F, I := ExteriorAlgebra(ff,r);
    return ActionOnGradedModule(F,I,n, A);

end intrinsic;


intrinsic ExteriorPower(M::ModGrp, n::RngIntElt) -> ModGrp
{The n-th exterior power of M}

    ff := BaseRing(M);
    G := Group(M);
    r := Dimension(M);
    F, I := ExteriorAlgebra(ff,r);
    L := [ActionOnGradedModule(F,I,n, ActionGenerator(M,i)): i in [1 .. Ngens(G\
									      )]];
    MM := GModule(G,L);

    return MM;

end intrinsic;


intrinsic ExteriorPowerNaturalModule(G::Grp, n::RngIntElt) -> ModGrp
{The natural module of the n-th exterior power of G}

    ff := BaseRing(G);
    r := Nrows(G.1);
    F, I := ExteriorAlgebra(ff,r);
    L := [ActionOnGradedModule(F,I,n,G.i): i in [1 .. Ngens(G)]];
    M := GModule(G,L);

    return M;

end intrinsic;


intrinsic SubspaceOfExteriorPower(M::ModGrp, S::SeqEnum, r::RngIntElt)
		-> SeqEnum
{Returns a basis for the subspace Lambda^r(SS) in \Lambda^r(M) where 
SS is the subspace of M with basis S.}

   k := BaseRing(M);
   n := Dimension(M);
   m := #S;
   F, I := ExteriorAlgebra(k,n);
   G, J := ExteriorAlgebra(k,m);
   mu := hom<G -> F | [&+[u[i]*F.i: i in [1 .. n]]: u in S]>;
   WG := ListGradedMonomialBasis(G,J,r);
   WF := ListGradedMonomialBasis(F,I,r);
   NS := [];
   V := VectorSpace(k,#WF);
   B := Basis(V);
   for x in WG do
      w := NormalForm(mu(x),I);
      mons := Monomials(w);
      coes := Coefficients(w);
      Append(~NS, &+[V|coes[j]*B[Index(WF,mons[j])]:j in [1 .. #mons]]);
   end for;

	return NS;

end intrinsic;


