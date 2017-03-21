freeze;

intrinsic BinaryForms(N::[RngIntElt], p::RngIntElt: GL := false)
    -> RngMPol, Mtrx, RngMPol
{The action on a direct sum of spaces of binary forms of the degrees given in
N, in characteristic p (p may be 0)}

/*
Define G = SL_2(K) with K algebraically closed of char. p, p = 0 okay.
Define the action on a direct sum of spaces of binary forms of degree n_i.
N is the list of the n_i.
Return three items: the ideal I_G, the matrix A (as a list of lists),
and a polynomial ring on which G acts with appropriate naming of variables.
*/

    if Type(N) eq RngIntElt then L:=[N]; else L:=N; end if;
    requirege p, 0;
    if p gt 0 then
	require IsPrime(p): "Argument 2 is not prime";
	K:=GF(p);
    else
	K:=Rationals();
    end if;
    if not GL then
        P:=PolynomialRing(K,4);
        AssignNames(~P,["t1","t2","t3","t4"]);
        IG := ideal<P | [P.1*P.4-P.2*P.3-1]>;
    else
        P:=PolynomialRing(K,5);
        AssignNames(~P,["t1","t2","t3","t4","d"]);
        IG := ideal<P | [P.5*(P.1*P.4-P.2*P.3)-1]>;
    end if;
    Px := PolynomialRing(P,2);
    phi:=hom<Px->Px | [P.4*Px.1-P.2*Px.2,-P.3*Px.1+P.1*Px.2]>;
    A:=MatrixAlgebra(P,#L + &+L)!0;
    n0:=0;
    for n in L do
        M := MonomialsOfDegree(Px,n);
        SM:=[phi(g): g in M];
        for i:=1 to #M do for j:=1 to #M do
            A[n0+i,n0+j]:=MonomialCoefficient(SM[j],M[i]);
        end for; end for;
        n0 +:= n+1;
    end for;
    A:=Matrix([[A[i,j]: j in [1..n0]]: i in [1..n0]]);
    P:=PolynomialRing(K,n0);
    if #L eq 1 then
        AssignNames(~P,["x"*IntegerToString(i): i in [0..L[1]]]);
    else
        AssignNames(~P,&cat[["x"*IntegerToString(i)*IntegerToString(j):
            j in [0..L[i]]]: i in [1..#L]]);
    end if;
    return IG,A,P;

end intrinsic;

intrinsic BinaryForms(n::RngIntElt, p::RngIntElt: GL := false)
    -> RngMPol, Mtrx, RngMPol
{The action on a direct sum of spaces of binary forms of degree n,
in characteristic p (p may be 0)}

    return BinaryForms([n], p: GL := GL);

end intrinsic;
