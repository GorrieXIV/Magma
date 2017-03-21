freeze;

declare attributes AlgBas: NonIdempotentGenerators,IdempotentGenerators ;

intrinsic IdempotentGenerators(B::AlgBas) -> []
{Returns the sequence of idempotent generators of B.}
alg := B;
ppt := [1] cat [Dimension(ProjectiveModule(alg,i)):
        i in [1 .. NumberOfProjectives(alg)]];
pptt := [&+[ppt[j]: j in [1 .. i]]:i in [1 .. #ppt-1]];
blst := [alg!Basis(VectorSpace(alg))[pptt[i]]:i in [1 .. #pptt]];
B`IdempotentGenerators := blst;

	return blst;

end intrinsic;
 
////////////////////////////////////////////////////////////////////

intrinsic NonIdempotentGenerators(B::AlgBas) -> []
{Returns the sequence of nonidempotent generators of the algebra B.}
    alg := B;
    n := NumberOfProjectives(alg);
    s := Ngens(alg);
    if s eq n  then return [];
    end if;
    bl := [];
    PL := [ProjectiveModule(alg,i): i in [ 1 .. n]];
    V, ij, pr := DirectSum(PL);
    for j := n+1 to s do
       bl[j-n] := B!VectorSpace(B)!&+[ij[i]((Action(PL[i]).j)[1]):
                   i  in [1 .. n]];
    end for;
    B`NonIdempotentGenerators := bl;

              return bl;

end intrinsic;

////////////////////////////////////////////////////////////////////////
 
intrinsic Generators(B::AlgBas) -> []
{Returns the sequence of generators of B.}
alg := B;
blst := IdempotentGenerators(alg) cat NonIdempotentGenerators(alg);
return blst;
end intrinsic;

///////////////////////////////////////////////////////////////////////

intrinsic Basis(B::AlgBas) -> []
{Returns the standard basis of B.}
    return [B ! v: v in Basis(VectorSpace(B))];
end intrinsic;

//////////////////////////////////////////////////////////////////////

intrinsic IdempotentPositions(B::AlgBas) -> []
{The index positions of the projective modules of B.}
    alg := B;
    ppt := [1] cat [Dimension(ProjectiveModule(alg,i)):
	    i in [1 .. NumberOfProjectives(alg)]];
    pptt := [&+[ppt[j]: j in [1 .. i]]:i in [1 .. #ppt-1]];
    return pptt;
end intrinsic;

/////////////////////////////////////////////////////////////////////


intrinsic GeneratorAssociatedIdempotents(A::AlgBas) -> SeqEnum
{Returns a sequence of pairs of integers such that the j-th
element is the unique pair <u,v> such that e_u*x_j*e_v = x_j
where x_j is the j-th generator of the algebra A and e_u, e_v
are the u-th and v-th idempotent generators of A.}

nproj := NumberOfProjectives(A);
S := [PathTree(A,i): i in [1 .. nproj]];
T := [[y[2]: y in x|y[1] eq 1]: x in S];
left := [[i : i in [1 .. nproj]| j in T[i]][1]:j in [1 .. Ngens(A)]];
GG := Generators(A);
right := [1 .. nproj];
for j := nproj+1 to #GG do
   for l := 1 to nproj do
     if GG[j]*GG[l] eq GG[j] then
        Append(~right, l);
        break l;
     end if;
  end for;
end for;

        return [<left[i],right[i]>: i in [1 .. #GG]];

end intrinsic;

/////////////////////////////////////////////////////////////////////

intrinsic PositionsOfGenerators(A::AlgBas) -> SeqEnum
{Returns the sequence N = [n_1, ..., n_s] such that
A.n_1, ..., A.n_s are the generators of the algebra A.}

np := NumberOfProjectives(A);
PT := &cat[PathTree(A,i): i in [1 .. np]];
loc := [[j : j in [1 .. #PT]|PT[j][2] eq i and PT[j][1] eq 1][1]:
        i in [1 .. #Generators(A)]];

        return loc;

end intrinsic;

/////////////////////////////////////////////////////////////////////

intrinsic IsUnit(v::AlgBasElt) -> BoolElt
{True if v is a unit.}
    vec := v;
    alg := Parent(vec);
    ppt := [1] cat [Dimension(ProjectiveModule(alg,i)): 
	    i in [1 .. NumberOfProjectives(alg)]];
    pptt := [&+[ppt[j]: j in [1 .. i]]:i in [1 .. #ppt-1]];
    mm := &*[vec[pptt[j]]:j in [1 .. #pptt]];
    if mm ne 0 then 
	    return true;
    else 
	    return false;
    end if;
end intrinsic;

/////////////////////////////////////////////////////////////////

intrinsic IsInvertible(v::AlgBasElt) -> Bool, AlgBasElt
{True if v is a unit and  if so returns the inverse also.}

    A := Parent(v);
    M := Matrix([v*A.i: i in [1 .. Dimension(A)]]);

    hi, s := IsConsistent(M, Vector(A!1));
    if not hi then
	return false, _;
    end if;
    return true, A!s;
end intrinsic;

//////////////////////////////////////////////////////////////////

intrinsic '^'(v::AlgBasElt, n::RngIntElt) -> AlgBasElt
{Returnis v^n.}
    if n eq 0 then
	return Parent(v)!1;
    end if;
    if n lt 0 then
	n := -n;
	hi, v := HasInverse(v);
	require hi: "Argument 1 is not invertible";
    end if;

    w := Parent(v)!1;
    vp := v;
    while n gt 0 do
	if n mod 2 eq 1 then
	    w := w * vp;
	end if;
	vp := vp * vp;
	n := n div 2;
    end while;
    return w;

end intrinsic;

//////////////////////////////////////////////////////////////////

intrinsic ComponentProduct(
    B::AlgBas, a::ModRngElt, b::ModRngElt, i::RngIntElt
) -> ModRngElt
{}
   mmd := Parent(a);

   T := PathTree(B, i);
   Act := Action(mmd);
   x := a*Act.(T[1][2]);
   if IsZero(x) then return x; end if;
 
   alst := [x];
   for k := 2 to #T do
      alst[k] := alst[T[k][1]]*Act.(T[k][2]);
   end for;
   return  &+[b[i]*alst[i]: i in [1.. #T]];
 
end intrinsic;

//////////////////////////////////////////////////////////////////////
 
intrinsic MinimalPolynomial(v::AlgBasElt) -> RngUPolElt
{Return the minimal polynomial of v.}
    B := Parent(v);
    R := BaseRing(B);
    n := Dimension(B);
    Q := [];
    w := B!1;
    for i := 1 to n + 1 do
	Q cat:= Eltseq(w);
	w := w * v;
    end for;
    X := RMatrixSpace(R, n + 1, n) ! Q;
    r := Rank(X);
    s := Solution(Submatrix(X, 1, 1, r, Ncols(X)), X[r + 1]);
    return PolynomialRing(R) ! (Eltseq(-s) cat [1]);
end intrinsic;

/*
intrinsic DirectSum(Q::[AlgBas]) -> AlgBas, [], []
{The direct sum D of the sequence Q of algebras, together with a sequence 
containing the embedding maps from each algebra of Q into D and a 
sequence containing the projection maps from D onto each algebra of Q}

    // Do arg checking...

    B := Parent(v);
    R := BaseRing(B);
    n := Dimension(B);
    Q := [];
    w := B!1;
    for i := 1 to n + 1 do
	Q cat:= Eltseq(w);
	w := w * v;
    end for;
    X := RMatrixSpace(R, n + 1, n) ! Q;
    r := Rank(X);
    s := Solution(Rows(X, 1, r), X[r + 1]);
    return PolynomialRing(R) ! (Eltseq(-s) cat [1]);
end intrinsic;
*/

intrinsic BasicAlgebra(F::FldFin) -> AlgBas
{The field F as a basic algebra over itself};
 
   M := MatrixAlgebra(F,1);
   C := BasicAlgebra([<M,[<1,1>]>]);
   return C;
 
end intrinsic;

/////////////////////////////////////////////////////////////////////

intrinsic Order(B::AlgBas) -> RngIntElt
{The order of the basic algebra B}
    return #BaseRing(B)^Dimension(B);
end intrinsic;

////////////////////////////////////////////////////////////////////

intrinsic '#'(B::AlgBas) -> RngIntElt
{"} // "
    return Order(B);
end intrinsic;

///////////////////////////////////////////////////////////////////

intrinsic PrintMagma(B::AlgBas)
{}
    printf "BasicAlgebra(%m)", 
    [<Action(ProjectiveModule(B,i)),PathTree(B,i)>:
	    i in [1 ..NumberOfProjectives(B)]];
end intrinsic;
