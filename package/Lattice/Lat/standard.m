freeze;

Z := IntegerRing();
Q := RationalField();

intrinsic Lattice(S::MonStgElt, n::RngIntElt) -> Lat
{The standard lattice given by S and n}
    if S eq "A" then
	requirege n, 1;
	B := RMatrixSpace(Z, n, n + 1) ! 0;
	for i := 1 to n do
	    B[i][i] := -1;
	    B[i][i + 1] := 1;
	end for;
	return LatticeWithBasis(B);
    elif S eq "B" then
	requirege n, 1;
	return StandardLattice(n);
    elif S eq "C" then
	return Lattice("D", n);
    elif S eq "D" then
	requirege n, 3;
	B := RMatrixSpace(Z, n, n) ! 0;
	B[1][1] := -1;
	B[1][2] := -1;
	for i := 2 to n do
	    B[i][i - 1] := -1;
	    B[i][i] := 1;
	end for;
	return LatticeWithBasis(B);
    elif S eq "E" then
	require n in [6, 7, 8]: "Argument 2 must be 6, 7, or 8";

	B := RMatrixSpace(Q, n, 8) ! 0;
	if n eq 8 then
	    B[1][1] := 2;
	    s := 1;
	elif n eq 7 then
	    s := 0;
	else
	    s := -1;
	end if;
	for i := Max(1 - s, 1) to 8 - 2 do
	    B[i + s][i] := -1;
	    B[i + s][i + 1] := 1;
	end for;
	for j := 1 to 8 do
	    B[n][j] := n eq 8 or j le 4 select 1/2 else -1/2;
	end for;
	return LatticeWithBasis(B);
    elif S eq "F" then
	require n in [4]: "Argument 2 must be 4";
	return Lattice("D", n);
    elif S eq "G" then
	require n in [2]: "Argument 2 must be 2";
	return Lattice("A", n);
    elif S eq "Kappa" then
        require n in [1 .. 13]: "Argument 2 should be in the range [1 .. 13]";
	return KappaLattice(n);
    elif S eq "Lambda" then
        require n in [1 .. 31]: "Argument 2 should be in the range [1 .. 31]";
	return LaminatedLattice(n);
    else
	require false:
	    "Argument 1 should be one of " cat
		"\"A\", \"B\", \"C\", \"D\", \"E\", \"F\", \"G\", " cat
		"\"Kappa\", or \"Lambda\"";
    end if;
end intrinsic;


intrinsic BKZ(L::Lat,n::RngIntElt : Delta:=0.999) -> Lat, AlgMatElt
{Return a BKZ-reduced lattice M over Q/Z/R and a transformation T over Z
 such that M = TLT^t on the Gram matrices.}
 if InnerProductMatrix(L) eq 1 then d:=Dimension(L);
  B,T,r:=BKZ(BasisMatrix(L),n : Delta:=Delta);
  if IsGLattice(L) then U:=Inverse(T); S:=[T*g*U : g in Generators(Group(L))];
   G:=sub<GL(d,Integers())|S>; return LatticeWithBasis(G,B),T; end if;
  return LatticeWithBasis(B),T; end if;
 BR:=BaseRing(L); require Type(BR) in {FldRat,FldRe,RngInt}: "Bad ring type";
 GM:=GramMatrix(L);
 if Type(BR) eq RngInt then m:=Max([Abs(x) : x in Eltseq(GM)]);
  RF:=RealField(5+Ceiling(Log(m)/Log(10))); end if;
 if Type(BR) eq FldRat then GM:=GM*LCM([Denominator(x) : x in Eltseq(GM)]);
  m:=Max([Abs(x) : x in Eltseq(GM)]);
  RF:=RealField(5+Ceiling(Log(m)/Log(10))); end if;
 if Type(BR) eq FldRe then RF:=BR; end if;
 d:=Dimension(L); C:=Cholesky(L,RF); BM:=BasisMatrix(C);
 nm:=&+[e^2 : e in Eltseq(BM)]; BM:=BM/Sqrt(nm);
 p:=Precision(BaseRing(Parent(BM)));
 M:=Matrix(d,d,[Round(x) : x in Eltseq(BM*10^p)]);
 B,TZ:=BKZ(M,n : Delta:=Delta); T:=ChangeRing(TZ,BR);
 BM:=ChangeRing(BasisMatrix(L),BR); IPM:=ChangeRing(InnerProductMatrix(L),BR);
 if IsGLattice(L) then TI:=Inverse(T); S:=[T*g*TI : g in Generators(Group(L))];
  G:=sub<GL(d,Integers())|S>; return LatticeWithBasis(G,T*BM,IPM),TZ; end if;
 return LatticeWithBasis(T*BM,IPM),TZ; end intrinsic;

intrinsic BKZ(X::Mtrx,b::RngIntElt :
              Delta:=0.999, Eta:=0.501,
              InitialBlocksize:=2, Method:="Automatic",
              NormLimit:=-1, ProgressionConstant:=100.0,
              Prune:=1.0, PruneTable:=[],
              StepLimit:=0, TimeLimit:=0.0) -> Mtrx, AlgMatElt, RngIntElt
{Return a matrix B whose rows are a BKZ reduced (with block-size b) basis
 for the lattice (over a real subring) spanned by the rows of X together
 with a unimodular matrix T over Z such that L = T * X, and the rank of X.}
 BR:=BaseRing(X); require Type(BR) in {FldRat,FldRe,RngInt}: "Bad ring type";
 M,T,r:=LLL(X : Delta:=Delta, Eta:=Eta); u:=Nrows(X);
 if r ne Nrows(M) and PruneTable ne [] then
  error "Rows must be independent when PruneTable given"; end if;
 M:=Submatrix(M,1,1,r,Ncols(M));
 B,T2,r2:=InternalBKZ(M,b : Delta:=Delta, Eta:=Eta,
		      InitialBlocksize:=InitialBlocksize, Method:=Method,
		      ProgressionConstant:=ProgressionConstant, Prune:=Prune,
		      NormLimit:=NormLimit, PruneTable:=PruneTable,
		      StepLimit:=StepLimit, TimeLimit:=TimeLimit);
 require r eq r2: "Error (internal) in rank from LLL versus BKZ?";
 if u ne r then T2:=DiagonalJoin(T2,IdentityMatrix(BaseRing(T2),u-r));
                B:=VerticalJoin(B,RMatrixSpace(BR,u-r,Ncols(X))!0); end if;
 return B,T2*T,r2; end intrinsic;
