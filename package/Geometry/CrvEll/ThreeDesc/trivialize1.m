freeze;

// Trivialising the algebra
// Given structure constants for a Q-algebra known to be isomorphic
// to Mat(3,Q), we find such an isomorphism explicitly

// This version: T. Fisher, April 2009 
// Based in part on earlier code of M. Stoll 

// In ThreeDescent there is a simple switch between the 2 methods.
// Currently this method is not being used; sometimes the error
// "Failed to trivialize" is encountered.

// Regarding speed: generally this was observed to be several times
// faster than the old method when AdHocReduce is false; however 
// when true, this is only slightly faster (around 25%, say).

// April 2010 - tried setting precision in a more sensible
// way, but haven't tested it.

MinPoly := MinimalPolynomial;
Id := IdentityMatrix;

function GetMatrices(AA,bas)
  n := Dimension(AA);
  V := Module(AA);
  h := hom<V -> V | bas>;
  sss := [[Eltseq((bas[i]*bas[j]) @@ h) : j in [1..n]] : i in [1..n]];
  return [Matrix(n,[sss[i,j,k] : i,j in [1..n]]): k in [1..n]];
end function;  

function TraceMatrix(A,b)
  n := Dimension(A);
  flag,nn := IsSquare(n);
  assert flag;
  _, mm := MatrixAlgebra(A);
  trd := func<x|(1/nn)*Trace(mm(x))>;
  return Matrix(n,n,[trd(b[i]*b[j]): i,j in [1..n]]);
end function;

IsTrivialisation := func<A,mats| forall{ [i,j] : i,j in [1..n] | 
  mats[i]*mats[j] eq &+[Eltseq(A.i*A.j)[k]*mats[k]: k in [1..n]] }
  where n := Dimension(A) >;

IsApproxTrivialisation := func<A,mats,prec| forall{ [i,j] : i,j in [1..n] | 
  Maximum([Abs(x): x in Eltseq(mats[i]*mats[j] 
       - &+[Eltseq(A.i*A.j)[k]*mats[k]: k in [1..n]])]) lt 10^(-prec) }
  where n is Dimension(A) >;

function RowSpaceMatrix(mat,rk)
  R := BaseRing(mat);
  if R cmpeq Integers() then
    V := RModule(R,Ncols(mat));
    U,map := sub<V|[V!mat[i]: i in [1..Nrows(mat)]]>;
    bb := [map(b): b in Basis(U)];
    mat1 := Matrix(R,#bb,Ncols(mat),[Eltseq(b): b in bb]);
    mat1 := ChangeRing(LLL(mat1),Rationals());
  else
    mat1 := ZeroMatrix(R,rk,Ncols(mat));
    i := 1;
    for j in [1..Nrows(mat)] do
      mat1[i] := mat[j];
      if Rank(mat1) eq i then i +:= 1; end if;
      if i gt rk then break; end if;
    end for;
  end if;
  return mat1;
end function;

function TrivialisationFromZeroDivisor(A,xx,bas)
  K := BaseRing(A);
  V9 := Module(A);
  h := hom<V9 -> V9|bas>;
  mat := Matrix(K,9,9,[Eltseq((xx[1]*b) @@ h): b in bas]);
  if K cmpeq Rationals() then 
    d := RationalGCD(Eltseq(mat));
    mat := ChangeRing((1/d)*mat,Integers());
  end if;
  rk := Rank(mat);
  assert rk in {3,6};
  if rk eq 6 then 
    if K cmpeq Rationals() then 
      mat := KernelMatrix(mat); 
    else
      mat := Matrix(K,9,9,[Eltseq((xx[2]*b) @@ h): b in bas]);
    end if;
    assert Rank(mat) eq 3;
  end if;
  mat := RowSpaceMatrix(mat,3);
  V3 := VectorSpace(K,3);
  map := hom<V3 -> V9|mat> * h;
  bb := [map(V3.i): i in [1..3]];
  mats := [Matrix(K,3,3,[Eltseq((b*A.j) @@ map): b in bb]): j in [1..9]];
  return mats;
end function;

function RealTrivialisation(A,bas,prec)
  for b in bas do
    f := MinPoly(b);
    if Degree(f) gt 1 then x := b; break; end if;
  end for;
  if IsIrreducible(f) then 
    L := NumberField(f);
    AL := ChangeRing(A,L);
    P := PolynomialRing(L); X:=P.1;
    f1 := X - L.1;
    f2 := ExactQuotient(P!f,f1);
  else
    L := Rationals();
    AL := L;
    f1 := Factorization(f)[1][1];
    f2 := ExactQuotient(f,f1);
  end if;
  theta := AL!Eltseq(x);
  x1 := Evaluate(f1,theta);
  x2 := Evaluate(f2,theta);
  assert (x1 ne 0) and (x2 ne 0) and x1*x2 eq 0;
  basL := [AL!Eltseq(b) : b in bas];
  mats := TrivialisationFromZeroDivisor(AL,[x1,x2],basL);
  R := RealField(prec);
  if L cmpeq Rationals() then 
    matsR := [ChangeRing(M,R): M in mats];
  else
    iota := func<x|Conjugates(x:Precision:=prec)[1]>;
    matsR := [Matrix(R,3,3,[iota(M[i,j]): i,j in [1..3]]): M in mats];
  end if;
  return matsR;
end function;

function Upper(mat) 
  D, T := OrthogonalizeGram(mat);
  Tinv := T^(-1);
  D1 := DiagonalMatrix([Abs(D[i,i]) : i in [1..Nrows(mat)]]);
  return Tinv*D1*Transpose(Tinv);
end function;

function TweakToPositiveDefinite(mat)
  mat +:= Transpose(mat);
  fa := 0.0001;
  while not IsPositiveDefinite(mat) do
    mat +:= fa*Parent(mat)!1;
    fa *:= 2;
  end while;
  return mat;
end function;

function Act(matseq, T)
  return [&+[iT[i,j]*seq0[j] : j in [1..#seq0]] : i in [1..#seq0]]
         where iT := T1^-1
         where seq0 := [Transpose(T1)*mat*T1 : mat in matseq]
         where T1 := ChangeRing(T, CoefficientRing(Universe(matseq)));
end function;

function AdHocReduction(A,bas)
  n := Dimension(A);
  matsize := func<mat|&+[c^2 : c in Eltseq(mat)]>;
  algsize := func<mats|&+[matsize(mat) : mat in mats]>;
  mats := GetMatrices(A,bas);
  size := algsize(mats);
  vprintf ThreeDescent, 2 : "    Size = %o\n", size;
  ctr := 0;
  bestsize := size;
  while ctr lt 10 do
    UU := [Upper(m + Transpose(m)) : m in mats];
    TT := [ Transpose(T) where _,T := LLLGram(U) : U in UU];
    wts := [Sqrt(matsize(m)) : m in mats];
    UU := [ChangeRing(U, RealField()) : U in UU];
    UU1 := [&+UU, &+[1/wts[i]*UU[i] : i in [1..#wts]],
             &+[1/Sqrt(wts[i])*UU[i] : i in [1..#wts]]];
    UU1 := [TweakToPositiveDefinite(U) : U in UU1];
    TT cat:= [ Transpose(T) where _,T := LLLGram(U) : U in UU1];
    newmats := [Act(mats, T) : T in TT];
    size, pos := Min([algsize(mm) : mm in newmats]);
    mats := newmats[pos];
    bas := [&+[T[j,i]*bas[j] : j in [1..n]] : i in [1..n]] where T := TT[pos];
    vprintf ThreeDescent, 2 : "     pos = %o ==> Size = %o\n", pos,size;
    if size lt 100 then break; end if;
    if size lt (1/2)*bestsize then ctr := 0; end if;
    if size lt bestsize then bestsize := size; end if;
    ctr +:= 1;
  end while;
  return bas;
end function;

intrinsic TrivializeNew(A::AlgAss, bas::SeqEnum : JustBasis := false, 
                        UseTraceForm := true, AdHocReduce := true ) -> Map
{Given a Q-algebra A known to be isomorphic to Mat(3,Q), and a basis of a maximal order in A, finds an isomorphism A -> Mat(3,Q).}
  n := Dimension(A);
  trmat := TraceMatrix(A,bas);
  discr := Abs(Determinant(trmat));
  error if discr ne 1, 
     "A must be split, and bas must be a basis of a maximal order.";
  if UseTraceForm then 
    vprint ThreeDescent, 2 :  "    Reducing trace form";
    U := Upper(trmat);
    _,T := LLLGram(U);
    bas := [&+[T[i,j]*bas[j] : j in [1..n]] : i in [1..n]];
  end if;
  if AdHocReduce then 
    bas := AdHocReduction(A,bas);
  end if;
  P := PolynomialRing(Rationals()); X:=P.1;
  x := A!0;
  prec := 100;
  for loopvar in [1..10] do
    ss := 100;
    for b in bas do
      f := P!MinimalPolynomial(b);
      ss := Maximum([ss] cat [Abs(x): x in Coefficients(f)]);
      vprint ThreeDescent, 2 : "      Minimal Polynomial =",f;
      if not IsIrreducible(f) then x := b; break loopvar; end if;
    end for;
    vprint ThreeDescent, 2 : "    Computing real trivialisation";
    prec := 2*Maximum(Ilog(10,Round(ss)),50); 
                   // April 2010 : try setting precision?
                   // this is just a wild guess
    vprint ThreeDescent, 2 : "Using real precision =",prec;
    matsR := RealTrivialisation(A,bas,prec);
    matsR := [&+[bas[i][j]*matsR[j] : j in [1..9]]: i in [1..9]];
    R := BaseRing(matsR[1]);
    if loopvar ge 0 then // use Hunter's theorem
      if bas[1] ne One(A) then 
        mat := Matrix(Rationals(),9,9,[Eltseq(b): b in bas]);
        ss := Solution(mat,One(A));
        _,_,T := SmithForm(Matrix(Integers(),1,9,Eltseq(ss)));
        Tinv := T^(-1);
        bas := [&+[Tinv[i,j]*bas[j]: j in [1..9]]: i in [1..9]];
        matsR := [&+[Tinv[i,j]*matsR[j] : j in [1..9]]: i in [1..9]];
        if bas[1] ne One(A) then bas[1] *:= -1; end if;
        assert bas[1] eq One(A); 
      end if;
      t := [(1/3)*Trace(mat) : mat in matsR];
      matsR := [matsR[i] - t[i]*Id(R,3): i in [2..9]];
      M := Matrix(R,8,9,[Eltseq(mat): mat in matsR]);
      _,U := LLL(M : Delta := 0.999);   
      U := DiagonalJoin(Id(Integers(),1),U);
      tt := [&+[U[i,j]*t[j] : j in [1..9]]: i in [1..9]];
      for i in [2..9] do U[i,1] := -Round(tt[i]); end for;
    else
      M := Matrix(R,9,9,[Eltseq(mat): mat in matsR]);
      _,U := LLL(M : Delta := 0.999);
    end if;
    bas := [&+[U[i,j]*bas[j]: j in [1..9]]: i in [1..9]];
    prec *:= 2;
  end for;
  error if x eq 0, "Trivialisation failed";
  if JustBasis then return bas; end if;
  f := Factorization(MinPoly(x))[1][1];
  mats := TrivialisationFromZeroDivisor(A,[Evaluate(f,x)],bas);
  Mat := Universe(mats);
  iso := map< A -> Mat | a :-> &+[ Eltseq(a)[i]*mats[i] : i in [1..9]] >;
  return iso;
end intrinsic;


