freeze;

/**********************************************************
*                                                         *
* This file implements:                                   *
* M. Kirschmer, "A normal form for definite quadratic     *
* forms over F_q[t]", Math. Comp. 81 (2012), 1619--1634.  *
*                                                         *
* September 2010, Markus Kirschmer                        *
*                                                         *
**********************************************************/

//declare verbose ddf, 1;

forward MakeCanonical;

// requires X over F_q[t] (q odd) to be reduced
function IsDefinite(X)
  if Ncols(X) gt 4 then return false; end if;
  Y:= [ X[i,i]: i in [1..Ncols(X)] ];
  A:= [ LeadingCoefficient(y) : y in Y | IsEven(Degree(y)) ];
  B:= [ LeadingCoefficient(y) : y in Y | IsOdd (Degree(y)) ];
  return (#A le 2) and (#A lt 2 or not IsSquare(-A[1]*A[2]))
     and (#B le 2) and (#B lt 2 or not IsSquare(-B[1]*B[2]));
end function;

function InputOK(X, Finite)
  if not IsSymmetric(X) then return false, "The matrix must be symmetric";
  elif Nrows(X) eq 0 then return false, "Matrix must have positive rank"; end if;
  K:= BaseRing(BaseRing(X));
  if not IsField(K) or not IsOdd(Characteristic(K)) then
    return false, "The base field must have odd characteristic";
  elif Finite and not IsFinite(K) then 
    return false, "The base field must be finite";
  end if;
  return true, _;
end function;

// Reduction by L. Gerstein and D. Djokovic
intrinsic DominantDiagonalForm(X :: Mtrx[RngUPol] : Canonical:= false, ExtensionField:= 0) -> Mtrx, Mtrx, GrpMat, FldFin
{Given a symmetric matrix X, returns matrices G, T such that G=T*X*T^tr is in dominant diagonal form. 
 If X is a definite matrix over Fq[t] with odd q and Canonical is set to true then G is unique.}

  ok, msg:= InputOK(X, Canonical);
  require ok: msg;

//  vprint ddf : "Start reducing.";
  n:= Ncols(X);
  R:= BaseRing(X);
// RSpaceElts won't do due to incompatibilities in mult. code.
  if Type(X) ne AlgMatElt then
    X:= Matrix(R, n, Eltseq(X));
  end if;

  Xold:= X;
  T:= Basis( RSpace(R, n) );
  D:= [ Degree( X[i,i] ): i in [1..n] ];

  ParallelSort(~D, ~T);
  X:= TT * Xold * Transpose(TT) where TT:= Matrix(T);

  while true do
    t:= 1;
    repeat
      t +:= 1;
      d:= Max({ Degree(X[i,t]) - D[i] : i in [1..t-1] });
    until (d ge 0) or t ge n;
    if d lt 0 then break; end if;

    V:= T[t] - &+[ (LeadingCoefficient(X[i,t]) / LeadingCoefficient(X[i,i]) * R.1^d) * T[i]: i in [1..t-1] | Degree(X[i,t]) ge D[i] + d ];
    dV:= Degree( (V * Xold * Matrix(1, Eltseq(V)))[1] );

    if dV ge D[t] then
      T[t]:= V;
      D[t]:= dV;
    else
      ok:= exists(m){m: m in [1..t] | dV lt D[m] };
      assert(ok);
      Remove(~T, t);
      Remove(~D, t);
      Insert(~T, m, V);
      Insert(~D, m, dV);
    end if;
    X:= TT * Xold * Transpose(TT) where TT:= Matrix(T);
    assert D eq [ Degree( X[i,i] ): i in [1..n] ];
  end while;
  T:= Matrix(T);

//  vprint ddf: "Reduction complete.";

  if Canonical then
//    vprintf ddf: "Testing definiteness of:\n %o", X;
    require IsDefinite(X) : "Canonical reduction only works for definite matrices";
//    vprint ddf: "Definite. Good.";

    K:= BaseRing(R);
    if ExtensionField cmpeq 0 then
      ExtensionField:= ext< K | Polynomial([-1/Nonsquare(K),0,1]) >;
    else
      require BaseField(ExtensionField) cmpeq K and Degree(ExtensionField, K) eq 2 : "Wrong extension field.";
      e:= Eltseq(DefiningPolynomial(ExtensionField));
      require e[2] eq 0 and e[3] eq 1 : "Defining Polynomial of ExtensionField must be normalized.";
    end if;

    X, TT, Stab:= MakeCanonical(X, ExtensionField);
    T:= TT * T;
    assert X eq T * Xold * Transpose(T);
    assert forall{s: s in Generators(Stab) | t * X * Transpose(t) eq X where t:= Matrix(s) };
    return X, T, Stab, ExtensionField;
  end if;

  assert X eq T * Xold * Transpose(T);
  return X, T, _, _;
end intrinsic;


intrinsic IsIsometric(G1 :: Mtrx[RngUPol], G2 :: Mtrx[RngUPol] : ExtensionField:= 0) -> BoolElt, Mtrx, FldFin
{Tests whether the definite forms G1, G2 over F_q[t] are isometric.
 If so, the second return value is an isometry from G1 to G2}
  require Parent(G1) eq Parent(G2): "The matrices must be over the same ring.";
  ok, msg:= InputOK(G1, true);
  require ok: msg;
  ok, msg:= InputOK(G2, true);
  require ok: msg;
  X1, T1, _, E:= DominantDiagonalForm(G1 : Canonical, ExtensionField:= ExtensionField);
  X2, T2      := DominantDiagonalForm(G2 : Canonical, ExtensionField:= E);
  if X1 ne X2 then return false, _, E; end if;
  return true, T2^-1 * T1, E;
end intrinsic;


intrinsic AutomorphismGroup(G :: Mtrx[RngUPol] : ExtensionField:= 0) -> GrpMat, FldFin
{Computes the automorphism group of the definite form G over F_q[t]}
  ok, msg:= InputOK(G, true);
  require ok: msg;
  _, T, S, E:= DominantDiagonalForm(G : Canonical, ExtensionField:= ExtensionField);
  return S^(Generic(S) ! T), E;
end intrinsic;


intrinsic ShortestVectors(G :: Mtrx[RngUPol]) -> []
{The shortest non-zero vectors of the definite form G}
  ok, msg:= InputOK(G, false);
  require ok: msg;
  K:= BaseRing(BaseRing(G));
  require IsFinite(K) : "The base field must be finite";
  G, T:= DominantDiagonalForm(G : Canonical:= false);
  require IsDefinite(G) : "The form must be definite";

  L:= Nrows(G) ge 2 and Degree(G[1,1]) eq Degree(G[2,2]) 
  select
    [ < a*T[1] + b*T[2], a^2 * G[1,1] + b^2 * G[2,2] + 2*a*b*G[1,2] > : a,b in K | a ne 0 or b ne 0 ]
  else
    [ < a*T[1], a^2 * G[1,1] > : a in K | a ne 0 ];

  L2 := [x[2] : x in L];
  ParallelSort(~L2, ~L);

  return L;
end intrinsic;

function PolynomialsUpTo(P, B)
  V:= VectorSpace(BaseRing(P), B+1);
  return [ P | Eltseq(v) : v in V ];
end function;

intrinsic ShortVectors(G :: Mtrx[RngUPol], B :: RngIntElt) -> []
{The vectors whose norms with respect to the definite form G have degree at most B}
  ok, msg:= InputOK(G, false);
  require ok: msg;
  GG, T:= DominantDiagonalForm(G: Canonical:= false);
  require IsDefinite(GG) : "The form must be definite";

  n:= Ncols(GG);
  P:= BaseRing(G);
  Degs:= [ Max(-1, (B-Degree(GG[i,i])) div 2) : i in [1..n] ];
  Polys:= [ PolynomialsUpTo(P, d) : d in Degs ];
  C:= CartesianProduct(Polys);
  L:= [ <v, (v*G*Matrix(1, Eltseq(v)))[1]> where v:= Vector([c[i]: i in [1..n]])*T : c in C ];

  L2 := [x[2] : x in L];
  ParallelSort(~L2, ~L);

  return L;
end intrinsic;



// The canonical reduction part.

// Return s, n such such that x = s^2 * e^n
function eSqrt(x, e)
  ok, y:= IsSquare(x);
  if ok then
    n:= 0;
  else
    y:= Sqrt(x/e);
    n:= 1;
  end if;
  my:= -y;
  return y le my select y else my, n;
end function;

// Returns the parameters corresponding to the matrix X
function decompose(X, E)
  einv:= -ConstantCoefficient(DefiningPolynomial(E));
  a:= ( X[1,1] - X[2,2] * einv)/2;
  b:= (-X[1,2] + X[2,1]       )/2;
  g:= E ! [(X[1,1] + X[2,2] * einv)/2 , (X[1,2] + X[2,1])/2];
  return <a, b, g>;
end function;

RegRep:= function(x)
  einv:= -ConstantCoefficient(DefiningPolynomial(Parent(x)));
  return Matrix(2, [y[1], y[2] * einv, y[2], y[1]]) where y:= Eltseq(x);
end function;


// To avoid constructing intermediate matrix groups, stabilizers are denoted
// internally as a single character.
// "n" = -I_n where n = 1 or 2
// "S" = SOMinus = < s >
// "G" = GOMinus = < s, D >
// "V" = < -I_2, D >
// "B" = < -I_2, s*D >
// "b" = < (s,s), (D, s*D) >
// "X" = GO x GO
// where D:= Diag(1,-1) and s = RegRep(beta)

// To convert the character to the group one uses
function CharToGroup(S, beta)
  K:= BaseField(Parent(beta));
  if S in {"1", "2"} then
    return [ MatrixRing(K, StringToInteger(S)) ! -1 ], 2;
  end if;
  s:= RegRep(beta);
  if S eq "S" then 
    return [ s ], #K + 1;
  end if;
  D:= DiagonalMatrix([ K | 1, -1 ]);
  case S:
    when "G": return [ s, D ], 2*(#K+1);
    when "b": return [ DiagonalJoin(s,s), DiagonalJoin(D, s*D)], 2*(#K+1);
    when "B": return [ Parent(D) ! -1, s*D ], 4;
    when "V": return [ Parent(D) ! -1,   D ], 4;
    when "X": one:= Parent(s) ! 1;
              return [ DiagonalJoin(s, one), DiagonalJoin(D, one), DiagonalJoin(one, s), DiagonalJoin(one, D) ], 4*(#K+1)^2;
  end case;
  error "Unknown stabilizer.";
end function;

// Computes t in SO such that tMt^tr is canonical as well as the
// decomposition of tMt^tr and its stabilizer
function stdorbSO(M, beta)
  E:= Parent(beta);
  X:= decompose(M, E);
  if X[3] eq 0 then return Parent(M) ! 1, < X[1], X[2], 0, 0, 0 >, "S";  end if;
  alpha:= PrimitiveElement(E);
  c, m:= eSqrt(Norm(X[3]), Norm(alpha));
  x:= X[3] / (c * alpha^m);
  ok, u:= IsSquare(x);
  if ok and Norm(u) eq 1 then
    n:= 0;
  else
    n:= 1;
    u:= Sqrt(x / beta);
    assert Norm(u) eq 1;
  end if;
  t:= RegRep(u^-1);

  assert decompose(t * M * Transpose(t), E) eq < X[1], X[2], c * alpha^m * beta^n >;

  return t, < X[1], X[2], c, m, n >, "2";
end function;

// Same for GO
function stdorbGO(M, beta)
  t, X:= stdorbSO(M, beta);
  if X[3] eq 0 then		// no imaginary part at all
    if X[2] eq 0 then return t, X, "G"; end if;
    if -X[2] lt X[2] then t[2] *:= -1; X[2] *:= -1; end if;
    return t, X, "S";
  end if;
  if X[4] eq 0 then 		// no alpha
    if X[2] eq 0 then return t, X, X[5] eq 0 select "V" else "B"; end if;
    if -X[2] lt X[2] then 
      t[2] *:= -1; X[2] *:= -1;
      // Diag(1,-1) maps beta to beta^-1. We have to correct this.
      if X[5] eq 1 then t:= RegRep(beta)*t; end if;
    end if;
  elif X[5] eq 1 then 		// OK, we have some alpha. Remove beta iff it exists.
    t[2] *:= -1; X[2] *:= -1; X[5]:= 0;
  end if;
//  assert decompose(t * M * Transpose(t), E) eq < X[1], X[2], X[3] * PrimitiveElement(E)^X[4] * beta^X[5] > where E:= Parent(beta);
  return t, X, "2";
end function;

// Returns g in SO such that g*(a,b)^t is in standard form the second return value
// indicates whether the second entry of this standard form is zero or not
function stdorbSOcol(a, b, E)
  if a eq 0 and b eq 0 then return MatrixRing(Parent(a), 2) ! 1, true; end if;
  alpha:= PrimitiveElement(E);
  w:= E ! [a,b];
  c, n:= eSqrt(Norm(w), Norm(alpha));
  v:= n eq 0 select E ! c else c * alpha;
  g:= RegRep(v/w);

//  assert g * Matrix(1, [a,b]) eq Matrix(1, Eltseq(v));
//  assert Determinant(g) eq 1 and g * F * Transpose(g) eq F where F:= DiagonalMatrix([1, 1/ConstantCoefficient(DefiningPolynomial(E))]);
  return g, n eq 0;
end function;

Coeffs:= func< M, d | Matrix( Ncols(M), [ Coefficient(x, d) : x in Eltseq(M) ] ) >;

// Canonical reduction for reduced 2x2 matrices over Fq[t] if the
// diagonal entries have the same degree.
function reduce2(X, beta)
  E:= Parent(beta);
  K:= BaseField(E);
  e:= -1/ConstantCoefficient(DefiningPolynomial(E));

  c, k:= eSqrt(LeadingCoefficient(X[1,1]), e); c:= 1/c;
  b:= LeadingCoefficient(X[2,2]);
  if k eq 0 then
    T:= DiagonalMatrix([c, Sqrt(-e/b)]);
  else
    d:= Sqrt(-1/b);
    if #K mod 4 eq 1 then
      T:= Matrix(2, [0, d*j, c*j, 0]) where j:= Sqrt(K ! -1);
    else
      alpha:= PrimitiveElement(E);
      u:= Sqrt(-1/Norm(alpha));
      T:= u*Matrix(2, [ee[2]*c*e, ee[1]*d, ee[1]*c, ee[2]*d]) where ee:= Eltseq(alpha);
    end if;
  end if;

  d:= Degree(X[1,1]);
//  assert T * Coeffs(X, d) * Transpose(T) eq DiagonalMatrix([1,-e]);

  S:= "G";	// Current stabilizer is the full GO. Now we descent.
  while d gt 0 and S eq "G" do
    d -:= 1;
    M:= T * Coeffs(X, d) * Transpose(T);
    t, _, S:= stdorbGO(M, beta);
    if not IsOne(t) then T:= t*T; end if;
  end while;
//  assert S in {"G", "B", "V", "2"};
//  assert forall{ g : g in CharToGroup(S, beta) | g * C * Transpose(g) eq C } where C:= Coeffs(T * X * Transpose(T), d);
//  tt:= decompose(T * Coeffs(X, d) * Transpose(T), E);

  if d gt 0 and S ne "2" then
    X1:= T * X * Transpose(T);
    t:= CharToGroup(S, beta)[2];
    X2:= t * X1 * Transpose(t);
    if X1 ne X2 then
      S:= "2";
      if X2 lt X1 then T:= t*T; end if;
    end if;
  end if;

  return T, S;
end function;

// Finds the smallest element in the orbit of M under the
// matrix group generated by gens. 
// It is assumed that this groups is isomorpic to C_2^#gens.
function enumerate(M, gens)
//  vprintf ddf: "enumerate with %o gens.\n", #gens;
  V:= VectorSpace(GF(2), #gens);
  S:= sub< V | >;
  Orbit:= {@ M @};
  Paths:= [ V ! 0 ];

  i:= 0;
  while i lt #Orbit do
    i +:= 1;
    for k in [1..#gens] do
      X:= gens[k] * Orbit[i] * Transpose(gens[k]);
      j:= Index(Orbit, X);
      if j eq 0 then
        Append(~Paths, Paths[i] + V.k);
	Include(~Orbit, X);
      else
        Include(~S, Paths[i] + Paths[j] + V.k);
      end if;
    end for;
  end while;

  X, i:= Minimum(Orbit);
  f:= func< v | &*[ Parent(M) | gens[j] : j in Support(v) ] >;
  return X, f(Paths[i]), [ f(v) : v in Basis(S) ];
end function;

function InsertDiag(M, i)
  M[i,i]:= -1;
  return M;
end function;

// Suppose only the stabilizer of the diagonal block starting at I is GO
// This function normalizes the non-diagonal entries.
function singleGO(X, I, beta)
  E:= Parent(beta);
  K:= BaseField(E);
  n:= Ncols(X);
  Js:= [1..I-1] cat [I+2..n];
  d, j:= Maximum([ Degree(X[i, j]) : i in [ I, I+1 ], j in Js ]);
  assert d ge 0;
  j:= Js[(j+1) div 2];

  one:= MatrixRing(K, n) ! 1;
  gens:= [ -one ];
  t, iszero:= stdorbSOcol(Coefficient(X[I, j], d), Coefficient(X[I+1, j], d), E);
  t:= InsertBlock(one, t, I, I);

  D:= DiagonalMatrix([K ! 1, -1]);
  g:= iszero select D else D*RegRep(beta);
  g:= InsertBlock(one, g, I, I);
  X1:= t * X * Transpose(t);
  X2:= g * X1 * Transpose(g);
  if X1 eq X2 then
    Append(~gens, g);
  elif X2 lt X1 then
    t:= g*t; X1:= X2;
  end if;

  return X1, t, gens, 2^#gens;
end function;

procedure swap(~a, ~b)
  x:= a; a:= b; b:= x;
end procedure;

// The action of GxG on a matrix M.
function GOxGO(M, beta)
  K:= BaseRing(M);
  one:= MatrixRing(K, 2) ! 1;
  if IsZero(M) then return <one, one>, "X"; end if;
  E:= Parent(beta);
  X:= decompose(M, E);

  if X[3] eq 0 or (X[1] eq 0 and X[2] eq 0) then
    if X[3] ne 0 then
      r:= DiagonalMatrix([K | 1, -1]);
      X:= [ ee[1], ee[2] ] where ee:= Eltseq(X[3]);
    else
      r:= one;
    end if;
    l, iszero:= stdorbSOcol(X[1], X[2], E);
    return <l, r>, iszero select "G" else "b";
  end if;

  na:= Norm( PrimitiveElement(E) );
  a1, n1:= eSqrt(Norm(E ! [X[1], X[2]]), na);
  a2, n2:= eSqrt(Norm(X[3]), na);

  if (n1 eq 1 and n2 eq 0) or (n1 eq n2 and a1 gt a2) then
    r:= DiagonalMatrix([K | 1, -1]);
    swap(~n1, ~n2);
    swap(~a1, ~a2);
    X:= < ee[1], ee[2] > where ee:= Eltseq(X[3]);
    M:= M*r;
  else
    r:= one;
  end if;

  l, iszero:= stdorbSOcol(X[1], X[2], E);
  M:= l*M;

  if iszero then
    t, X:= stdorbGO(M, beta);
  else
    t, X:= stdorbSO(M, beta);
  end if;

  Stab:= [ < mone, mone > ] where mone:= -one;

  D:= DiagonalMatrix([K | 1, -1]);
  s:= RegRep(beta);
  if a1 eq a2 and n1 eq n2 then
    n:= X[5];
    Append(~Stab, <one, n eq 0 select D else s*D >);
    if n2 eq 0 then
      Append(~Stab, < n eq 0 select D else s*D, one >);
    else
      Append(~Stab, < n eq 1 select D else D*s, one >);
    end if;
  elif n2 eq 0 then
    x:= X[5] eq 0 select D else s*D;
    Append(~Stab, <x,x>);
  elif n1 eq 1 then
    if X[5] eq 0 then
      Append(~Stab, <D*s, D>);
    else
      Append(~Stab, <D, s*D>);
    end if;
  end if;
//  MM:= t * M * Transpose(t);
//  OK:= [ t[1] * MM * Transpose(t[2]) eq MM : t in Stab ];
//  assert &and OK;

  return < t*l, t*r >, Stab;
end function;


// requires X over F_q[t] (q odd) to be reduced
function MakeCanonical(Xold, E)
//  vprint ddf: "Make Canonical starts";
  X:= Xold;
  n:= Ncols(X);
  K:= BaseRing(BaseRing(X));
  one:= MatrixRing(K, n) ! 1;
  T:= MatrixRing(K, n) ! 0;
  e:= -1/ConstantCoefficient(DefiningPolynomial(E));
  beta:= 0;

  blocks:= [];  // Stores position and stabilizer of diagonal blocks.
  i:= 1;
  while i le n do
    if i eq n or Degree(X[i,i]) lt Degree(X[i+1, i+1]) then
      T[i,i]:= 1/eSqrt(LeadingCoefficient(X[i,i]), e);
      Append(~blocks, <i,"1">);
      i +:= 1;
    else
      if beta cmpeq 0 then
        beta:= PrimitiveElement(E)^(#K-1);		// alpha^q / alpha
      end if;
      t, S:= reduce2( Submatrix(X, i, i, 2, 2), beta);
      InsertBlock(~T, t, i, i);
      Append(~blocks, <i, S>);
      i +:= 2;
    end if;
  end while;
  X:= T * X * Transpose(T);
  // The stablizer is now a direct Product of copies of C_2, V_4 and G0Minus
  // Now we handle the different cases.
  
//  vprint ddf: "Found the block structure", blocks;
  
  if #blocks eq 1 then		// Already solved
    gens, order:= CharToGroup(blocks[1,2], beta);

  // Only 1x1 blocks. The orthogonal decomposition yields the stabilizer.
  elif forall{b: b in blocks | b[2] in {"1", "V"}} then
//    vprint ddf: "orthogonal decomposition";
    Components:= [];
    todo:= {1..n};
    repeat
      c:= Support(X[Rep(todo)]);
      repeat
        size:= #c;
        c:= &join [ Support(X[j]) : j in c ];
      until size eq #c;
      Append(~Components, c);
      todo diff:= c;
    until IsEmpty(todo);
    order:= 2^#Components;
    gens:= [ DiagonalMatrix([K | i in c select -1 else 1 : i in [1..n] ]) : c in Components ];

    // Compute the minimal form under sign changes.
    // The first vector in each component remains unchanged.
    for c in Components do
      x:= Sort(Setseq(c));
      fixed:= { x[1] };
      for i in [1..#x], j in x[i+1..#x] do
        if (x[i] notin fixed or j notin fixed) and X[x[i], j] ne 0 then
          s:= x[i] in fixed select j else x[i];
          Include(~fixed, s);
          l:= LeadingCoefficient(X[x[i], j]);
          if -l lt l then T[s] *:= -1; MultiplyRow(~X, -1, s); MultiplyColumn(~X, -1, s); end if;
        end if;
      end for;
    end for;

  // Two 2x2 blocks with huge stabilizers
  elif {b[2] : b in blocks} eq {"G"} then
//    vprint ddf: "GOxGO case";
    S:= "X";
    L:= Submatrix(X, 1, 3, 2, 2);
    d:= Max([ Degree(x) : x in Eltseq(L) ]);
    t:= <I2, I2> where I2:= MatrixRing(K, 2) ! 1;
    while d ge 0 and Type(S) eq MonStgElt and S in {"X", "b", "G", "S"} do
      XX:= t[1] * Coeffs(L, d) * Transpose(t[2]);
      case S: 
        when "X": tt, S:= GOxGO(XX, beta);
	when "G": tt, _, S:= stdorbGO(XX, beta);
	          tt:= < tt, tt >;
	when "S": tt, _, S:= stdorbSO(XX, beta);
                  tt:= < tt, tt >;
	when "b": a:= RegRep(PrimitiveElement(E));
	          ai:= a^-1;
		  tt, _, S:= stdorbGO(ai * XX, beta);
                  tt:= < a*tt*ai, tt >;
		  if S eq "G" then
		    S:= "b";
		  elif S notin {"2", "S"} then
                    S:= [ < a * g * ai, g > : g in CharToGroup(S, beta) ];
		    assert &and [ s[1] * YY * Transpose(s[2]) eq YY : s in S] where YY:= tt[1] * XX * Transpose( tt[2] );
		  end if;
	else error "unknown case";
      end case;
      t:= < tt[1] * t[1], tt[2] * t[2] >;
      d -:= 1;
    end while;
    t:= DiagonalJoin(t);
    T:= t*T;

    if Type(S) eq MonStgElt and S in {"X", "G", "S", "b"} then
      gens, order:= CharToGroup(S, beta);
      if S in {"G", "S"} then gens := [ DiagonalJoin(t,t) : t in gens ]; end if;
    else
      if Type(S) eq MonStgElt then
        S:= [ <t,t> : t in CharToGroup(S, beta) ];
      end if;
      gens:= [ DiagonalJoin(t) : t in S ];
      if d ge 0 then
        _, t, gens:= enumerate(t * X * Transpose(t), gens[2..#gens]);
        T:= t*T;
        Append(~gens, -one);
      end if;
      order:= 2^#gens;
    end if;

  // A single block with stabilizer GO.
  elif exists(b){b : b in blocks | b[2] eq "G"} then
//    vprintf ddf: "single GO";
    // The stab of the other blocks together yield a subgroup of C2xC2. 
    // But -I_n fixes every matrix, so wlog. the first generator can be ignored.
    extra:= [ InsertBlock(one, g, c[1], c[1]) : g in CharToGroup(c[2], beta), c in blocks | c[1] ne b[1] ];
    assert #extra in {0, 1, 2};
    extra:= extra[2..#extra];

    Js:= [1..b[1]-1] cat [b[1]+2..n];
    if exists{ <i,j> : i in [ b[1], b[1]+1 ], j in Js | X[i, j] ne 0 } then
      X1, t, gens, order:= singleGO(X, b[1], beta);
      if not IsEmpty(extra) then
        X2, t2, gens2 := singleGO(extra[1] * X * Transpose(extra[1]), b[1], beta);
	if X1 eq X2 then
	  Append(~gens, t2 * extra[1] * t^-1);
	  order *:= 2;
	elif X2 lt X1 then
	  t:= t2 * extra[1];
          gens:= gens2;
	end if;
      end if;
      T:= t*T;
    else
      gens, order:= CharToGroup("G", beta);
      gens:= [ InsertBlock(one, g, b[1], b[1]) : g in gens ] cat [-one];
      order *:= 2;
      if not IsEmpty(extra) then
        XX:= extra[1] * X * Transpose(extra[1]);
	if XX eq X then 
	  Append(~gens, extra[1]);
	  order *:= 2;
	elif XX lt X then
	  // no need to adjust gens. extra[1] has order 2 and commutes with gens!
	  T:= extra[1] * T;
	end if;
      end if;
    end if;

  else
    // Only blocks with tiny stabilizers.
    // The direct product of all stabs is a subgroup of C2^n
    // So enumerate and be done with it.
    gens:= [ InsertBlock(one, g, c[1], c[1]) : g in CharToGroup(c[2], beta), c in blocks ];
    X, t, gens:= enumerate(X, gens[2..#gens]);
    Append(~gens, -one);
    T:= t*T;
    order:= 2^#gens;
  end if;

  Stab:= sub< GL(n, K) | gens >;
//  assert #Stab eq order;
  Stab`Order:= order;		// Hopefully this is correct!
  return T * Xold * Transpose(T), T, Stab;
end function;
