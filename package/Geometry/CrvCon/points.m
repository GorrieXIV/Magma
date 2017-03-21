freeze;

/********************************************************************************
    
    IMPORTANT NOTE: 'HasPoint' is identified with 'HasRationalPoint'
    at bind level (which is a feature we should maintain). 
    Consequences:
    1) declaring one of them at package level gives you the other for free
    2) NEVER declare both at package level -- one or other of your declarations
       will just get ignored!!

*********************************************************************************   
  
  NOTES ABOUT SOME OF THE CHANGES:

  Steve, Feb/March '10:

    Many improvements to DiagonalForm (for CrvCon[FldAlg])

  Steve, September '08:
    
    Added new implementation of DiagonalForm(CrvCon[FldAlg]) which is careful
    to avoid unnecessary factorization.

    Included some functions for minimising conics over number fields at split
    primes, but these are currently not used anywhwere.

    Changed HasRationalPoint to call my new implementation of lagranges_method 
    (after careful diagonalization)

  Steve, August '07:
    
    HasRationalPoint now declared here instead of at bind level.
    It now covers conics over FldFunRat's too.
    
********************************************************************************/

declare verbose Conic, 3;

import "lagrange.m" : solve_diagonal_conic;

import "fldfunrat.m": HasRationalPoint_FldFun;

/////////////////////////////////////////////////////////////////////////////////
//             HELPER FUNCTIONS FOR FACTORIZATION ISSUES                       //
/////////////////////////////////////////////////////////////////////////////////

forward can_factor; // temp

function factor_out_primes(N, primes)
  assert N ne 0;
  N1 := 1;
  N2 := Integers()! N; 
  Nprimes := {};
  for p in primes do 
    e := Valuation(N2, p);
    if e gt 0 then
      pe := p^e;
      N1 *:= pe;
      N2 div:= pe;
      Include(~Nprimes, p);
    end if;
  end for;
  return N1, N2, Nprimes;
end function;

// Return the set of prime divisors of N, trying the given primes first

function prime_divisors(N, primes)
  N1, N2, Nprimes := factor_out_primes(N, primes);
  newprimes := Seqset(PrimeDivisors(N2));
  StoreFactor(newprimes);
  //assert can_factor(N, 1); // using stored primes
  return Nprimes join newprimes; 
end function;

function easy_factorization(N : effort:=1) 
  // # of ecm curves tried is something like (ECMLimit-5000)/20
  // MPQS is used if # digits < MPQSLimit
  if effort lt 2 then
    ecm := Round( 100*effort );
    mpqs := 0;
  else
    ecm := Round( 100*effort );
    mpqs := 50 + Round( (effort-2) ); 
  end if;
  fact, _, unfact := Factorization(N : ECMLimit:=ecm, MPQSLimit:=mpqs, Proof:=false); 
  if assigned unfact then
    return false, _, _;
  else 
    primes := {tup[1] : tup in fact};
    StoreFactor(primes);
    return true, fact, primes;
  end if;
end function;

function can_factor(x, e) // e = effort
  if x cmpeq 0 then
    return true, [], {};

  elif Type(x) eq RngIntElt then
    return easy_factorization(x : effort:=e);

  elif Type(x) eq FldRatElt then
    ok, dfact, dprimes := can_factor(Denominator(x), e);
    if ok then
      ok, nfact, nprimes := can_factor(Numerator(x), e);
    end if;
    if ok then
      return true, dfact cat nfact, dprimes join nprimes;
    else
      return false, _, _;
    end if;
  end if;

  if ISA(Type(x), FldAlgElt) or ISA(Type(x), RngOrdElt) then
    x := x * Integers(NumberField(Parent(x)));
  end if;

  if ISA(Type(x), RngOrdFracIdl) then
    ok, dfact, dprimes := can_factor(Denominator(x), e);
    if ok then
      ok, mfact, mprimes := can_factor(Minimum(x), e);
    end if;
    if ok then
      return true, dfact cat mfact, dprimes join mprimes;
    else
      return false, _, _;
    end if;
  end if;
/*
  time0 := Cputime();
  bool, fact, primes := easy_factorization(x : effort:=e);
  t := Cputime(time0);
  if t gt e+1 then printf " (F%o:%os) ", e, Round(t); end if;

  if e le 10 and t gt 5*(e+2) then 
     printf "That's too long for can_factor (effort = %o), let's see that again:\n", e;
     verb := GetVerbose("Factorization"); SetVerbose("Factorization", 2);
     _ := easy_factorization(x : effort:=e);
     SetVerbose("Factorization", verb);
  end if;

  if bool then
    return bool, fact, primes;
  else 
    return false, _, _;
  end if;
*/
end function;

/////////////////////////////////////////////////////////////////////////////////

intrinsic LLLBasis(I::RngOrdFracIdl) -> SeqEnum[FldOrdElt]
{The basis given by LLLBasisMatrix}
  ZK := Order(I);
  K := NumberField(ZK);
  FF := FieldOfFractions(ZK);
  assert IsAbsoluteOrder(ZK);
  bm := LLLBasisMatrix(I);
  basis := [FF! Eltseq(bm[i]) : i in [1..Nrows(bm)]];
// TO DO: full check
//for b in basis do assert b in I; end for;
  return basis;
end intrinsic;

// Small element in an ideal I

function small_element_sub(I)
  M := Order(I);
  F := NumberField(M);
  PI := PowerIdeal(M);

  if IsTotallyReal(F) then
    BMI := ChangeRing(BasisMatrix(I), Rationals());
    D := Denominator(I);
    L := InternalExactLattice(PI!(I*D) : T:=false);
    C := CoordinateLattice(L);
    LL := LLL(C);
    elts := [];
    for i := 1 to Dimension(L) do 
      zvec := Matrix(Rationals(), [[Round(c) : c in Eltseq(LL.i)]]) * BMI;
      z := FieldOfFractions(M)! Eltseq(zvec);
      assert z in I;
      Append(~elts, z);
    end for;
  else
    elts := LLLBasis(I);
  end if;

  norms := [Abs(AbsoluteNorm(x)) : x in elts];
  _, i := Min(norms);
  return elts[i];
end function;

function small_element(I : class:=false) // class means use class group
  O := Order(I);
  F := NumberField(O);
  m := Minimum(I);
  if AbsoluteDegree(F) eq 1 then
    s := m;
    flag := true;
  elif class then
    flag, s := IsPrincipal(I);
  else
    flag := false;
  end if;
  if not flag then
    s := small_element_sub(I);
    if Abs(AbsoluteNorm(s)) ge Abs(AbsoluteNorm(F!m)) then
      s := m;
    end if;
  end if;
  s := F!s;
  assert s in I;
  return s;
end function;

// Find a small element z in I^-1
// Return the integral ideal z*I and z

function reduce_ideal(I : class:=false)
  z := small_element(I^-1 : class:=class);
  zI := z*I;
  return Order(I) !! zI, z;
end function;

// Find nice inverses under the residue map res of the elements in seq,
// ie they have small coordinates w.r.t the power basis of the field
// (Called only by getU)

function nice_lifts(seq, res)
  OK := Domain(res);  K := NumberField(OK);  d := Degree(K);
  k := Codomain(res);  p := #k;
  error if not IsPrime(p), "nice_lift not implemented for degree > 1"; 
//    return [a@@res : a in seq]; end if;
  basK := [K.1^i : i in [0..d-1]];
  bas := [Integers()| b @res @@res : b in basK];
  assert bas[1] eq 1;
  lifts := [OK| ];
  // For a in seq, let n < p be an integer lift of a.  We assume bas[1] = 1.
  // Find x0,x1,..,xd s.t  x0*p + sum of xi*bas[i] = n   with all xi small
  // Equiv, via x1 :-> x1-n, find a point close to [n/p,-n,0 .. 0] in the lattice 
  //   x0*p + sum of xi*bas[i] = 0  close to [n/p,-n,0 .. 0]
  C := Matrix(Integers(), d+1, 1, [p] cat bas);
  L := Lattice(Kernel(C));  assert Dimension(L) eq d;
//L := Lattice(HKZ(BasisMatrix(L))); // HKZ is currently not in the released version
  for a in seq do  
    n := Integers()! (a@@res);
    if n in {0,1} then Append(~lifts, OK!n); continue; end if;
    /*
    w := Vector([0,-n] cat [0: i in [2..d]]);
    const := 100;
    repeat
printf "CloseVectors with constant %o ... ", const; time
      vecs := CloseVectors(L, w, const*Ceiling(p^(2/d)) : Max:=1); 
      const *:= 10;
    until not IsEmpty(vecs);
    v := Eltseq(vecs[1][1]);
"v =", v;
    v[2] +:= n;
"v =", v;
    */
    // CloseVectors seem to be totally screwed up!!
    // Work around -- project w onto L in a naive iterative way
    w := Vector([0,n] cat [0: i in [2..d]]);  assert bas[1] eq 1;
    ww := w;
    wproj := Parent(w)!0;
    repeat
      normww := Round(Norm(ww));
      for b in Basis(L) do
        c := Round(InnerProduct(ww,b)/Norm(b));
        ww := ww - c*b;  wproj := wproj + c*b;
      end for;
      assert wproj in L and w - wproj eq ww;
    until Round(Norm(ww)) eq normww; // loop has reached a fixed point
    v := ww;
assert n eq v[1]*p + &+[ v[i+1]*bas[i] : i in [1..4]];
    l := &+[OK| v[i+1]*basK[i] : i in [1..d] ];
    assert l@res eq a;
    Append(~lifts, l);
  end for;  
assert &and[ lifts[i] @res eq seq[i] : i in [1..#seq] ];
  return lifts;
end function;

// This is Algorithm 2.2 from Denis Simon's paper "Solving quadratic equations"
// applied to a matrix M over a number field at a prime P
// (Called only by minimise_qf_over_nf)

function getU( M, P)
  K := NumberField(BaseRing(M));
  OK := Integers(K);  assert Order(P) eq OK;
  k, res := ResidueClassField(OK, P);
  n := Nrows(M);  assert n eq Ncols(M);
  M0 := M;
  bool, M := IsCoercible(MatrixRing(OK,n), M);
  error if not bool, "in getU, the given matrix must be integral";
  U := IdentityMatrix(K,n);
  i := n; d := 0;
  while i gt 0 do
    j := i+d;
    while j gt 0 and Valuation(M[i,j],P) gt 0 do
      j -:= 1;
    end while;
    if j eq 0 then
      d +:= 1; i -:= 1; j := i+d;
      continue;
    end if;
    if j lt i+d then
      perm := [1..n]; perm[j] := i+d; perm[i+d] := j;
      T := PermutationMatrix(K, perm);
      M *:= T;  U *:= T;
    end if;
    r := M[i,i+d] @ res;  assert r ne 0;
    u := (1/r) @@ res;
    for k := 1 to j-1 do
      a := u*M[i,k];
      a := a @res @@ res; // try to reduce mod P
      T := IdentityMatrix(K,n);  T[i+d,k] := -a;
      M *:= T;  U *:= T;
    end for;
    M := Parent(M)! [m @res @@res : m in Eltseq(M)]; // try to reduce mod P
    i -:= 1;
  end while;
  U := Matrix(OK,n,n, nice_lifts( [m@res : m in Eltseq(U)], res) );
  resM0 := Matrix(k,n,n, [m @res : m in Eltseq(M0)]);
  resU := Matrix(k,n,n, [m @res : m in Eltseq(U)]);
  assert n-d eq Rank(resM0);
  assert Kernel(Transpose(resM0)) eq RowSpace(Transpose(Submatrix(resU,1,1,n,d)));
  return MatrixRing(OK,n)! U, d;
end function;

// Transform a quadratic form to remove certain factors from the discriminant 
// Currently only removes primes those primes above integers in 'primes' for which
// the discriminant has valuation at least 2 and the corank of the reduced matrix is 1.
// Currently assumes primes arising are principal.

// Currently not called anywhere!

function minimise_qf_over_nf(M, primes) // Mtrx, SetEnum -> Mtrx, Mtrx
  K := NumberField(BaseRing(M));
  OK := Integers(K);
  assert IsSymmetric(M);
  M0 := M;
  n := Nrows(M);
  disc := Determinant(M);
  TT := IdentityMatrix(OK,n);
  Ps := &cat[ [Ideal(tup[1]) : tup in Decomposition(K,p)] : p in primes ];
  Ps := [P : P in Ps | Valuation(disc,P) gt 0];
  Sort(~Ps, func<P1,P2| Norm(P2)-Norm(P1)> );
  for P in Ps do 
    if Minimum(P) lt 100 then continue; end if;
    k, res := ResidueClassField(P);
    Mk := Matrix(k,n,n, [res(m) : m in Eltseq(M)] );
    ker := Kernel(Mk);
    r := Rank(Mk);  assert r gt 0; // assuming we divided out the content
    v := Valuation(disc,P);
    if r eq 1 and v ge 2 then
"Prime above", Minimum(P), "of degree", InertiaDegree(P), ": val =", v, "rank =", r;
"Gram matrix =", MatrixRing(K,n)! M;
"Disc =", Norm(Determinant(M));
"Disc primes =", prime_divisors(Norm(Determinant(M)), primes);
      // scale out a square factor from one variable
      U,d := getU( M, P);  assert d eq 1;
      M := Transpose(U)*M*U;
      TT := TT*U;
assert Valuation(M[1,1],P) ge 2 and &and [Valuation(M[1,j],P) ge 1 : j in [2..n]];
      bool, t := IsPrincipal(P);  assert bool;      
      T := DiagonalMatrix([1/t,1]);
      M := MatrixRing(OK,n)! (T*M*T);
      TT := TT*T;
      assert ideal<OK| disc> eq P^2 * ideal<OK| Determinant(M)>;  
      disc := Determinant(M);
    end if;
  end for;
  TT := MatrixRing(K,n)! TT;
  assert M eq Transpose(TT)*M0*TT;
  return M, TT;
end function;

// TO DO: option to just do a naive diagonal form

intrinsic DiagonalForm(C::CrvCon[FldAlg]) -> RngMPolElt, Mtrx, SeqEnum
{A (carefully chosen) diagonal form of the equation of the plane conic C
 defined over a number field.  Also returns the transformation matrix}

  K := BaseRing(C);  
  M := Matrix(C);
  _<X,Y,Z> := Parent(Equation(C));

  if IsDiagonal(M) then 
    return DefiningPolynomial(C), IdentityMatrix(K,3), {}; 
  end if;

  require IsAbsoluteField(K): "Conic should be over an absolute extension of Q"; 
  OK := Integers(K);

  if not IsIntegral(K.1) then // do obvious reduction (TO DO: more efficiently)
    denom := Denominator(K.1);
    if not IsIntegral(denom*K.1) then
      denom *:= LCM([ Denominator(c) : c in Coefficients(MinimalPolynomial(denom*K.1)) ]);
      assert IsIntegral(denom*K.1);
    end if;
    KK := NumberField(MinimalPolynomial(denom*K.1));
    KtoKK := iso< K -> KK | 1/denom*KK.1 >;
    KKtoK := iso< KK -> K | denom*K.1 >;
    Cmat := SymmetricMatrix(DefiningPolynomial(C)); 
    CKKmat := Matrix(KK, 3,3, [c@KtoKK : c in Eltseq(Cmat)] );
    diagKK, TKK, primes := DiagonalForm(Conic(CKKmat));
    diagmat := Matrix(K, 3,3, [c@KKtoK : c in Eltseq(SymmetricMatrix(diagKK))] );
    diagpol := diagmat[1,1]*C.1^2 + diagmat[2,2]*C.2^2 + diagmat[3,3]*C.3^2;
    TK := Matrix(K, 3,3, [c@KKtoK : c in Eltseq(TKK)] );
    return diagpol, TK, primes;
  end if;
  
  vprint Conic: "Diagonalizing conic ... "; 
  IndentPush();

  M0 := M;
  TT := IdentityMatrix(OK,3);
  
  // Scale so coefficients are integral with small gcd
  content := ideal< OK | Eltseq(M) >;
  vprintf Conic: "Trying to remove content ... "; 
  vtime Conic:
  _,scaling := reduce_ideal(content); 
  M := scaling*M; 
  content := scaling*content;

  vprintf Conic: "Factoring the remaining content ... "; 
  vtime Conic: 
  primes := prime_divisors(Minimum(content), {});

  disc := OK! Determinant(M);
  vprintf Conic: "Factoring the discriminant ... "; 
  vtime Conic: 
  primes join:= prime_divisors(Minimum(disc*OK), primes);
/*
  M, T := minimise_qf_over_nf(M, primes);
  TT := Transpose(T) * TT;
  disc := OK! Determinant(M);
  M := MatrixRing(K,3)! M;
*/
  // Change of vars to make M[1,1] nonzero, and put smallest diag coeff first
  // TO DO: if a = 0, use solution [1,0,0] to transform to a nice conic
  heights := [(M[i,i] eq 0) select Infinity()  
                             else  AbsoluteLogarithmicHeight(M[i,i]) : i in [1..3]];
  Sort(~heights, ~perm);
  T := PermutationMatrix(K, perm);
  M := T*M*Transpose(T);
  TT := T * TT;
  if M[1,1] eq 0 then 
    T := Matrix(K,3,3, [1,1,0, 0,1,0, 0,0,1]);
    repeat
      M := T*M*Transpose(T);
      TT := T * TT;
    until M[1,1] ne 0;
  end if;
  // If two cross terms are zero, permute so M[1,2] = M[1,3] = 0
  if M[1,2] eq 0 and M[2,3] eq 0 and M[1,3] ne 0 then
    T := PermutationMatrix(K, [1,3,2]);
    M := T*M*Transpose(T);
    TT := T * TT;
  elif M[1,3] eq 0 and M[2,3] eq 0 and M[1,2] ne 0 then
    T := PermutationMatrix(K, [3,2,1]);
    M := T*M*Transpose(T);
    TT := T * TT;
  end if;

  if not can_factor(M[1,1], 1) then
    F := M[1,1]*X^2 + 2*M[1,2]*X*Y + 2*M[1,3]*X*Z + M[2,2]*Y^2 + 2*M[2,3]*Y*Z + M[3,3]*Z^2;
    found := false;
    L := StandardLattice(3);
    N := 0;

    vprintf Conic: "Looking for an easily factorable value: ";
    vtime Conic:
    while not found do 
      N +:= 1;
      if N gt 10^4 then
        "WARNING!!! Have not found an easily factorable value of "*
                   "the quadratic form. Something is probably wrong!";
      end if;
      effort := (N le 10) select 0 else 1;
      for tup in ShortVectors(L, N, N) do
        XYZ := Eltseq(tup[1]);
        if XYZ[1] eq 0 then continue; end if; // because of choice of T below
        if GCD(XYZ) ne 1 then continue; end if;
        value := Evaluate(F, XYZ);
        found, _, primes1 := can_factor(value, effort);
        if found then break; end if;
        vprintf Conic: ".";
      end for; 
    end while;
    primes join:= primes1;
  
    // Change variables by a matrix with XYZ as the first row
    x,y,z := Explode(XYZ);
    T := Matrix(3, [K| x,y,z, 0,1,0, 0,0,1]);
    M := T*M*Transpose(T);
    TT := T * TT;
    assert value eq M[1,1];
  end if;

  a:= M[1,1]; b:= 2*M[1,2]; c:= 2*M[1,3]; d:= M[2,2]; e:= 2*M[2,3]; f:= M[3,3];
  T := Matrix(K,3,3, [2*a,b,c, 0,1,0, 0,0,1]) ^-1;
  M := 4*a*Transpose(T)*M*T;
  assert M eq SymmetricMatrix(X^2 + 4*a*(d*Y^2 + e*Y*Z + f*Z^2) - (b*Y+c*Z)^2);
  TT := Transpose(T) * TT;
  scaling *:= 4*a;
  M1 := Submatrix(M, 2,2,2,2); // the Y,Z part
  disc1 := OK! Determinant(M1);
  primes join:= prime_divisors(Norm(disc1), primes);
/*
  M1, T := minimise_qf_over_nf(M1, primes);
  TT := DiagonalJoin(Matrix(K,1,1,[1]), Transpose(T)) * TT;
  disc1 := OK! Determinant(M1);
  M1 := MatrixRing(K,2)! M1;
*/

  // Does the 2x2 part factor? if so, return trivial diagonal form
  // (this step is essential because if it factors, we won't find nearly-prime values)
  // TO DO: this merely pushes the hard factorization into T, so may still lead to problems 
  a := M1[1,1]; b := 2*M1[1,2]; c := M1[2,2];
  triv := false;
  if a eq 0 then
    triv := true;
    T := Matrix(K,3,3, [1,0,0, 0,b,0, 0,c,1]) ^-1;
  else
    triv, r := HasRoot(Polynomial([K| c, b, a ]));
    if triv then
      T := Matrix(K,3,3, [1,0,0, 0,1,a, 0,-r,a*r+b]) ^-1;
    end if;
  end if;
  if triv then
    vprint Conic: "Found a solution, returning a trivial diagonal form";
    // so far T transforms M to X^2 + Y*Z; now make it X^2 + Y^2 - Z^2
    T := Matrix(K,3,3, [1,0,0, 0,1,1, 0,-1,1]) * T;
    M := DiagonalJoin(IdentityMatrix(K,1), M1);
    M := T*M*Transpose(T);
    TT := T * TT;
    assert Eltseq(M) eq [1,0,0, 0,1,0, 0,0,-1]; 

  else 
    // The form in Y,Z given by M1 does not factor
    F1 := X^2 + M1[1,1]*Y^2 + 2*M1[1,2]*Y*Z + M1[2,2]*Z^2;
    vprintf Conic: "Looking for an easily factorable value of the 2x2 part: ";
    vtime Conic:
    for i := 1 to 10^10 do 
      if i gt 10^3 then 
        "WARNING!!! Have not found an easily factorable value of "*
                   "the quadratic form. Something is probably wrong!";
      end if;
      effort := (i le 5) select 0 else 1;
      for j in [0..i], s in [1,-1] do 
        if GCD(i,j) ne 1 then continue j; end if; 
        XYZ := [0, i, s*j];
        value := Evaluate(F1, XYZ);
        found, _, primes1 := can_factor(value, effort);
        if found then break i; end if;
        vprintf Conic: ".";
      end for; 
    end for; 
    primes join:= primes1;

    // want to diagonalise with one of the coeffs being F1(XYZ)
    // first do trivial change of basis to get the value we can factor as a diagonal coeff
    h,i,j := Explode(XYZ);  assert h eq 0;
    g,jj,ii := XGCD(i,j);  assert g eq 1 and i*jj + j*ii eq 1;
    T := Matrix(K,3,3, [1,0,0, 0,i,j, 0,-ii,jj]);
    M := DiagonalJoin(Matrix(K,1,1,[1]), M1);
    M := T*M*Transpose(T);
    TT := T * TT;
    d:= M[2,2]; e:= M[2,3]; f:= M[3,3];
    T := Matrix(K,3,3, [1,0,0, 0,1/d,0, 0,-e/d,1]); // diagonalize 2x2 part
    T := Matrix(K,3,3, [0,1,0, 1,0,0, 0,0,1]) * T;  // swap X and Y
    M := d*T*M*Transpose(T);
    TT := T * TT;
    scaling *:= d;
    assert &and [IsIntegral(m) : m in Eltseq(M)];
    assert M[1,1] eq 1 and M[2,2] eq d and M[3,3] eq d*f-e^2;
    assert d*f-e^2 eq disc1; 

  end if; // triv

  assert M eq scaling*TT*M0*Transpose(TT);
  assert IsDiagonal(M);
  Fdiag := M[1,1]*X^2 + M[2,2]*Y^2 + M[3,3]*Z^2;
  IndentPop();
  return Fdiag, TT, primes;
end intrinsic;

// Check means check local solubility (if false, error may result if not soluble)

intrinsic HasRationalPoint(C::CrvCon : Check:=true) -> BoolElt, Pt
{True iff the conic curve C has a point over its ground field.
 If true, also returns one point.  The conic may be over the rationals, 
 the integers, a number field, a finite field, or a rational function field.}
    K := BaseRing(C);

    if Type(K) in {FldRat, FldFin, RngInt} then
       return InternalHasRationalPoint(C);

    elif ISA(Type(K), FldAlg) and Degree(K) eq 1 then // stupid case, K is a trivial extension
       CC := ChangeRing(C, BaseField(K));
       bool, pt := HasRationalPoint(CC);
       if bool then
          return bool, C! Eltseq(pt);
       else 
          return false, _;
       end if;

    elif ISA(Type(K), FldAlg) then 
       // Code doesn't work if K has stupid defining poly (not monic and integral), so do obvious reduction
       require IsSimple(K) : "The base field must be a simple extension";
       fK := AbsoluteMinimalPolynomial(K.1);
       den := LCM([Denominator(c) : c in Coefficients(AbsoluteMinimalPolynomial(K.1))]);
       if den ne 1 or not IsMonic(DefiningPolynomial(K)) then
         assert IsIntegral(den*K.1);
         KK := NumberField(MinimalPolynomial(den*K.1)); // KK has same base as K
         Embed(KK, K, den*K.1);
         bool, pt := HasRationalPoint(ChangeRing(C, KK));
          if bool then
             return bool, C! Eltseq(pt);
          else 
             return false, _;
          end if;
       end if;
       
       // TO DO: store completions somehow, to avoid recreating them in every call to IsLocallySolvable
       Cdiag, TT, primes := DiagonalForm(C);
       Cdiag1 := Conic(ProjectiveSpace(Parent(Cdiag)), Cdiag);
       // Check local solubility first (since people might call this when they should call that)
       if Check and not IsLocallySolvable(Cdiag1) then
          return false, _;
       end if;
       coeffs := [MonomialCoefficient(Cdiag, Pol.i^2) : i in [1..3]] where Pol is Parent(Cdiag);
       assert &and [c ne 0 : c in coeffs];
       rel := not IsAbsoluteField(K);
       if rel then
         Kabs := AbsoluteField(K);
         coeffs := [Kabs!c : c in coeffs];
       end if;
//"Solving diagonal conic"; "   ", coeffs[1]; "   ", coeffs[2]; "   ", coeffs[3];
       bool, soln_diag := solve_diagonal_conic(coeffs : Primes:=primes);
       if not bool then 
          return false,_; 
       end if;
       if rel then
          ChangeUniverse(~soln_diag, K);
       end if;
       soln := Vector(soln_diag) * TT;
       soln := C(K)! Eltseq(soln);
       return true, soln;

    elif Type(K) eq FldFunRat then
       F := BaseField(K);
       require Type(F) eq FldRat or ISA(Type(F),FldNum) or IsFinite(F) and Characteristic(F) ne 2:
         "If the base field of the conic is a function field, it must be a "*
         "rational function field over Q or over a finite field of odd characteristic";
       return HasRationalPoint_FldFun(C);

    elif ISA(Type(K), FldFunG) then
       require Characteristic(K) ne 2 : "Not implemented for characteristic 2";
       Cdiag, t := DiagonalForm(C);
       Pol := Parent(Cdiag);
       a := MonomialCoefficient(Cdiag, Pol.1^2);
       b := MonomialCoefficient(Cdiag, Pol.2^2);
       c := MonomialCoefficient(Cdiag, Pol.3^2);
       L := ext< K | Polynomial([K| b/a, 0, 1]) >;
       bool, y := IsSquare(-b/a);
       if bool then
         pt := [1, y, 0];
       else
         bool, sol := NormEquation(L, -c/a);
         if not bool then
           return false, _;
         else
           pt := Eltseq(sol[1]) cat [1];
         end if;
       end if;
       return true, C(K)!pt; // this checks the solution

    else
       // TO DO(?) local fields have NormEquation implemented too
       require false: "Not implemented for conics over this kind of base field";

    end if;
end intrinsic;

intrinsic RationalPoint(C::CrvCon) -> Pt
    {A point on the conic C over its ground field, if one exists.
    The conic may be over the rationals, the integers, a number field,
    a finite field, or a rational function field.}
    require Type(BaseRing(C)) in {RngInt,FldRat,FldFin,FldFunRat} :
        "Argument must be defined over the integers, rationals, " *
        "a finite field, or a rational function field.";
    bool, P := HasPoint(C);
    require bool : "Argument does not have a rational point";
    return P;
end intrinsic;

intrinsic ReducedPoint(C::CrvCon) -> Pt
    {Same as RationalPoint}
    require Type(BaseRing(C)) in {RngInt,FldRat,FldFin,FldFunRat} :
        "Argument must be defined over the integers, rationals, " *
        "a finite field, or a rational function field.";
    bool, P := HasPoint(C);
    require bool : "Argument does not have a rational point";
    return P;
end intrinsic;

intrinsic Random(C::CrvCon : Bound:=10^9, Reduce:=false) -> Pt
    {A point of the conic (over the rationals, integers, or a
    finite field), if one exists.}
    require Type(BaseRing(C)) in {RngInt,FldRat,FldFin} :
        "Argument must be defined over the integers, rationals " *
        "or a finite field.";
    if Type(BaseRing(C)) eq FldFin then return HasPoint(C); end if;
    bool, _ := HasPoint(C);
    require bool : "Argument does not have a rational point";
    require Bound gt 0 : "Bound must be positive";
    P:=DefiningEquations(Parametrization(C));
    x:=Random(-Bound,Bound); y:=Random(-Bound,Bound);
    pt:=C![Evaluate(p,[x,y]) : p in P];
    if Reduce eq true then pt:=Reduction(pt); end if;
    return pt;
end intrinsic;
