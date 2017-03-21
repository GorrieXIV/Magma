freeze;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//  Reduction of binary quartics over number fields                  //
//                                                                   //
//  Steve Donnelly                                                   //
//  (with some functions written by Tom Fisher)                      //
//                                                                   //
//  Latest version: November 2013                                    //
//                                                                   //
///////////////////////////////////////////////////////////////////////

Q := Rationals();

function model_is_over_Q(model)
  return CanChangeUniverse(Eltseq(model), Q);
end function;

function ConjMat(M)
  if ISA(Type(BaseRing(M)), FldRe) then
    return M;
  else
    return Matrix(Ncols(M), [Conjugate(m): m in Eltseq(M)]);
  end if;
end function;

function TwoTorsionOrbits(E)
  a1,_,a3 := Explode(aInvariants(E));
  b2 := Explode(bInvariants(E));
  c4,c6 := Explode(cInvariants(E));
  K := BaseRing(E);
  P := PolynomialRing(K); X := P.1;
  F := X^3 - 27*c4*X - 54*c6;
  FF := [f[1] : f in Factorization(F)];
  function torspt(L,rt)
    x := (rt - 3*b2)/36;
    return E(L)! [x, -(a1*x + a3)/2];
  end function;
  TT := <torspt(K,Roots(f)[1][1]) : f in FF | Degree(f) eq 1>;
  if exists(f){f : f in FF | Degree(f) gt 1} then
    L := NumberField(f : Check:=false);
    Append(~TT, torspt(L,L.1));
  end if;
  return TT;
end function;

function TwoTorsionOrbitsFromPrevious(E, TTPrev);
  E0, TT0 := Explode(TTPrev);
  bool, phi := IsIsomorphic(E0, E); assert bool;
  TT := < pt@phi : pt in TT0 >;
  // assert forall{T: T in TT | 2*T eq E!0};
  return TT;
end function;

function torsmat2(quartic,xT)
  a,b,c,d,e := Explode(Eltseq(quartic));
  phi := (-1/12)*xT;
  alpha1 := 4*a*phi - 8*a*c + 3*b^2;
  alpha2 := b*phi - 6*a*d + b*c;
  alpha3 := -2/3*phi^2 + 2/3*c*phi - 3*b*d + 4/3*c^2;
  M := Matrix(2,[-alpha2,-alpha3,alpha1,alpha2]);
  if alpha1 eq 0 then 
    beta1 := alpha2;
    beta2 := 1/3*phi^2 + 2/3*c*phi - 12*a*e + 1/3*c^2;
    beta3 := d*phi - 6*b*e + c*d;
    M := Matrix(2,[-beta2,-beta3,beta1,beta2]);
  end if;
  return M;
end function;

function TwoTorsionMatrices(E,quartic,torspts)
  assert cInvariants(E) eq cInvariants(quartic); // this is essential
  a1,a2,a3 := Explode(aInvariants(E));
  mats := < torsmat2(quartic, 36*T[1] + 3*(a1^2 + 4*a2)) : T in torspts >;
  return mats;
end function;

function Emb(M, indx, prec)
  return Matrix(2, [Conjugate(M[i,j],indx:Prec:=prec) : i,j in [1..2]]);
end function;

function Embs(M, K, u, prec)
  L := BaseRing(M);
  inds := L eq K select [[u]] else [[u,v] : v in [1..Degree(L,K)]];
  return [Emb(M,i,prec): i in inds];
end function;

// Reduction covariants associated to the given binary quartic
// over a number field K, given as lists of symmetric or Hermitian
// matrices corresponding to the real and complex embeddings of K

// The standard action on the ReductionCovariants corresponding to 
// the usual left action model :-> T*model 
// is M :-> Conjugate(T)*M*Transpose(T)

// TO DO: is there much value in TwoTorsionOrbitsFromPrevious?

function ReductionCovariants(model, prec : TTPrev:=0)
  epsilon := 10^(-prec div 2);
  E := Jacobian(model);
if true or TTPrev cmpeq 0 then
    TT := TwoTorsionOrbits(E);
  else
    TT := TwoTorsionOrbitsFromPrevious(E, TTPrev);
  end if;
  mats := TwoTorsionMatrices(E, model, TT);
  AA := [**];
  K := NumberField(BaseRing(model));
  n := Degree(K);
  nr := Signature(K);
  for i in [1 .. nr] cat [nr+1 .. n by 2] do
    MM := &cat[Embs(mat,K,i,prec): mat in mats];
    assert #MM eq 3;
    MM := [IdentityMatrix(BaseRing(MM[1]),2)] cat MM;
    dets := [Abs(Determinant(M)): M in MM];
    if exists{D: D in dets | D lt epsilon} then
      return false, _, _;
    end if;
    A := &+ [Transpose(ConjMat(MM[i])) * MM[i] / dets[i] : i in [1..4]];
    Append(~AA,A);
  end for;
  return true, AA, <E,TT>;
end function;

// covariants in upper half plane and upper half space;
// standard action is z :-> Inverse(Transpose(T)) * z

function covariants_R(mats, prec)
  epsilon := 10^(-prec div 2);
  R := RealField(prec);
  C := ComplexField(prec);
  covs := [C| ];
  for M in mats do 
    a,b,c,d := Explode(Eltseq(M));
    okay := Abs(b-c) lt epsilon;
    bb := b+c; 
    // solve quadratic by hand
    s2 := R!(4*a*d - bb^2); 
    okay and:= s2 gt epsilon;
    s := Sqrt(s2);
    r := (-bb + s*C.1)/(2*a);
    if not okay then 
      return false, _; 
    end if;
    Append(~covs, r);
  end for;
  return true, covs;
end function;

function covariants_C(mats, prec)
  epsilon := 10^(-prec div 2);
  R := RealField(prec);
  C := ComplexField(prec);
  covs := [CartesianProduct(C,R)| ];
  for M in mats do 
    a,b,bb,c := Explode(Eltseq(M));
    okay := forall{x : x in {a,b+bb,c} | Abs(Im(x)) lt epsilon};
    // covariant = <t,u> in C + R^+ where
    // a|X|^2 + bXZ + conj(b)XZ + c|Z|^2 = a(|X - tZ|^2 + u^2|Z|^2)
    t := -b/a;
    u2 := Real(c/a - Norm(t));
    okay and:= u2 gt epsilon;
    u := Sqrt(u2);
    if not okay then 
      return false, _; 
    end if;
    Append(~covs, <t,u>);
  end for;
  return true, covs;
end function;

function covariants(mats, nr, prec)
  bool, covs_R := covariants_R(mats[1 .. nr], prec);
  if bool then
    bool, covs_C := covariants_C(mats[nr+1 .. #mats], prec);
  end if;
  if bool then
    return true, covs_R, covs_C;
  else
    return false, _, _;
  end if;
end function;

// Minkowski lattice using coordinates re(), im() at complex places,
// with a robust inverse map

function minkowski_lattice(ZK, prec)
  epsilon := 10 ^ (-prec div 2);
  B := Basis(ZK);
  n := Degree(ZK);
  nr := Signature(ZK);
  R := RealField(prec);
  BM := MatrixRing(R, n) ! 0;
  for i := 1 to n do
    for j := 1 to nr do
      BM[i,j] := Real(Conjugate(B[i], j : Precision:=prec));
    end for;
    for j := nr + 1 to n by 2 do
      c := Conjugate(B[i], j : Precision:=prec);
      BM[i,j] := Real(c);
      BM[i,j+1] := Im(c);
    end for;
  end for;
  L := LatticeWithBasis(BM);
  assert Abs(2^(n-nr)*Determinant(L) - Abs(Discriminant(ZK))) lt epsilon;
  BMI := BM ^ -1;
  function from(v)
    w := Vector(v)*BMI;
    ww := [Round(c) : c in Eltseq(w)];
    assert forall{i: i in [1..n] | Abs(w[i]-ww[i]) le 10^-10};
    return &+ [ww[i]*B[i] : i in [1..#B]];
  end function;
  return L, from;
end function;

// lattice with basis corresponding to the given units

function logs(x, prec)
  K := Parent(x);
  n := Degree(K);
  nr := Signature(K);
  return [Log(Abs(Conjugate(x, i : Precision:=prec))) : i in [1..n]];
end function;

function UnitLattice(units, prec)
  B := Matrix([logs(u, prec) : u in units]);
  L := LatticeWithBasis(B);
  return L;
end function;

// Solve s*B = v for s, and return s rounded to integers.
// Includes work-around for the case of a unit lattice
// because Solution only works when B has full rank.

function iSolution(B, v)
  n := Nrows(B);
  d := Ncols(B);
  assert n in {d,d-1};
  if n eq d-1 then
    epsilon := 10.0 ^ (20 - Precision(BaseRing(B)));
    // Assumption: rows must sum to zero
    assert forall{i: i in [1..n] | Abs(&+Eltseq(B[i])) lt epsilon};
    // Add independent row with length M much larger than all coords
    M := Round(10^100 * Max([Abs(x) : x in Eltseq(B) cat Eltseq(v)]) ); 
    B := VerticalJoin(B, Vector(BaseRing(B), [M : i in [1..d]]) );
  end if;
  s := v * NumericalInverse(B : Epsilon:=0.0);
  if n eq d-1 then
    assert Abs(s[d]) lt epsilon;
  end if;
  return [Round(s[i]) : i in [1..n]];
end function;

// TO DO: ClosestVectors(L, v : Max:=1) ought to work

function closest_vector(L, v : coordinates:=false)
  n := Rank(L);
  // Get some w in L, with w close to v
  // TO DO: also try w + s for some short vectors s
  B := BasisMatrix(LLL(L));
  s := iSolution(B, v);
  w := Vector(BaseRing(B),s) * B;

  if coordinates then
    // Get coords of w as a combination of the (fixed) basis of L
    B := BasisMatrix(L);
    c := iSolution(B, w);
    // Check it's a good approximation
    delta := w - Vector(BaseRing(B),c) * B;
    assert Norm(delta) lt 10^-20;
    return true, w, c;
  else
    return true, w;
  end if;
end function;


// Find the best pair (c,d) for the given covariants.
// B is the basis matrix for the image of ZK in Minkowski space.
// Test 'num' short vectors.

function get_cd(covs_R, covs_C, B, ZK : num:=10*2^Degree(ZK), optimize:=0 )
  n := Degree(ZK);
  nr := Signature(ZK);

  xx := [Real(z) : z in covs_R] cat &cat[[Real(z),Im(z)] where z is c[1] : c in covs_C];
  yy := [  Im(z) : z in covs_R] cat &cat[          [u,u] where u is c[2] : c in covs_C];
  assert forall{y : y in yy | y gt 0};

//"Heights:", ChangeUniverse(yy, RealField(4));

  // M = matrix that maps (c,d) in ZK^2 with coords wrt the basis B
  //                  to (c,c*x+d) in two copies of Minkowski space
  // X = matrix representing multiplication by xx in Minkowski space
  X := DiagonalMatrix(xx[1..nr]);
  for c in covs_C do
    a := Real(c[1]);
    b :=   Im(c[1]);
    X := DiagonalJoin(X, Matrix(2, [a, b, -b, a]));
  end for;
  M := BlockMatrix(2, 2, [Parent(B)| B, B*X, 0, B]);

  // apply weightings
  W := DiagonalMatrix(yy cat [1/y : y in yy]);
  G := M * W * Transpose(M);

  // construct lattice (over Z)
  prec := Precision(BaseRing(G));
  GZ := Matrix(Integers(), Ncols(G), 
               [Round(x) : x in Eltseq(10^prec * G)] );
  try
    L := LatticeWithGram(GZ + Transpose(GZ));
  catch ERR
    // "argument is not positive definite"
    error if "positive" notin ERR`Object, ERR; 
"WARNING: Lattice positive definite test failed with precision", prec;
    return false, _, _, _;
  end try;

  // choose short vector with the largest average imaginary part:
  // for each SV, calculate product of |c*z+d|^2 over all places
  cds := [];
  denoms := [];
  N := Ceiling(Minimum(L) * num^(1/n)); // L has rank 2*n
  repeat
    SV := ShortVectors(L, N);
    N := Ceiling(N * 2^(1/n));
    num -:= #SV;

    for sv in SV do
      v := Eltseq(sv[1]);
      if GCD(v) ne 1 then
        continue;
      end if;
      c := ZK! v[1..n];
      d := ZK! v[n+1..2*n];
      I := ideal<ZK|c,d>;
      if Minimum(I) ne 1 then 
        // If I is principal, the corresponding primitive (c,d) is likely 
        // to be among the short vectors, in which case we will find it.
        // It would be much too slow to call IsPrincipal(I) in order to 
        // obtain the primitive (c,d)
        continue;
      end if;
      Append(~cds, <c,d>);
      vM := Vector(BaseRing(M), v) * M;
      // Real:    |c*x+d|^2 + |c*y|^2
      // Complex: |c*z+d|^2 + |c|^2 * u^2
      denoms_R := [vM[n+i]^2 + (vM[i]*yy[i])^2
                  : i in [1 .. nr]];
      denoms_C := [vM[n+i]^2 + vM[n+i+1]^2 + (vM[i]^2 + vM[i+1]^2) * yy[i]^2
                  : i in [nr + 1 .. n by 2]];
      // complex places twice
      Append(~denoms, denoms_R cat &cat[[x,x] : x in denoms_C]);
    end for;

  until num le 0 and #cds gt 0;
//num, #denoms, "Candidates:"; [RealField(4)| &*d : d in denoms];

  inds := [1 .. nr] cat [nr + 1 .. n by 2];
  if optimize eq "prod" then
    _, m := Minimum([&*d : d in denoms]);
  elif optimize eq "height" then
    heights := [ Min([yy[i]/d[i] : i in inds]) : d in denoms];
    _, m := Maximum(heights);
  end if;
  c, d := Explode(cds[m]);
  im1 := [yy[i]/denoms[m][i] : i in inds];
//"Improved heights:", ChangeUniverse(im1, RealField(4));

  return true, c, d;
end function;


// Find a, b such that a*d - b*c = 1

function get_ab(c, d)
  ZK := Parent(c);
  if d eq 0 then
    return ZK!0, ZK!(-1/c);
  elif c eq 0 then
    return ZK!(1/d), ZK!0;
  end if;
  bool, x, y := Idempotents(c*ZK, d*ZK); assert bool;
  b := -x div c;
  a := y div d;
  assert a*d - b*c eq 1;
  return a, b;
end function;


// SL2 reduce with no scaling
// Returns redmodel, trans, height

function ReduceSL2(model)

  K  := BaseRing(model);

  if model_is_over_Q(model) then
     modelQ, trQ := Reduce(ChangeRing(model, Q));
     return ChangeRing(modelQ, K), ChangeRing(trQ, K), Infinity();
  end if;
  
  ZK := LLL(Integers(K));
  n  := Degree(K);
  nr := Signature(K);

  // For verbose:
  RR := RealField(4);              
  CC<i> := ComplexField(4);
  CCRR := CartesianProduct(CC, RR);

  // Translate by upper triangular matrix to shove everything near the middle
  procedure translate(~covs_R, ~covs_C, ~T, LZK, fromLZK)
    xx := Vector([Real(z) : z in covs_R] cat 
                 &cat[[Real(z),Im(z)] where z is c[1] : c in covs_C]);
    ok, w := closest_vector(LZK, xx); assert ok;
    w := Eltseq(w);
    if not IsZero(w) then
      a := ZK ! (w @ fromLZK);
      T1 := Matrix(2, [ZK| 1, -a, 0, 1]);
      T := Transpose(T1)^-1 * T;
      covs_R := [covs_R[i] - w[i] : i in [1..nr]];
      covs_C := [< c[1] - Parent(c[1])! w[nr+2*i-1 .. nr+2*i] , c[2] > 
                  where c is covs_C[i] : i in [1..#covs_C] ];
    end if;
  end procedure;

  // The action by T sending model :-> T * model corresponds to 
  // the action on covariants in upper half planes sending
  //  z :-> Inverse(Transpose(T)) * z

  T := IdentityMatrix(ZK, 2); // T*model = reduced model
  Tprev := {};
  Swap := Matrix(2, [ZK| 0, -1, 1, 0]);

  // Stopping condition -- this gets gradually weakened below
  // TO DO: what should we hope for? 
  ybound := Round(Sqrt(Abs(Discriminant(ZK)))); 
  ybound := 1;

  // TO DO: what precision to start with? has to be the size of the coeffs?
  // but should only use large precision for the calculations where its needed
  model_size := Max([Ceiling(AbsoluteLogarithmicHeight(c)/Log(10)) : c in Eltseq(model)]);
  prec0 := Ceiling(3*model_size/100)*100; // 2 is not enough (Kazuo Matsuno example)
  prec0 := Max(prec0, 100*n);

  vprintf Reduction : "Model has height 10^%o\n", model_size;

  inc := 0;
  iterations := 0;
  best := <T, 0, 0, 0>;     // will be < T, covs_R, covs_C, ymin >
  best_model := model;

  model_over_Q := false;
  finished     := false;
  final        := false;

  while not finished and not model_over_Q do 

    inc +:= 1;
    prec := inc*prec0;
    increased_prec := true;
    vprint Reduction: "Initializing with precision", prec;
if inc ge 20 then
 "WARNING: 'Reduce' seems to need precision", prec;
end if;
    R := RealField(prec);
    epsilon := 10^(-prec div 2); // used in assertions

    LZK, fromLZK := minkowski_lattice(ZK, prec);

    while not finished do 
      iterations +:= 1;
      Tprev join:= {T,-T};
 
      // Recompute the covariants regularly (TO DO: how often?)
      MM := 1;
      if increased_prec or (iterations-1) mod MM eq 0 then
        m := tr*model where _,tr is IsTransformation(2, <K!1, T>);
        bool, mats, TT := ReductionCovariants(m, prec :
                          TTPrev := assigned TT select TT else 0);
//if not bool then printf " BAD RC "; end if;
        if bool then
          bool, covs1_R, covs1_C := covariants(mats, nr, prec);
//if not bool then printf " BAD cov "; end if;
        end if;
        if not bool then
          break; // increase precision and re-initialize
        end if;
        if increased_prec then
          increased_prec := false;
          covs_R := covs1_R;
          covs_C := covs1_C;
          // also need the best covariants to the same precision
          // TO DO: really?
          mbest := tr*model where _,tr is IsTransformation(2, <K!1, best[1]>);
          bool, mats := ReductionCovariants(mbest, prec : TTPrev:=TT);
//if not bool then printf " BAD RC (best) "; end if;
          if bool then
            bool, covs_best_R, covs_best_C := covariants(mats, nr, prec);
//if not bool then printf " BAD cov (best) "; end if;
          end if;
          if not bool then
            break; // increase precision and re-initialize
          end if;
          best := < best[1], covs_best_R, covs_best_C, 
                    Min([Im(z) : z in covs_best_R] cat [z[2] : z in covs_best_C]) >;
        else
// TO DO (important)
// some issues here, sometimes causing unnecessary precision increase
          // check we didn't lose too much precision
          // (transformed covs may be lower half plane, so flip them first) [TO DO: still true?]
          flag := false;
          covs0_R := [Im(c) gt 0 select c else Conjugate(c) : c in covs_R];
          for i := 1 to nr do
            rp :=      Abs(covs0_R[i]   -   covs1_R[i]) / 
                  Max( Abs(covs0_R[i]), Abs(covs1_R[i]) );
            if rp gt epsilon then
//lrp := Round(-Log(10,rp));
//"WARNING!!! Real covariants were only correct to relative precision", lrp;
              flag := true;
            end if;
          end for;
          for i in [1..#covs_C], j in [1..2] do
            if j eq 1 and IsZero(covs1_C[i,1]) then continue; end if;
            rp :=      Abs(covs_C[i,j]   -   covs1_C[i,j]) / 
                  Max( Abs(covs_C[i,j]), Abs(covs1_C[i,j]) );
            if rp gt epsilon then
//lrp := Round(-Log(10,rp));
//"WARNING!!! Complex covariants were only correct to relative precision", lrp;
              flag := true;
            end if;
          end for;
          if flag then  // increase precision and re-initialize
            break;
          end if;
          covs_R := covs1_R;
          covs_C := covs1_C;
        end if;
      end if;

      vprintf Reduction, 3:
        "Current model:\n%o\n", Equation(tr*model) where _,tr is IsTransformation(2, <K!1, T>);
      vprintf Reduction, 2:
        "Current covariants:    %o %o\n", ChangeUniverse(covs_R, CC), ChangeUniverse(covs_C, CCRR);

      bool, c, d := get_cd (covs_R, covs_C, BasisMatrix(LZK), ZK : 
                            optimize := (final select "height" else "prod") );
      if not bool then
        break; // increase precision and start again
      end if;

      a, b := get_ab(c, d);
      T1 := Matrix(2, [a, b, c, d]);
      T := Transpose(T1)^-1 * T;
      covs_R := [ (Conjugate(a,i:Precision:=prec)*covs_R[i] + Conjugate(b,i:Precision:=prec)) / 
                  (Conjugate(c,i:Precision:=prec)*covs_R[i] + Conjugate(d,i:Precision:=prec)) 
                : i in [1..nr]];
      for i := 1 to #covs_C do
        zi := covs_C[i];
        ii := nr + 2*i - 1;
        ai := Conjugate(a, ii : Precision:=prec);
        bi := Conjugate(b, ii : Precision:=prec);
        ci := Conjugate(c, ii : Precision:=prec);
        di := Conjugate(d, ii : Precision:=prec);
        den := Norm(ci*zi[1] + di) + Norm(ci*zi[2]);
        covs_C[i] := < ( (ai*zi[1] + bi)*Conjugate(ci*zi[1] + di) + ai*Conjugate(ci)*zi[2]^2 ) / den,
                       zi[2] / den >;
      end for;

      vprintf Reduction, 2: 
        "Improved covariants:   %o %o\n", ChangeUniverse(covs_R, CC), ChangeUniverse(covs_C, CCRR);

      translate(~covs_R, ~covs_C, ~T, LZK, fromLZK);

      vprintf Reduction, 2: 
        "Translated covariants: %o %o\n", ChangeUniverse(covs_R, CC), ChangeUniverse(covs_C, CCRR);

      // Keep track of the best so far (measured by inf of imaginary parts)
      ymin := Min([R| Im(z) : z in covs_R] cat [R| z[2] : z in covs_C]);
assert ymin gt 0; // can they get flipped?
      if ymin ge best[4] then
        vprint Reduction: "Best height now: ", RR! ymin;
        best := < T, covs_R, covs_C, ymin >;
        // reduced model over Q ?
        best_model := tr * model where _,tr := IsTransformation(2, <K!1, T>);
        if model_is_over_Q(best_model) then
          model_over_Q := true;
          break;
        end if;
      end if;

      if T notin Tprev then
        Tprev join:= {T,-T};
      elif not final then
        final := true;
      else
        finished := true;
      end if;

    end while;

  end while;

  _, tr := IsTransformation(2, < K!1, best[1] >);

  if model_over_Q then
    modelQ, trQ := Reduce(ChangeRing(best_model, Q));
    return ChangeRing(modelQ, K), ChangeRing(trQ, K) * tr, Infinity();
  end if;

  return best_model, tr, best[4];

end function;


intrinsic Reduce(model::ModelG1[FldAlg] : SL2:=false, Tidy:=false)
       -> ModelG1, TransG1
{A reduced model equivalent to the given genus one model
(of degree 2, without cross terms, defined over a number field)}
  
  K  := BaseRing(model);
  ZK := LLL(Integers(K));
  n  := Degree(K);
  ur := UnitRank(K);

  require IsAbsoluteField(K) : 
          "The base field must be an absolute extension of Q";

  require #Eltseq(model) eq 5 : 
          "Implemented only for models without cross terms";

  require forall{c : c in Eltseq(model) | IsIntegral(c)} : 
          "The given model does not have integral coefficients";

  redmodel, tr, h := ReduceSL2(model);

  // GL2 case

  if not SL2 and ur gt 0 then
    // apply diag(u, 1) for u in U/U^2 and SL2 reduce each of them

    U, mU := IndependentUnits(K : Al:="ClassGroup");
    units := [ (U![x: x in c]) @ mU : c in 
               CartesianProduct([{0}] cat [{0,1} : i in [2.. Ngens(U)]]) ];
    assert units[1] eq 1;

    // calling it again for u = 1
    reds := [* *];
    for u in units[1 .. #units] do 
      vprintf Reduction: "GL2 reduction: trying u = %o\n", K!u;
      _, utr := IsTransformation(2, < K!1, Matrix(2, [u,0,0,1]) >);
      rm1, tr1, h1 := ReduceSL2(utr * redmodel);
      Append(~reds, < rm1, tr1 * utr, h1 >);
    end for;

    _, indx  := Max([t[3] : t in reds]);
    redmodel := reds[indx,1];
    tr       := reds[indx,2] * tr;

    vprintf Reduction: "GL2 reduction: best u = %o\n", K!units[indx];
  end if;

  // Scalings

  scal, T  := Explode(Tuple(tr));

  if ur gt 0 and not model_is_over_Q(redmodel) then
    // Scale quartic by a square unit; worth doing as well as the next step
    // Don't need high precision here

    U, mU := IndependentUnits(K : Al:="ClassGroup");

    lowprec := 100;
    coeffs := [c : c in Eltseq(redmodel) | c ne 0];
    coeffs_logs := [logs(c, lowprec) : c in coeffs];
    // average log sizes
    ll := [ &+ [coeffs_logs[i,j] : i in [1..#coeffs]] / #coeffs 
          : j in [1..#coeffs_logs[1]] ];
    // shift so sum is zero (not essential),
    // divide by 2 because the scaling is by scal^2
    ll_avg := (&+ll)/#ll;
    ll1 := [(l-ll_avg)/2 : l in ll];
    assert Abs(&+ll1) lt 10^(20-lowprec);
    units := [Codomain(mU) | U.i @ mU : i in [2..Ngens(U)]];
    UL := UnitLattice(units, lowprec);
    cv := ClosestVectors(UL, Vector(ll1));
    if IsEmpty(cv) then  // TO DO: means what?
      c := [];
    else
      c := Coordinates(UL, cv[1]);
    end if;
    if exists{x: x in c | x ne 0} then
      scal *:= K! &* [ZK| units[i]^-c[i] : i in [1..#units]];
      vprintf Reduction, 2: "Scaling quartic by square of unit %o\n", scal;
      _,tr := IsTransformation(2, <scal, T>);
      redmodel := tr * model;
    end if;
  end if;

  if Tidy and not model_is_over_Q(redmodel) then
    // Scale quartic by a square: result has integral coeffs,
    // we want coeffs to have small height, and small content
    coeffs := {@ c : c in Eltseq(redmodel) | c ne 0 @};
    prec := 167;
    conjs := [Conjugates(c:Precision:=prec) : c in coeffs];
    W := [Sqrt(&+[Abs(conjs[i,j])^2 : i in [1..#coeffs]]) : j in [1..n]];
    // Note: RHS in ideal constructor must not be a sequence
    content := Factorization(ideal< ZK | coeffs >); 
    assert forall{t: t in content | t[2] ge 0};
    content2 := &* [PowerIdeal(ZK)| t[1] ^ (t[2] div 2) 
                                  : t in content | t[2] ge 2];
    content2i := content2 ^ -1;
    bas2i := Basis(content2i);
    B := Matrix([Conjugates(b:Precision:=prec) : b in bas2i]);
    G := B * DiagonalMatrix(BaseRing(B), W) * Transpose(ConjMat(B));
    G := Matrix(n, [Real(x) : x in Eltseq(G)]);
    L := LatticeWithGram(G + Transpose(G));
    v := ShortestVectors(L)[1];
    try
      c := Coordinates(v);
      ok := true;
    catch ERR
      ok := false;
//"WARNING: Coordinates failed !!!";
    end try;
    if ok then
      scal *:= &+ [K| c[i] * bas2i[i] : i in [1..n]]; 
      if not IsOne(scal) then
        vprintf Reduction, 2: 
          "Scaling quartic by square (non-unit) %o, norm %o\n", 
           scal, Norm(scal);
        // TO DO: if it is a unit, should we use it?
        _, tr := IsTransformation(2, <scal, T>);
        redmodel := tr * model;
      end if;
    end if;
  end if;

  if model_is_over_Q(redmodel) then
    redmodelQ := ChangeRing(redmodel, Q);
    redmodelQ, trQ := Reduce(redmodelQ);
    redmodel := ChangeRing(redmodelQ, K);
    tr := ChangeRing(trQ, K) * tr;
  end if;

  assert forall{c : c in Eltseq(redmodel) | IsIntegral(c)};

  assert redmodel eq tr * model;

  return redmodel, tr;

end intrinsic;


/**********************************************************************************

//////////  Examples  ///////////

SetVerbose("Reduction", 2);

F, ZF, w := nf(x^2 - 5);
E := EllipticCurve([F| 0, 2767587264 ]);
TD := TwoDescent(E); TD; 

F, ZF, w := nf (x^2 - 2);
E := EllipticCurve([0, (220259326464*w + 292251234816) ]);
TD := TwoDescent(E); TD;

F, ZF, w := nf(x^2 - x - 52);
E := EllipticCurve([F| 0, (-29259832766899423680*w - 196872331259043751680) ]);
TD := TwoDescent(E); TD;

F, ZF, w := nf([1, -1, -4, 0, 1]);
E := EllipticCurve([ 0, -1728 * (3*w^3 - 18*w^2 - 32*w + 16) ]);
TD := TwoDescent(E : RemoveTorsion); TD;

//////////  Testing  ///////////

SetVerbose("Reduction", 2);

SetClassGroupBounds("GRH");

x := PolynomialRing(Rationals()).1;
F<w> := NumberField(x^2 + 41);
F<w> := NumberField(x^3 - x^2 - 3*x + 1);

CDB := CremonaDatabase();
for N in [10^1..10^6], EQ in EllipticCurves(CDB, N) do
    E := BaseChange(EQ, F);
    CremonaReference(EQ), Norm(Conductor(E)); E;
    TD := TwoDescent(E : RemoveTorsion, MinRed:=false); TD;
    if #TD gt 0 then
        ProStart();
        TD := TwoDescent(E : RemoveTorsion, MinRed:=true); TD;
        ProShow(20);
    end if;
end for;

for m in [0..10], n in [1..100], c4 in [0..10] do
    E := EllipticCurve([c4, n + m*w]);
    Norm(Conductor(E)); E;
    TD := TwoDescent(E : RemoveTorsion, MinRed:=false); TD;
    if #TD gt 0 then
        ProStart();
        TD := TwoDescent(E : RemoveTorsion, MinRed:=true); TD;
        ProShow(20);
    end if;
end for;

**********************************************************************************/

