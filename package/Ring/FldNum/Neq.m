freeze;

/*
  <example>

 Q:=Rationals();
 E:=RadicalExtension(Q,2,-33);
 F:=RadicalExtension(E,2,-1);
 O:=MaximalOrder(F);
 Oa := MaximalOrder(O);
 Oa := AbsoluteOrder(O);
 K := FieldOfFractions(Oa);

 S := Support(2*3*5*Oa);
 S := [x : x in S];
 #S;
 SUnitGroup(S:Raw);
 U, mU, B := $1;
 SUnitAction(mU, map<FieldOfFractions(Oa) -> E | x :-> Norm(F!x)>, S:Base := B);

 </example>
 <exmaple>
 //example showing the need for mu_exp:
   SetVerbose("ClassGroup", 3);
   SetClassGroupBounds(500);
   SetSeed(1);
   x := PolynomialRing(Rationals()).1;
   K := NumberField(x^4 + 17*x^2 + 7569);
   a := 1/87*(-13*K.1^3 + 910*K.1 + 14181);
   b := 1/174*(K.1^3 + 104*K.1 + 783);
   L := ext< K | Polynomial([ -a, 0, 1]) >;
   SetVerbose("NormEquation", 2);
   SetVerbose("NormEquation", 3);
   NormEquation(L,b);
 </example>
*/

function InduceAut(M, s)
  if ISA(Type(M), ModTupFldElt) then
    l := Eltseq(M);
    l := [ s(x) : x in l];
    return Parent(M)!l;
  elif ISA(Type(M), Mtrx) then
    l := Eltseq(M);
    l := [ s(x) : x in l];
    return Matrix(Nrows(M), Ncols(M),l);
  else
    error "case not supported";
  end if;
end function;

function get_eps (d, Real)
  if Real then
    eps := Log(2+1/72 * Log(2*d)^2/(2*d)^4);
  else
    eps := 1/6 * Log(d) / d^2;
  end if;
  return eps;
end function;

function CF_mu(u, d:Real := false, Chol := false) 
  if Chol cmpeq false then  
    c := PseudoCholeskyForm(u*Transpose(u):Swap); 
           // should be passed in if possible...
  else
    c := Chol;
  end if;
  // if Real then eps should be different.
  // Furthermore, eps should be used in the return statement,
  R := CoefficientRing(c);
  eps := R!get_eps(d, Real);
  r := Nrows(c);
  if r eq 1 then
    return CoefficientRing(c)!1;
  end if;
  pq := &*[CoefficientRing(c)| c[i][i] : i in [1..r-1]];
  h := R!HermiteConstant(r);
  s := Sqrt(h*((1/eps)^2)^r * 2^(3*r-3) *(1+r)* pq);
  m := 1/c[r-1][r-1];
  m := Maximum(m, s);
  return m;
end function;  

function CF_prec(M, mu)
  d := 1/(2*mu^2*OperatorNorm(M:Norm := Infty) * Nrows(M));
  return Ceiling(-Log(d) / Log(10));
end function;


function NiceSolution(K, sol, mU, Base, S)
  
  vprint NormEquation, 2: "Improve solution, starting with:", sol;

  /* OK, now we have a "Raw" representation of a solution to the equation.
   * now the idea is to "nicyfy it by applying LLL techniqes.
   * We get the LogLattice, supplement it by the valuation vectors
   * and finally append the Rhs. As the Rhs is NOT in the lattice, Allan
   * should be able to produce a good reduction of it...
   */

  /* Use decent precision.  (We shouldn't need huge precision, because
   * the input was obtained as a fairly simple combination of S-units
   * given by SUnitGroup, which is supposed to return a reduced basis.)
   */
  prec := 1000;
  R := RealField(prec);

  L := [Logs(x : Precision:=prec) : x in Eltseq(Base)];

  LogBaseMat := Matrix(R, Matrix(L));
  U := Domain(mU);
  KernelGens := [U!x : x in Generators(K)];

  L := CoefficientRing(Base);
  r1, r2 := Signature(L);
  r := r1 + r2;

  // Let's start by reducing the valuation part as much as possible
  // Then we try to reduce the infinite part.
  // maybe (and it's a clear MAYBE) this should be done in one step.
  // It should not. I've tried it and unless s.o. comes up with a great
  // idea how to weight finite and infinite places, it's doomed.

  ValBaseMat := Matrix(Integers(), 
               [ [ Valuation(x, p)*Norm(p) : p in S] : x in Eltseq(Base)]);
  Units_only_S, mq := quo<K | K meet sub<U|[U.i : i in [1 .. r]]>>;
  KernelGens_only_S := [ U!(x@@mq) : x in Generators(Units_only_S)];

  gens := Append(KernelGens_only_S, sol);
  gens := [ mU(x) : x in gens];
  X := Matrix(gens) * ValBaseMat;

  l := #gens;
  vprint NormEquation, 2: "Valuations of the solutions", X[#gens+1..Nrows(X)];
//  "sols (unreduced): ", X[l..Nrows(X)];
  if not false then
    X, T := GramSchmidtReduce(X, l-1);
//    "sols (reduced): ", X[l..Nrows(X)];
    vprint NormEquation, 2: "reduced to", X[#gens+1..Nrows(X)];
    assert T[l][l] eq 1;
    sol +:= &+ [U|T[l][i] * KernelGens_only_S[i] : i in [1..l-1]];
    s := [sol];
  else
    L := LatticeWithBasis(Matrix(X[1..l-1]));
    cc, z := ClosestVectors(L, AmbientSpace(L)!X[l]);
    s := [ sol - &+ [U|Coordinates(y)[i] * KernelGens_only_S[i] : i in [1..l-1]] 
                 : y in cc];
    s := SetToSequence(Set(s));
  end if;

  vprint NormEquation, 2: "After reduction at the finite places:", s[1];
//  "after fin. reduction", s;

  // let's see how far we get WITHOUT the S-Units, so taking Units alone..
  // The 1st generator of U is the torsion part, the next r-1 are the
  // "fundamental" units.
  Units_no_S := sub<U|[U.i : i in [1..r]]>;
  KernelGens_no_S := [U!x : x in Generators(K meet Units_no_S)];
  
  gens := KernelGens_no_S cat s;
  gens := [ mU(x) : x in gens];
  gens := Matrix(R, Matrix(gens));
  X := gens * LogBaseMat;
  scale := 10^(10 + Precision(R)); // the extra is just for ordinary roundoff error
  X := Matrix(Ncols(X), [Round(x*scale) : x in Eltseq(X)]);
  l := Nrows(gens);
/*
"sols (unreduced): ";
[Log(1+&+ [ x*x : x in Eltseq(X[i])]) - 2*Log(scale): i in [1..Nrows(X)]];
*/
  XX, TT, r := LLL(Matrix(X[1..l-#s]));
  assert TT*Matrix(X[1..l-#s]) eq XX;
  assert forall{<i,j> : i in [r+1..Nrows(XX)], j in [1..Ncols(XX)] | XX[i][j] eq 0};
  assert forall{i : i in [1..r] | exists{j : j in [1..Ncols(XX)] | XX[i][j] ne 0}};
  XX := VerticalJoin(Matrix(XX[1..r]), Matrix(X[l-#s+1..l]));
/*
"XX: ";
[Log(1+&+ [ x*x : x in Eltseq(XX[i])]) - 2*Log(scale): i in [1..Nrows(XX)]];
*/
  TT := Submatrix(TT, 1, 1, r, l-#s);
  assert l-#s eq Ncols(TT);
  X, T := GramSchmidtReduce(XX, r);
  assert T*XX eq X;
/*
"reduced: ";
[Log(1+&+ [ x*x : x in Eltseq(X[i])]) - 2*Log(scale): i in [1..Nrows(X)]];
*/
  T := Submatrix(T, r+1, 1, #s, Ncols(T)-1);
  T := T*TT;
  sol := [s[j] + &+ [U|T[j][i] * KernelGens_no_S[i] 
                      : i in [1..#KernelGens_no_S]] 
                      : j in [1..#s]];
  X := Matrix(R, Matrix([mU(x) : x in sol]))*LogBaseMat;                    

  vprint NormEquation, 2: "reduce to", sol[1];
  return sol;
end function;


intrinsic InternalSUnitLowLevel(SU::Map, S::[RngOrdIdl], 
          Val::UserProgram  // Val(Func::UserProg) -> Mtrx 
                            // containing Func applied to the 
                            // elements.
                            // Func can be Valuation, Logs, ResidueClassField
                            // map (any log-like function)
            :Base := false, Check := false) -> Mtrx
  {For internal use}
  /* given the map returned by SUnitGroup (and the multiplicative base
   * as returned as the 3rd return value with raw),
   * Convert Nrm into an endomorphism of the domain of SU
   */
  /* most likely it should be done for e sequence of Maps (Act) together...
   * we shall see!
   */

  G := Domain(SU);
  if ISA(Type(Codomain(SU)), FldAlg) then
    Base := [SU(G.i) : i in [1..Ngens(G)]];
    R := RSpace(Integers(), Ngens(G));
    SU := hom<G -> RSpace(Integers(), R)| [R.i : i in [1..Ngens(G)]]>;
  else  
    R := Codomain(SU);
    if ISA(Type(Base), Mtrx) then
      Base := Eltseq(Base);
    end if;
  end if;
  K := Universe(Base);
  MK := MaximalOrder(K);

  // This will be done in a 3 step method
  // 1: decompose the S-Unit part, ie. find elements in G that have the
  //    correct valuation at all places in S. 
  // 2: decompose the Unit part by finding elements in G that have
  //    correct logarithms
  // 3: decompose the torsion part.   
  

  // is the same as in the Val call below!
  vals := Matrix(Integers(), #Base, #S, 
    [ [ Integers()| Valuation(x, p) : p in S] : x in Base]);

  r1, r2 := Signature(K);
  r := r1 + r2 -1;

  M := Matrix(Integers(), Ngens(G)-r-1, Ncols(SU(G.0)), 
    [SU(G.i) : i in [r+2..Ngens(G)]]);

  // now find y in R such that ex -SU-> K -Act->K
  //          equals           y          -SU-> K
  // this means &* [ Base[i]^y[i] : i] eq [ BaseImg[i]^ex[i] : i]
  // this implies: y* vals eq ex * valsImg
  
  f, Y := IsConsistent(M*vals, Val(func<a | [Integers()|Valuation(a, p) : p in S]>));
  if not f then
    error "Error: map does not act on the S-units";
  end if;

  // END OF STEP 1!!!
  //
  // now y is "almost" correct, ie. the finite valuations are OK, but
  // the element may (will) be off by a unit.
  // The 1st r1+r2 - 1 generators of G will in fact be units!
  // (which is why this loop does not cover them)

  // now we have to find the images of
  //   - the 1st r generators
  //   - the error term of the last few
  // and this is going to involve real arithmetic.  
  // we have to do both:
  // find the images of the units and
  // correct the errors we made for the true S-units
  // (we still makeing an error by ignomring the torsion units)
  pr := 167;
  extra := 1;
  old_pr := 0;
  old_R := GetDefaultRealField();
  old_kpr := GetKantPrecision();
  p := 1;

  RegLbound := 0.2/2^r2;

  
  repeat
    no_i := 1;
    TT := [];
    if r ge 1 then
      mu_exp := 1;
      repeat
        if pr ne old_pr then
          old_pr := pr;
          SetKantPrecision(K, pr);
          SetDefaultRealField(RealField(pr));
          RegLbound := ChangePrecision(RegLbound, pr);

          vals := Matrix([ Logs(K!x)[1..r] : x in Base]);

          UnitMatrix := [];
          for i in [2..r+1] do
            ex := SU(G.i);
            unit := Matrix(CoefficientRing(vals), ex)*vals;
            Append(~UnitMatrix, unit);
          end for;
          if r ne 0 then
            UnitMatrix := Matrix(UnitMatrix);
          else
            UnitMatrix := Matrix(RealField(pr), 0, 0, []);
          end if;
          Val_mat := Val(func<a | Logs(K!a)[1..r]>);
          assert Precision(CoefficientRing(Val_mat)) ge pr;
        end if;

        ImageMatrix := Matrix(Val_mat[no_i]) - 
                Matrix(CoefficientRing(vals), Matrix(Y[no_i] *M)) * vals;
        // "ImageMatrix[1][1]: ", ImageMatrix[1][1], " of precosopm ", Precision(ImageMatrix[1][1]);         

        R := VerticalJoin(UnitMatrix, ImageMatrix);
        B := R*Transpose(R);
        c := PseudoCholeskyForm(B:Swap, Error := false);
        if c cmpeq false then
          pr +:= 50;
          vprint NormEquation, 3: "Fail1: prec now", pr;
          continue;
        end if;
        if &* [RealField()|c[i][i] : i in [1..Nrows(c)-1]] lt RegLbound^2 then
          pr +:= 50;
          vprint NormEquation, 3: "Fail2: prec now", pr;
          continue;
        end if;
        if Ilog2(&* [RealField()|c[i][i] : i in [1..Nrows(c)-1]]/RegLbound^2)/3 gt pr then
          pr +:= 50;
          vprint NormEquation, 3: "Fail3: prec now", pr;
          continue;
        end if;

        mu := CF_mu(R, r1+2*r2:Real := false, Chol := c)^mu_exp;
        mu_pr := CF_prec(B, mu);
        // "using mu_pr ", mu_pr;
        if mu_pr gt pr then
          pr +:= Maximum(mu_pr - pr+20, 50);
          vprint NormEquation, 3: "Fail4: prec now", pr;
          continue;
        end if;

        muB := Matrix(Nrows(B), Ncols(B), 
                       [ Round(mu*mu*x) : x in Eltseq(B)])
               + Ceiling(Nrows(B)/2)*IdentityMatrix(Integers(), Nrows(B));

        LL, T, rr := LLLGram(muB:Sort := false, Check);
//        "LLL called, result is ", LL;

        mp, p := Minimum([LL[x][x] : x in [1..Nrows(LL)]]);
        if (p ne 1 and p ne Nrows(LL)) or mp lt 0 or Log(mu)/Log(mp+1) lt 2 then
          pr +:= 50;
          mu_exp +:= 1;
          vprintf NormEquation, 3: "Fail5: prec now %o p:%o LL(%o, %o), Log:%o\n", pr, p, Nrows(LL), Ncols(LL), mp lt 0 select false else Log(mu)/Log(mp+1);
          continue;
        end if;
        assert p eq 1 or p eq Nrows(LL);

        if p eq Nrows(LL) then
          rel := T[Nrows(T)];
          assert IsUnit(rel[Nrows(T)]); 
          rel := Matrix(rel);
          rel :=  Submatrix(rel, 1, 1, 1, Nrows(T)-1)*rel[1][Nrows(T)];
        else
          rel := T[1];
          assert IsUnit(rel[Nrows(T)]); 
          rel := Matrix(rel);
          rel :=  Submatrix(rel, 1, 1, 1, Nrows(T)-1)*rel[1][Nrows(T)];
        end if;

        Append(~TT, rel);
        no_i +:=1;
      until no_i gt Nrows(Y);
    else 
      TT := Matrix(Integers(), Nrows(Y), 0, []);
    end if;

    // now we can do  new "Y" which is the map up to torsion
    //       
    // we have
    //
    // TT*UnitMatrix + ImageMatrix = 0
    //                                  
    //             
    // so essentially: ImageMatrix = -TT*UnitMatrix
    I := -Matrix(TT);
    // I is the 
    //   action on the units
    //   the correction for the S-units
    // so we have to combine I and Y (which is the action of the S-units ONLY)
    // (both ignore the torsion)
    Y := HorizontalJoin(I, Y);

    // END OF STEP 2
    //
    // now the final step: Y is the correct transformation - up to 
    // torsion units.
    // The torsion part can (and will) be evaluated in a finite field
    // having large enought torsion:
    n := Order(G.1); // the torsion part!
    M := MaximalOrder(K);
    if p eq 1 then // can fail if the precision needed incrementing
                   // ie if the repeat .. until f loop is executed again
      p := NextPrime(1000);
      repeat
        while p mod n ne 1 do
          p := NextPrime(p);
        end while;
        if Gcd(Discriminant(MK), p) ne 1 then 
          p := NextPrime(p);
          continue;
        end if;
        ld := DecompositionType(MK, p);
        i := Position([x[1] : x in ld], 1);
        if i eq 0 then
          p := NextPrime(p);
          continue;
        end if;
        P := Decomposition(MK, p)[i][1];
        F, mF := ResidueClassField(P);
        if true in {(Integers()!Denominator(x)) mod p eq 0 : x in Base } then
          p := NextPrime(p);
          continue;
        end if;
        if true in { Numerator(x) in P : x in Base } then
          p := NextPrime(p);
          continue;
        end if;
        break;
      until false;
    end if;

    vals := Matrix([[ Log(mF(x))] : x in Base]);
    valsImg := Val(func<a|[Log(mF(a))]>);

    ImageMatrix := [];
    for i in [1..1] do
      ex := SU(G.i);
      unit := Matrix(ex)*vals;
      Append(~ImageMatrix, unit);
    end for;
    M := Matrix([Codomain(SU)|SU(G.i) : i in [2..Ngens(G)]]);

    
    unit := valsImg -
            Matrix(CoefficientRing(vals), Y *M) * vals;
    ImageMatrix := VerticalJoin(Matrix(ImageMatrix), unit);        

    Zn := Integers(#F-1);
    Z := Integers();


    ImageMatrix := Matrix(Zn, ImageMatrix);
    ImageMatrix := Eltseq(ImageMatrix);
    ImageMatrix := [ Solution(ImageMatrix[1], ImageMatrix[i]) : i in [2..#ImageMatrix]];
    ImageMatrix := Matrix(Z, #ImageMatrix, 1, ImageMatrix);

    Y := HorizontalJoin(ImageMatrix, Y);

    if not Check then               
      // now it remains to convert Y back to a hom between G and G
      // I think this will mean some IsConsistent calls.
      // Probaly one should NOT compute Y inthe 1st place but only the action
      // on G
      break;
    end if;

    error "not implemented yet...";

    // here we need to check that certain (large) power products are
    // equal to 1.
    // I currently don't feel like it...
      
  until f;

  SetKantPrecision(old_kpr);
  SetDefaultRealField(old_R);

  return Y;               
end intrinsic;    

intrinsic SUnitDiscLog(SU::Map, RHS::FldAlgElt, S::[RngOrdIdl]:Base := false) -> GrpAbElt
  {For the S-unit group represented by the map into the field and the sequence of ideals, and some element in the field, write is as an element in the abstract group.}
  /* 
   * decomposes RHS (hopefully)
   * 
   */

  G := Domain(SU);
  if ISA(Type(Codomain(SU)), FldAlg) then
    Base := [SU(G.i) : i in [1..Ngens(G)]];
    R := RSpace(Integers(), Ngens(G));
    SU := hom<G -> RSpace(Integers(), R)| [R.i : i in [1..Ngens(G)]]>;
  else  
    R := Codomain(SU);
    if ISA(Type(Base), Mtrx) then
      Base := Eltseq(Base);
    end if;
  end if;
  K := Universe(Base);
  MK := MaximalOrder(K);

  function Val(Func)
    f := Func(RHS);
    if Type(f) eq SeqEnum then
      if #f eq 0 then
        R := Integers();
      else
        R := Universe(f);
      end if;
    elif ISA(Type(f), Mtrx) then
      R := CoefficientRing(f);
    end if;
    return Matrix(R, [Func(RHS)]);
  end function;
  
  M :=  InternalSUnitLowLevel(SU, S, Val:Base := Base);
  return G!Eltseq(M);
end intrinsic;


intrinsic SUnitDiscLog(SU::Map, RHS::[FldAlgElt], S::[RngOrdIdl]:Base := false) -> []
  {For the S-unit group represented by the map from the abstract group into the field, and a sequence of elements in the field, write them as elements in the abstract group.}
  /* 
   * decomposes RHS (hopefully)
   * 
   */

  G := Domain(SU);
  if ISA(Type(Codomain(SU)), FldAlg) then
    Base := [SU(G.i) : i in [1..Ngens(G)]];
    R := RSpace(Integers(), Ngens(G));
    SU := map<G -> R| x:->R!Eltseq(x)>;
  else  
    R := Codomain(SU);
    if ISA(Type(Base), Mtrx) then
      Base := Eltseq(Base);
    end if;
  end if;
  K := Universe(Base);
  MK := MaximalOrder(K);

  function Val(Func)
    return Matrix([Func(x) : x in RHS]);
  end function;
  
  M :=  InternalSUnitLowLevel(SU, S, Val:Base := Base);
  return [G!Eltseq(M[i]) : i in [1..#RHS]];
end intrinsic;

 
function check_action_on_ideals(map, S) 
  O := Ring(Universe(S));
  mi := func<X | ideal<O|[map(x) : x in Generators(X)]>>;
  S := {x : x in S};
  return forall{x : x in S | Support(mi(x)) subset S};
end function;

intrinsic SUnitAction(SU::Map, Act::Map, S::[RngOrdIdl]:Base := false, CheckAction) -> Map
  {For the S-unit group represented by the map from the abstract group into the field, compute the action on the group induced by the field map provided.}
  /* given the map returned by SUnitGroup (and the multiplicative base
   * as returned as the 3rd return value with raw),
   * Convert Nrm into an endomorphism of the domain of SU
   */

  require not CheckAction or check_action_on_ideals(Act, S) :
    "The map does not act on the ideals provided";

  G := Domain(SU);
  if ISA(Type(Codomain(SU)), FldAlg) then
    Base := [SU(G.i) : i in [1..Ngens(G)]];
    R := RSpace(Integers(), Ngens(G));
    SU := map<G -> RSpace(Integers(), Ngens(G))| x :-> Eltseq(x)>;
  else  
    R := Codomain(SU);
    if ISA(Type(Base), Mtrx) then
      Base := Eltseq(Base);
    end if;
  end if;
  K := Universe(Base);
  MK := MaximalOrder(K);

  // May 2013, SRD 
  DA := Domain(Act);
  if forall{x : x in Base | x in DA} then
    act := Act;
  else
    act := map< K -> K | x :-> Act(Numerator(x)) / Act(Denominator(x)) >; 
  end if;

  BaseImg := [ act(x) : x in Base];
  ChangeUniverse(~BaseImg, Universe(Base)); // for the common case of Norm

  function Val(Func) 
    assert #BaseImg ne 0;
    f := Func(BaseImg[1]);
    if #f eq 0 then
      R := Integers();
    else
      R := Universe(f);
    end if;
    N := Matrix(R, #BaseImg, #f, [Func(x) : x in BaseImg]);
    M := Matrix(R, Matrix(Ngens(G), Ncols(SU(G.0)), [SU(G.i) : i in [1..Ngens(G)]]));
    return M*N;
  end function;

  M := InternalSUnitLowLevel(SU, S, Val:Base := Base);
  return hom<G ->G | [G!Eltseq(M[i]) : i in [1..Ngens(G)]]>;

end intrinsic;  

intrinsic SUnitAction(SU::Map, Act::[Map], S::[RngOrdIdl]:Base := false, CheckAction) -> Map
  {For the S-unit group represented by the map from the abstract group into the field, compute the actions on the group induced by the field maps provided.}
  /* given the map returned by SUnitGroup (and the multiplicative base
   * as returned as the 3rd return value with raw),
   * Convert Nrm into an endomorphism of the domain of SU
   */

  require not CheckAction or forall{x : x in Act | check_action_on_ideals(x, S)} :
    "One of the maps does not act on the ideals provided";
  G := Domain(SU);
  if ISA(Type(Codomain(SU)), FldAlg) then
    Base := [SU(G.i) : i in [1..Ngens(G)]];
    R := RSpace(Integers(), Ngens(G));
    SU := map<G -> RSpace(Integers(), Ngens(G))| x :-> Eltseq(x)>;
  else  
    R := Codomain(SU);
    if ISA(Type(Base), Mtrx) then
      Base := Eltseq(Base);
    end if;
  end if;
  K := Universe(Base);
  MK := MaximalOrder(K);

  // May 2013, SRD 
  act := [Universe(Act)| ];
  for i := 1 to #Act do
    A := Act[i];
    DA := Domain(A);
    if forall{x : x in Base | x in DA} then
      act[i] := A;
    else
      act[i] := map< K -> K | x :-> A(Numerator(x)) / A(Denominator(x)) >; 
    end if;
  end for;

  BaseImg := [ [A(x) : x in Base] : A in act];
  ChangeUniverse(~BaseImg, PowerSequence(Universe(Base))); // for the common case of Norm

  function Val(Func) 
    assert #BaseImg ne 0;
    f := Func(BaseImg[1][1]);
    if #f eq 0 then
      R := Integers();
    else
      R := Universe(f);
    end if;
    flag := true;
    for X in BaseImg do
      N := Matrix(R, #BaseImg[1], #f, [Func(x) : x in X]);
      M := Matrix(R, Matrix(Ngens(G), Ncols(SU(G.0)), [SU(G.i) : i in [1..Ngens(G)]]));
      y := M*N;
      if flag then
        flag := false;
        Y := y;
      else
        Y := VerticalJoin(Y, y);
      end if;
    end for;
    return Y;
  end function;

  M := InternalSUnitLowLevel(SU, S, Val:Base := Base);
  return [hom<G ->G | [G!Eltseq(M[i+j*n]) : i in [1..n]]> : j in [0..Nrows(M) div Ngens(G)-1]] 
                                                   where n := Ngens(G);

end intrinsic;  


declare attributes FldAlg : NeqOrder;


// When K is a quadratic extension of Q, better to solve the conic
function NEQ_using_conics_over_Q(K, m)
  m := Rationals()!m;
  C,B,A := Explode(Eltseq(DefiningPolynomial(K)));
  plane := ProjectiveSpace(Rationals(),2);
  conic := Conic(plane, A*plane.1^2 - B*plane.1*plane.2 + C*plane.2^2 - m*plane.3^2);
  bool, pt := HasRationalPoint(conic);
  if not bool then return false, _; end if;
  XX,YY,ZZ := Explode(Eltseq(pt));
  sol := (XX + K.1*YY)/ZZ;
  assert Norm(sol) eq m;
  return true, [sol];
end function;


function NEQ(K, m:Primes := 1, Nice:= 2, Raw := 3)
  if m eq 0 then
    if Raw then
      error "0 cannot be represented in raw";
    end if;
    return true, [K!0]; 
  end if;  
  if m eq 1 then
    if Raw cmpeq true then return true, [Vector([1])], Vector([K!1]);
    else return true, [K!1]; end if;
  end if;
  if m eq -1 and IsOdd(Degree(K)) then
    if Raw cmpeq true then return true, [Vector([1])], Vector([K!-1]);
    else return true, [K!-1]; end if;
  end if;

  if BaseField(K) cmpeq Rationals() and Degree(K) eq 2 then 
    has_sol, sols := NEQ_using_conics_over_Q(K, m);  
    if not has_sol and Raw cmpeq true then return false, _,_;
    elif not has_sol then return false, _;
    elif Raw cmpeq true then return true, [Vector([1])], Vector(sols);
    else return true, sols;
    end if;
  end if;

  f, m := IsCoercible(BaseField(K), m);
  if not f then
     error "Error: Rhs must be in the coefficient field of the large field.";
   end if;

  if assigned K`NeqOrder then
    M := K`NeqOrder;
  else
    vprintf NormEquation: "Creating maximal order in absolute field ... "; 
    vtime NormEquation:
    if not IsAbsoluteField(K) then
      // TO DO: more here ... eg use the minimal multiple of Kgens[1] that is integral
      F := BaseField(K);
      Kgens := GeneratorsSequence(K);
      if IsAbsoluteField(F) and #Kgens eq 1 and IsIntegral(Kgens[1]) then
        Kabs := AbsoluteField(K);
        Kpowerbasis := [1] cat [alpha^i : i in [1..Degree(K)-1]] where alpha is Kabs!Kgens[1];

        IndentPush();
        vprintf NormEquation: "\nCreating the obvious order in the absolute field ... "; 
        vtime NormEquation:
        O := Order([Kabs| (Kabs!b) * a : b in Basis(MaximalOrder(F)), a in Kpowerbasis] 
                   : Order:=true, Verify:=false);

        vprintf NormEquation: "Computing MaximalOrder ... "; 
        vtime NormEquation:
        M := MaximalOrder(O);
        IndentPop();
      else
        M := MaximalOrder(AbsoluteField(K));
      end if;
    else
      M := MaximalOrder(K);
    end if;
    K`NeqOrder := M;
  end if;
  Nrm := map<M -> M | x :-> M!Norm(K!x)>;
  if Raw then
    f, s, b := NormEquation(m, Nrm:Primes := Primes, Nice := Nice, Raw := Raw);
  else
    f, s := NormEquation(m, Nrm:Primes := Primes, Nice := Nice, Raw := Raw);
  end if;
  if f then
    if Raw then
      ChangeUniverse(~b, K);
      return f, s, b;
    else
      ChangeUniverse(~s, K);
      return f, s;
    end if;
  else
    return f, _, _;
  end if;
end function;

intrinsic NormEquation(rhs::RngElt, Nrm::Map: Raw := false, Nice := true, Primes := [], ReturnAction := false ) -> BoolElt, RngElt
  {Tries to find a preimage for rhs under the given map.}
 
  if IsZero(rhs) then
    return true, Domain(Nrm)!0;
  end if;
  /*
   * Tries to solve Nrm(x) = rhs  where Nrm is a multiplicative
   * function from some field K into itself.
   * I assume that taking enough primes to generate the class group 
   * of K covers all possible denominators
   *
   * This is true if the field is relative normal!!!
   * (and NOT checked!!!)
   */
   /* can be optimized (a little bit) further...  */

  K := Domain(Nrm);
  if ISA(Type(K), FldAlg) and assigned K`NeqOrder then
    M := K`NeqOrder;
  else
    if ISA(Type(K), RngOrd) then
      M := K;
      K := FieldOfFractions(M);
      if assigned K`NeqOrder then
        M := K`NeqOrder;
      end if;
    else
      M := MaximalOrder(K);
    end if;
  end if;
  K`NeqOrder := M;

  vprintf NormEquation: "Getting class group ... "; 
  vtime NormEquation:
  C, mC := ClassGroup(M : Proof := "GRH");
  // If we find a solution, it is rigorous (obviously)
  // regardless whether class group was even correct.
  // If no solution, in principle we should prove this
  // by getting rigorous S-units (TO DO)
  // Sep 2012, SRD

  S := [ x[1] : x in Factorization(M*M!Numerator(K!rhs) *Denominator(K!rhs))];
  if Primes cmpne [] then
    S := S cat Primes;
  else
    c := sub<C|[x @@ mC : x in S]>;
    if c ne C then
      p := 1;
      repeat
        p := NextPrime(p);
        lp := Decomposition(M, p);
        for P in lp do
          if Norm(P[1]) lt 1000 or Degree(P[1]) eq 1 and not P[1] in S then
            d := P[1]@@mC;
            if not d in c then
              Include(~S, P[1]);
              c := sub<C|c,d>;
              if c eq C then
                break;
              end if;
            end if;
          end if;
        end for;
      until c eq C;
    end if;
  end if;
  S := &join [{ x[1] : x in Decomposition(M, Minimum(y))} : y in S];
  S := [PowerIdeal(M)| x : x in S];


  vprintf NormEquation: "Getting S-unit group ... "; 
  vtime NormEquation:
  U, mU, Base := SUnitGroup(S:Raw);
  NoSU := SUnitAction(mU, Nrm, S:Base := Base);

  vprintf NormEquation: "Solving discrete log problem in S-unit group ... "; 
  vtime NormEquation:
  Rhs := SUnitDiscLog(mU, K!rhs, S:Base := Base);


  if Rhs in Image(NoSU) then
    sol := Rhs @@ NoSU;
    if Nice then
      vprintf NormEquation: "Trying to make the solution nicer ... ";
      vprintf NormEquation, 2: "\n";
      vtime NormEquation:
      sol := NiceSolution(Kernel(NoSU), sol, mU, Base, S);
    else
      sol := [sol];
    end if;
    if Raw then
      if ReturnAction then
        return true, sol, Base, <U, mU, NoSU, S>;
      else
        return true, [mU(x) : x in sol], Base;
      end if;
    else
      return true, [PowerProduct(Base, mU(x)) : x in sol], _;
    end if;
  else
    if Raw then
      return false, _, _;
    else
      return false, _, _;
    end if;
  end if;
end intrinsic;

intrinsic NormEquation(O::RngOrd, m::RngIntElt:All := true, Solutions := -1, Exact := true, Ineq := false) -> BoolElt, SeqEnum
  {Solves the absolute norm equation in the order provided.}

  NEQ := InternalNormEquation;

  if Solutions eq -1 then
    return NEQ(O, m: All := All, Exact := Exact,
                                      Ineq := Ineq);
  else
    return NEQ(O, m: All := All, Solutions := Solutions,
                                      Exact := Exact,
                                      Ineq := Ineq);
  end if;
end intrinsic;

intrinsic ChangeUniverse(~x::ModTupRngElt, R::Rng)
  {Replaces x by the same vector, but with new base ring R}
  x := RSpace(R, Dimension(Parent(x)))!Eltseq(x);
end intrinsic;

intrinsic NormEquation(O::RngOrd, m::RngOrdElt:All := true, Solutions := -1, Exact := true, Ineq := false) -> BoolElt, SeqEnum
  {Solves the relative norm equation in the order provided.}

  NEQ := InternalNormEquation;

  if Solutions eq -1 then
    return NEQ(O, m: All := All, Exact := Exact,
                                      Ineq := Ineq);
  else
    return NEQ(O, m: All := All, Solutions := Solutions,
                                      Exact := Exact,
                                      Ineq := Ineq);
  end if;
end intrinsic;

intrinsic NormEquation(K::FldAlg, m::FldAlgElt: Primes := [], Nice := true, Raw := false ) -> BoolElt, SeqEnum
  {Solves the relative norm equation in the field provided.}

  return NEQ(K, m: Nice := Nice, Raw := Raw, Primes := Primes);
end intrinsic;

intrinsic NormEquation(K::FldAlg, m::RngIntElt:Nice := true, Primes := [], Raw := false ) -> BoolElt, SeqEnum
  {Return whether an element x of O exists such that Norm(x) eq m and, if so, a sequence of such solutions x.}

  return NEQ(K, m: Nice := Nice, Primes := Primes, Raw := Raw);

end intrinsic;

intrinsic NormEquation(K::FldAlg, m::FldRatElt:Nice := true, Primes := [], Raw := false ) -> BoolElt, SeqEnum
  {Return whether an element x of K exists such that Norm(x) eq m and, if so, a sequence of such solutions x.}

  return NEQ(K, m: Nice := Nice, Primes := Primes, Raw := Raw);

end intrinsic;

intrinsic IntegralNormEquation(a::RngElt, Nrm::Map, O::RngOrd:Nice := true) -> BoolElt, []
  {Solves Nrm(x) eq a with x in some order O}

  vprint NormEquation, 1: "IntegralNormEquation: first solving in the field";  
  has, s, base, A := NormEquation(a, Nrm:Raw, ReturnAction);
  if not has then
    vprint NormEquation, 1: "No solutions in the field";
    return false, _;
  end if;
  vprint NormEquation, 1: "Found", s;

  US := A[1];
  mUS := A[2];   // careful: mU: U -> Z^n, exponents for base!
  NoSU := A[3]; // Nrm as a map: U -> U
  S := A[4];    // the primes used...


  K := NumberField(O);
  U := sub<US|[US.i : i in [1..1+UnitRank(K)]]>;
 
  vprint NormEquation, 1: "Computing unit group of the suborder";
  UO, mUO := UnitGroupAsSubgroup(O:UG := <U, map<U -> K | x:-> PowerProduct(base, mUS(x))>>);
  vprint NormEquation, 2: "Index of unit group is", #quo<U|UO>;
  sU := s[1];

  // due to lack of theory, I currently cannot handle non-unit solutions.
  // (Well, UnitsAsSubgroup for S-Units is lacking (in theory and
  // implementation)
  assert sU in U;
  if sU in UO then
    vprint NormEquation, 2: "Solution is already in the suborder";
    return true, [PowerProduct(base, mUS(s[1]))];
  end if;

  N1 := Kernel(NoSU); // we need n in N1, s.th. sU+n in UO...
  if not sU in sub<US|N1, UO> then
    vprint NormEquation, 2: "Solution cannot be translated into the suborder";
    return false, _;
  end if;
  D, inc, proj := DirectProduct([N1, UO]);
  m := hom<D -> US | [D.i@proj[1] + D.i@proj[2] : i in [1..Ngens(D)]]>;
  assert sU in Image(m);
  p := sU@@m;
  p1 := p@proj[1];
  
  // now sU-p1 SHOULD be a solution in O...

  vprint NormEquation, 2: "Found solution", sU-p1;
  if Nice then
    s := NiceSolution(N1 meet UO, sU-p1, mUS, base, S)[1];
  else
    s := sU-p1;
    assert s in UO;
  end if;
  vprint NormEquation, 2: "evaluating power product...";
  vtime NormEquation, 2: x := [PowerProduct(base, mUS(s))];
  vprint NormEquation, 2: "... done, returning", x;
  return true, x;
end intrinsic;

