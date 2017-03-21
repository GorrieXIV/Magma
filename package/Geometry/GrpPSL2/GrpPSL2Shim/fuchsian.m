freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Arithmetic Fuchsian groups
// May 2006, June 2007, John Voight
//
//////////////////////////////////////////////////////////////////////////////

declare attributes GrpPSL2: ShimVolume, ShimEllipticInvariants, ShimLevel,
                            ShimFDDisc, ShimFDGens, ShimGroup, ShimGroupMap,
                            ShimFDSidepairs, IsShimuraGroup,
                            ShimData;
declare attributes AlgAssVOrd: IsEichler, FuchsianGroup;
declare attributes AlgQuat: SplitRealPlace, MatrixRepresentation;

import "domain.m" : AssignPrecision;

//-------------
//
// Embed the unit group of a quaternion algebra as a Fuchsian group
//
//-------------

intrinsic SplitRealPlace(A::AlgQuat) -> PlcNumElt
  {Returns the unique real place at which A is split, if it exists.}

  if assigned A`SplitRealPlace then
    return A`SplitRealPlace;
  end if;

  Foo := RealPlaces(BaseField(A));
  // Find the unique real place where A is unramified.
  a,b := StandardForm(A);

  v := [v : v in Foo | Evaluate(a,v) gt 0 or Evaluate(b,v) gt 0];
  require #v eq 1 : "The algebra must have only one split real place";

  A`SplitRealPlace := v[1];
  return v[1];
end intrinsic;

intrinsic FuchsianMatrixRepresentation(A::AlgQuat : Precision := 0) -> Map
  {Returns a map A -> M_2(R) when A has a unique split place.}

  v := SplitRealPlace(A);

  if assigned A`MatrixRepresentation and Precision eq 0 then
    return A`MatrixRepresentation;
  end if;
  if Precision eq 0 then
    if not assigned A`prec then AssignPrecision(A); end if;
    prec := A`prec;
  else
    prec := Precision;
  end if;

  RR := RealField(prec);
  M2RR := MatrixRing(RR, 2);

  a,b := StandardForm(A);

  F := BaseField(A);
  if Type(F) eq FldOrd then
    F := NumberField(F);
  end if;
  if Type(F) in {FldNum,FldQuad} then
    av := Evaluate(F!a,v : Precision := prec);
    bv := Evaluate(F!b,v : Precision := prec);
  else // FldRat
    av := RR!a;
    bv := RR!b; 
  end if;

  if bv gt 0 then
    Alpha := M2RR![0,SquareRoot(Abs(av)),
                  Sign(av)*SquareRoot(Abs(av)),0];
    Beta := M2RR![SquareRoot(bv),0,0,-SquareRoot(bv)];
  else
    Alpha := M2RR![SquareRoot(av),0,0,-SquareRoot(av)];
    Beta := M2RR![0,SquareRoot(Abs(bv)),
                 Sign(bv)*SquareRoot(Abs(bv)),0];
  end if;

  if Type(F) in {FldNum,FldQuad} then
    h := hom<A -> M2RR | gamma :-> 
                          Evaluate(F!gamma[1],v : Precision := prec) + 
                          Evaluate(F!gamma[2],v : Precision := prec)*Alpha +
                          Evaluate(F!gamma[3],v : Precision := prec)*Beta + 
                          Evaluate(F!gamma[4],v : Precision := prec)*Alpha*Beta>;
  else // FldRat
    h := hom<A -> M2RR | gamma :-> gamma[1] + gamma[2]*Alpha +
                                   gamma[3]*Beta + gamma[4]*Alpha*Beta>;    
  end if;
  if Precision eq 0 then
    A`MatrixRepresentation := h;
  end if;
  return h;
end intrinsic;

intrinsic FuchsianGroup(F::FldNum, D::RngOrdIdl, N::RngOrdIdl : 
      TotallyPositive := true, ComputeAlgebra := true) -> GrpPSL2
  {Returns the group of totally positive units of O 
   modulo base units as a Fuchsian group,
   where O is an Eichler order of level N in a quaternion algebra
   of discriminant D over F.  If ComputeAlgebra := false, then 
   a representative algebra is not computed, so the object returned
   is just an empty hull, and only invariants can be computed.}

  if not ComputeAlgebra then
    G := HackobjCreateRaw(GrpPSL2);
    G`ShimData := <F, D, N>;
    G`BaseRing := F;
    G`IsShimuraGroup := true;
    G`ShimTotallyPositiveFlag := TotallyPositive;
    return G;
  else
    require IsTotallyReal(F) : "F must be totally real";
    A := QuaternionAlgebra(D, RealPlaces(F)[1..Degree(F)-1]);
    return FuchsianGroup(Order(MaximalOrder(A), N));
  end if;
end intrinsic;

intrinsic FuchsianGroup(F::FldRat, D::RngIntElt, N::RngIntElt :
      ComputeAlgebra := true) -> GrpPSL2
  {Returns the group O_1^* of units of norm 1 as a Fuchsian group 
   where O is an Eichler order of level N in a quaternion algebra
   of discriminant D over F.  If ComputeAlgebra := false, then 
   a representative algebra is not computed, so the object returned
   is just an empty hull, and only invariants can be computed.}

  if not ComputeAlgebra then
    G := HackobjCreateRaw(GrpPSL2);
    G`ShimData := <F, D, N>;
    G`BaseRing := F;
    G`IsShimuraGroup := true;
    G`ShimTotallyPositiveFlag := false;
    return G;
  else
    return FuchsianGroup(QuaternionOrder(D, N));
  end if;
end intrinsic;

IsEichlerInternal := function(O, Omax, N);
  Z_F:= BaseRing(O);
  if Type(O) eq AlgQuatOrd then
    Obasis := [<1, g> : g in Basis(O)];
  else
    Obasis := PseudoBasis(O);
  end if;
  nus := [];

  for pp in Factorization(N) do
    M2Fp, phi, mFp := pMatrixRing(Omax, pp[1]);
    Fp := BaseRing(M2Fp);
    pi := UniformizingElement(Fp);
    Opbasis := [pi^Valuation(Obasis[i][1], pp[1])*phi(Obasis[i][2]) : i in [1..4]];

    // There exists a matrix conjugating a matrix to one which is upper
    // triangular modulo pp^e if and only if there exists (x:z) in PP^1 such that
    //   c*x^2 + (d-a)*x*z - b*z^2 = 0 (mod pp^e)
    // where the matrix is [[a,b],[c,d]].  Three simultaneous congruences
    // can therefore be solved by considering the 2-uple embedding and then
    // checking if the answer lies in the variety.

    // Implementation note (SRD, October 2010) 
    // The calculations here need to be done exactly in Z_F / pp^ee
    // The safest model of the quotient ring is quo< Z_F | pp^ee > 
    // (rather than some p-adic ring). 
    // Magma supports linear algebra in quo's.
    // However, it does not support IsSquare for any of the possible models
    // (for p-adics it is allowed but fails when ee is too small).
    // Fortunately we don't need IsSquare here.  
    // Instead to solve [t1, t2, t3] = [X^2 : X*Z : Z^2] we check that
    // t is normalized, and if (say) t1 = 1 we take [X:Z] = [1:t2]

    M := [[Opbasis[j][2,1], (Opbasis[j][2,2]-Opbasis[j][1,1]),
                  -Opbasis[j][1,2]] : j in [2..4]];

    if BaseRing(O) cmpeq Integers() then
      ZFpfixed, mFpfixed := quo< Integers() | pp[1]^pp[2] >;
    else
      ZFpfixed, mFpfixed := quo< Z_F | pp[1]^pp[2] >;
    end if;

    // define a "valuation" in the quotient ring
    valuation := func<x| Valuation(x @@ mFpfixed, pp[1]) >;

    M := Matrix([[mFpfixed(x@@mFp) : x in m] : m in M]);
    kerM := Kernel(Transpose(M));
    dim := Dimension(kerM);
    candidates := [];
    // sol = solution may exist 
    for j := 1 to dim do
      t := Eltseq(kerM.j);
      sol := valuation(t[1]) eq 0 or valuation(t[3]) eq 0;
      if sol then
        Append(~candidates, j);
        if t[1] eq 1 then
          sol := t[2]^2 eq t[3];
          if sol then
            // solution [X:Z] = [1:t[2]]
            Z := t[2] @@ mFpfixed @ mFp;
            nu := M2Fp! [Fp| 1, 0, Z, 1];
          end if;
        elif t[3] eq 1 then
          sol := t[2]^2 eq t[1];
          if sol then
            // solution [X:Z] = [t[2]:1]
            X := t[2] @@ mFpfixed @ mFp;
            nu := M2Fp! [Fp| X, -1, 1, 0];
          end if;
        else
          error "In IsEicher: vector is not normalized as expected";
        end if;
      end if;
      if sol then 
        break j;
      end if;
    end for;
          
    if not sol then  
      error if #candidates gt 1,
           "In IsEichler: unexpected case which is not handled. \nPlease report this bug!";
           // we have not check all combinations of candidates, so cannot return false 
      O`IsEichler := [* false *];
      return false, [];
    else
      nu := nu@@phi;
      Append(~nus, nu);
    end if;
  end for; // pp

  if #nus eq 0 then
    nus := [O!1];
  end if;

  O`IsEichler := [* true, nus *];
  return true, nus;
end function;

// TO DO: Ought to replace the intrinsic IsEichler(O) which just disappeared

intrinsic IsEichler(O::AlgQuatOrd, Omax::AlgQuatOrd) -> BoolElt
  {Returns true if and only if the quaternion order O is an Eichler order in Omax.} 

  if assigned O`IsEichler then
    if #O`IsEichler eq 2 then
      return O`IsEichler[1], O`IsEichler[2];
    else
      return O`IsEichler[1];
    end if;
  end if;

  B := Algebra(O);
  D := Discriminant(B);
  N := Discriminant(O) div D;
  if Gcd(N,D) ne 1 then
    O`IsEichler := [* false *];
    return false;
  end if; 

  bl, nus := IsEichlerInternal(O, Omax, N);
  return bl, nus;
end intrinsic;

intrinsic IsEichler(O::AlgAssVOrd, Omax::AlgAssVOrd) -> BoolElt
  {Returns true if and only if the quaternion order O is an Eichler order in Omax.} 

  if assigned O`IsEichler then
    if #O`IsEichler eq 2 then
      return O`IsEichler[1], O`IsEichler[2];
    else
      return O`IsEichler[1];
    end if;
  end if;

  B := Algebra(O);
  D := Discriminant(B);
  Z_F := BaseRing(O);
  N := Discriminant(O)/D;
  if N + D ne ideal<Z_F | 1> then
    O`IsEichler := [* false *];
    return false;
  end if; 

  bl, nus := IsEichlerInternal(O, Omax, N);
  return bl, nus;
end intrinsic;

intrinsic FuchsianGroup(O::AlgQuatOrd : VerifyEichler := true) -> GrpPSL2
  {Returns the group of units of reduced norm 1 as a Fuchsian group.
   Currently requires that O is an Eichler order.  By default,
   this is verified; to skip, set VerifyEichler := false.}

  if assigned O`FuchsianGroup then return O`FuchsianGroup; end if;

  G := HackobjCreateRaw(GrpPSL2);
  G`BaseRing := O;

  A := Algebra(O);
  require IsIndefinite(A) : "O must be an indefinite quaternion order";

  if VerifyEichler then
    require IsEichler(O, MaximalOrder(O)) : "O must be an Eichler order relative to the maximal order";
  end if;

  G`MatrixRepresentation := FuchsianMatrixRepresentation(A);
  G`MatrixGroup := Codomain(G`MatrixRepresentation);

  N := Discriminant(O)/Discriminant(Algebra(O));
  G`ShimLevel := Integers()!N;
  G`IsShimuraGroup := true;
  G`ShimTotallyPositiveFlag := false;

  O`FuchsianGroup := G;
  return G; 
end intrinsic;

intrinsic FuchsianGroup(O::AlgAssVOrd : VerifyEichler := true, TotallyPositive := true) -> GrpPSL2
  {Returns the group of totally positive units modulo base units as a Fuchsian group.
   Currently requires that O is an Eichler order.  By default,
   this is verified; to skip, set VerifyEichler := false.
   For the group of units of reduced norm 1, set TotallyPositive := 
   false.}

  if assigned O`FuchsianGroup and O`FuchsianGroup`ShimTotallyPositiveFlag eq TotallyPositive then 
    return O`FuchsianGroup; 
  end if;

  G := HackobjCreateRaw(GrpPSL2);
  G`BaseRing := O;

  A := Algebra(O);
  _, ramoo := RamifiedPlaces(A);
  require #ramoo eq Degree(BaseField(A)) - 1 : 
    "Quaternion algebra must have exactly one split real place.";

  if VerifyEichler then
    require IsEichler(O, MaximalOrder(O)) : "O must be an Eichler order relative to the maximal order";
  end if;

  G`MatrixRepresentation := FuchsianMatrixRepresentation(A);
  G`MatrixGroup := Codomain(G`MatrixRepresentation);

  N := Discriminant(O)/Discriminant(A);
  G`ShimLevel := N;
  G`IsShimuraGroup := true;
  G`ShimTotallyPositiveFlag := TotallyPositive;

  O`FuchsianGroup := G;
  return G;
end intrinsic;

intrinsic FuchsianGroup(A::AlgQuat : TotallyPositive := true) -> GrpPSL2
  {Returns the group of totally positive units modulo base units in a maximal order
   in A, as a Fuchsian group.}

  if BaseField(A) eq Rationals() then
    return FuchsianGroup(MaximalOrder(A));
  else
    return FuchsianGroup(MaximalOrder(A) : TotallyPositive := TotallyPositive);
  end if;
end intrinsic;

intrinsic Order(O::AlgAssVOrd, N::RngOrdIdl) -> AlgAssVOrd
  {Returns an order of level N inside the maximal quaternion order O.}

  require IsMaximal(O) : "O must be a maximal order";

  Z_F := BaseRing(O);
  require N+Discriminant(O) eq ideal<Z_F | 1> : 
    "N must be relatively prime to the discriminant of O";

  for pp in Factorization(N) do
    PO := PseudoBasis(O);
    M2Fp, phi, m := pMatrixRing(O, pp[1]);
    S := [MatrixUnit(M2Fp, i, j)@@phi : i,j in [1..2]]
         cat [PO[i][2] : i in [1..4]];
    I := [ideal<Z_F | 1>, ideal<Z_F | 1>, pp[1]^pp[2], ideal<Z_F | 1>]
         cat [pp[1]^pp[2]*PO[i][1] : i in [1..4]];
    O := Order(S, I);
  end for;

  O`IsEichler := [* true, O!1 *];
  return O;
end intrinsic;

intrinsic FuchsianGroup(A::AlgQuat, N::RngIntElt) -> GrpPSL2
  {Returns FuchsianGroup(QuaternionOrder(A, N)).}

  O := QuaternionOrder(A, N);
  return FuchsianGroup(O);
end intrinsic;

intrinsic FuchsianGroup(A::AlgQuat, N::RngOrdIdl : TotallyPositive := true) -> GrpPSL2
  {Returns the group of totally positive units modulo base units in an order of level N
   in A as a Fuchsian group.}

  O := MaximalOrder(A);
  ON := Order(O, N);
  return FuchsianGroup(ON : TotallyPositive := TotallyPositive);
end intrinsic;

intrinsic Quaternion(g::GrpPSL2Elt) -> AlgQuatElt
  {Returns the quaternion corresponding to the Fuchsian group element g.}

  G := Parent(g);
  require assigned G`IsShimuraGroup :
    "Argument must arise from an arithmetic Fuchsian group";
  return g`Element;
end intrinsic;
