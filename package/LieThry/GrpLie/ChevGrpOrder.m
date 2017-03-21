freeze;

/*=========================================================
  Don Taylor

  2 November 2010 

  $Id: ChevGrpOrder.m 48480 2014-09-28 02:09:52Z donnelly $

==========================================================
  Compute the orders of all finite Chevalley groups, in both
  full and factorised form.
  
  For the universal Chevalley group, the order is a polynomial in q.
  
  Versions
  --------
  There are three versions of Chevalley group covered by the
  code in this file:
  - Universal
  - Adjoint
  - Standard [Default]
  
  "Standard" refers to the group returned by ChevalleyGroup. It
  is the universal (matrix) group in all cases except for the
  orthogonal groups; i.e. types B, D and 2D.
  
  Type  Universal     "Standard"      Adjoint
  
  A_n   SL(n+1,q)      SL(n+1,q)      PSL(n+1,q)
  2A_n  SU(n+1,q)      SU(n+1,q)      PSU(n+1,q)
  B_n   Spin(2n+1,q)   Omega(2n+1,q)  POmega(2n+1,q)
  C_n   Sp(2n,q)       Sp(2n,q)       PSp(2n,q)
  D_n   Spin+(2n,q)    Omega+(2n,q)   POmega+(2n,q)
  2D_n  Spin-(2n,q)    Omega-(2n,q)   POmega-(2n,q)
  
  ATLAS conventions are used for the parameter q.  That is,
  we use 2A_n(q), not 2A_n(q^2), and similarly for 3D4 and 2E6.
  
==========================================================*/

// The basic degrees of a Chevalley group of Lie type tp and rank n
// The twisted types are included except for 3D4.

basicDegrees := function(tp,n)
  eps := [ 1 : i in [1..n]];
  mult := 1;
  case tp:
    when "A":
      deg := [2..n+1];
    when "2A":
      deg := [2..n+1];
      eps := [ (-1)^i : i in [2..n+1]];
    when "B","C":
      deg := [2..2*n by 2];
    when "2B":
      error if n ne 2, "rank must be 2";
      deg := [2,4]; 
      eps := [1,-1];
      mult := 2; // over Z[q^(1/2)]
    when "D":
      deg := [2..2*(n-1) by 2] cat [n];
    when "2D":
      deg := [2..2*(n-1) by 2] cat [n];
      eps[n] := -1;
    when "3D":
      error "not available for type 3D";
    when "E":
      if n eq 6 then  
        deg := [2,5,6,8,9,12];
      elif n eq 7 then
        deg := [2,6,8,10,12,14,18];
      elif n eq 8 then
        deg := [2,8,12,14,18,20,24,30];
      else
        error "rank must be 6, 7 or 8";
      end if;
    when "2E":
      if n eq 6 then  
        deg := [2,5,6,8,9,12];
        eps := [1,-1,1,1,-1,1];
      else
        error "rank must be 6";
      end if;
    when "F":
      if n eq 4 then
        deg := [2,6,8,12];
      else
        error "rank must be 4";
      end if;
    when "2F":
      if n eq 4 then
        deg := [2,6,8,12];
        eps := [1,-1,1,-1];
        mult := 2; // over Z[q^(1/2)]
      else
        error "rank must be 4";
      end if;
    when "G":
      if n eq 2 then
        deg := [2,6];
      else
        error "rank must be 2";
      end if;
    when "2G":
      if n eq 2 then
        deg := [2,6];
        eps := [1,-1];
        mult := 2; // over Z[q^(1/2)]
      else
        error "rank must be 2";
      end if;
    else
      error "unknown type " cat tp;
  end case;
  return deg, eps, mult;
end function;

intrinsic ChevalleyOrderPolynomial(tp :: MonStgElt, n :: RngIntElt) -> RngUPolElt
{The order of the universal Chevalley group of type tp and rank n
  as a polynomial in q}
  P := PolynomialRing(Integers()); q := P.1;
  if tp eq "3D" then
    require n eq 4: "rank must be 4";
    f := q^12*(q^2-1)*(q^6-1)*(q^8+q^4+1);
  else
    deg, eps, mult := basicDegrees(tp,n);
    N := (&+deg - n) div mult;
    if mult ne 1 then deg := [d div mult : d in deg]; end if;
    f := q^N;
    for i := 1 to #deg do f *:= q^deg[i] - eps[i]; end for;
  end if;
  return f;
end intrinsic;

ChevGrpCentre := function(tp, n, q)
// The order of the centre of the universal Chevalley group of 
// type tp and rank n over the field of q elements.  In the case
// of twisted groups, q is the order of the fixed field of the 
// Frobenius automorphism.
  z := 1;
  case tp:
    when "A":
      z := GCD(n+1,q-1);
    when "B","C":
      z := GCD(2,q-1);
    when "D":
      z := GCD(4,q^n-1);
    when "E":
      if   n eq 6 then z := GCD(3,q-1);
      elif n eq 7 then z := GCD(2,q-1);
      else z := 1; end if;
    when "2A":
      z := GCD(n+1,q+1);
    when "2D":
      z := GCD(4,q^n+1);
    when "2E":
      if n eq 6 then z := GCD(3,q+1); end if;
  end case;
  return z;
end function;

intrinsic FactoredChevalleyGroupOrder(tp :: MonStgElt, n :: RngIntElt,
    q :: RngIntElt : Proof := true, Version := "Default") -> RngIntEltFact
{The factored order of the Chevalley group of type tp and rank n
over the base field of q elements. The default is the order of the
group returned by ChevalleyGroup.}
  // First find the order of the universal group
  require IsPrimePower(q): "field order is not a prime power";
  if tp eq "3D" then
    require n eq 4: "rank must be 4";
    uord := &*[ Factorization(term : Proof := Proof) :
      term in [q^12,(q^2-1),(q^6-1),(q^8+q^4+1)]];
  else
    deg, eps, mult := basicDegrees(tp,n);
    N := (&+deg - n) div mult;
    if mult ne 1 then deg := [d div mult : d in deg]; end if;
    uord := Factorization(q^N : Proof := Proof);
    for i := 1 to #deg do
      uord *:= Factorization(q^deg[i] - eps[i] : Proof := Proof );
    end for;
  end if;
  return case< Version |
    "Adjoint" :
      uord / Factorization(ChevGrpCentre(tp,n,q) : Proof := Proof),
    "Default" :
      (tp in ["B","D","2D"] and IsOdd(q)) select uord / Factorization(2) else uord,
    default : uord >;
end intrinsic;

intrinsic FactoredChevalleyGroupOrder(tp :: MonStgElt, n :: RngIntElt,
    F :: FldFin : Proof := true, Version := "Default") -> RngIntEltFact
{The factored order of the Chevalley group of type tp and rank n
over the field F. The default is the order of the group returned by 
ChevalleyGroup.}
  q := #F;
  if tp in ["2A","2E"] then
    flag, q := IsSquare(q);
    require flag: "field order must be a square";
  elif tp eq "3D" then
    require n eq 4: "rank must be 4";
    flag, q := IsPower(q,3);
    require flag: "field order must be a cube";
  end if;
  return FactoredChevalleyGroupOrder(tp, n, q : Proof := Proof, Version := Version);
end intrinsic;

intrinsic ChevalleyGroupOrder(tp :: MonStgElt, n :: RngIntElt,
    q :: RngIntElt : Version := "Default") -> RngIntElt
{The order of the Chevalley group of type tp and rank n
over the base field of q elements. The default is the order of the
group returned by ChevalleyGroup.}
  // First find the order of the universal group
  flag, p, k := IsPrimePower(q);
  require flag: "field order is not a prime power";
  if tp eq "3D" then
    require n eq 4: "rank must be 4";
    uord := q^12*(q^2-1)*(q^6-1)*(q^8+q^4+1);
  else
    if tp in ["2B","2F"] then
      require p eq 2: "field must have characteristic 2";
      require IsOdd(k): "field order must be an odd power of 2";
    elif tp eq "2G" then
      require p eq 3: "field must have characteristic 3";
      require IsOdd(k): "field order must be an odd power of 3";
    end if;
    deg, eps, mult := basicDegrees(tp,n);
    N := (&+deg - n) div mult;
    if mult ne 1 then deg := [d div mult : d in deg]; end if;
    uord := q^N;
    for i := 1 to #deg do
      uord *:= q^deg[i] - eps[i];
    end for;
  end if;
  return case< Version |
    "Adjoint" : uord div ChevGrpCentre(tp,n,q),
    "Default" : (tp in ["B","D","2D"] and IsOdd(q)) select uord div 2 else uord,
     default  : uord >;
end intrinsic;

intrinsic ChevalleyGroupOrder(tp :: MonStgElt, n :: RngIntElt,
    F :: FldFin : Version := "Default") -> RngIntEltFact
{The  order of the Chevalley group of type tp and rank n
over the field F. The default is the order of the group returned by 
ChevalleyGroup.}
  q := #F;
  if tp in ["2A","2E"] then
    flag, q := IsSquare(q);
    require flag: "field order must be a square";
  elif tp eq "3D" then
    require n eq 4: "rank must be 4";
    flag, q := IsPower(q,3);
    require flag: "field order must be a cube";
  end if;
  return ChevalleyGroupOrder(tp, n, q : Version := Version);
end intrinsic;

toChevalley := function(type,d)
  case type:
    when "linear":
      n := d - 1;
      tp := "A";
    when "unitary":
      n := d - 1;
      tp := "2A";
    when "symplectic":
      n := d div 2;
      tp := "C";
    when "orthogonal":
      n := (d-1) div 2;
      tp := "B";
    when "orthogonalcircle":
      n := (d-1) div 2;
      tp := "B";
    when "orthogonalplus":
      n := d div 2;
      tp := "D";
    when "orthogonalminus":
      n := d div 2;
      tp := "2D";
    else
      error "unknown type " cat type;
  end case;
  return tp, n;
end function;

intrinsic ClassicalGroupOrder(type :: MonStgElt, d :: RngIntElt, q :: RngIntElt) -> RngIntElt
{The order and factored order of the classical group of linear, unitary, symplectic or 
 orthogonal type: SL, SU, Sp, Omega, OmegaPlus or OmegaMinus}

  case type:
    when "linear", "unitary":
      ignore := true;
    when "symplectic","orthogonalplus","orthogonalminus":
      require IsEven(d) : "degree must be even";
    when "orthogonal","orthogonalcircle":
      require IsOdd(d) : "degree must be odd";
    when "orthogonalcircle":
      require IsOdd(d) : "degree must be odd";
    else
      error "unknown type " cat type;
  end case;
  tp, n := toChevalley(type,d);
  return ChevalleyGroupOrder(tp,n,q);
end intrinsic;

intrinsic ClassicalGroupOrder(type :: MonStgElt, d :: RngIntElt, F :: FldFin) -> RngIntElt
{The order and factored order of the classical group of linear, unitary, symplectic or 
 orthogonal type: SL, SU, Sp, Omega, OmegaPlus or OmegaMinus}
  q := #F;
  if type eq "unitary" then
    flag, q := IsSquare(q);
    require flag: "field order must be a square";
  end if;
  return ClassicalGroupOrder(type, d, q);
end intrinsic;

intrinsic FactoredClassicalGroupOrder(type :: MonStgElt, d :: RngIntElt, q :: RngIntElt) -> RngIntElt
{The order and factored order of the classical group of linear, unitary, symplectic or 
 orthogonal type: SL, SU, Sp, Omega, OmegaPlus or OmegaMinus}
  case type:
    when "linear", "unitary":
      ignore := true;
    when "symplectic","orthogonalplus","orthogonalminus":
      require IsEven(d) : "degree must be even";
    when "orthogonal","orthogonalcircle":
      require IsOdd(d) : "degree must be odd";
    when "orthogonalcircle":
      require IsOdd(d) : "degree must be odd";
    else
      error "unknown type " cat type;
  end case;
  tp, n := toChevalley(type,d);
  return FactoredChevalleyGroupOrder(tp,n,q);
end intrinsic;

intrinsic FactoredClassicalGroupOrder(type :: MonStgElt, d :: RngIntElt, F :: FldFin) -> RngIntElt
{The order and factored order of the classical group of linear, unitary, symplectic or 
 orthogonal type: SL, SU, Sp, Omega, OmegaPlus or OmegaMinus}
  q := #F;
  if type eq "unitary" then
    flag, q := IsSquare(q);
    require flag: "field order must be a square";
  end if;
  return FactoredClassicalGroupOrder(type, d, q);
end intrinsic;

// Henrik Baarnhielm's code
// ------------------------

// Centre orders of SL, SU, Sp, Omega^(\epsilon)
// Used in ChevalleyGroupOrders and HBChevalleyGroupOrder
ClassicalCentreOrder := AssociativeArray();
ClassicalCentreOrder["linear"] := func<d, q | GCD(d, q - 1)>;
ClassicalCentreOrder["symplectic"] := func<d, q | GCD(2, q - 1)>;
ClassicalCentreOrder["unitary"] := func<d, q |
    (d eq 3 and qq eq 2) select 3 else GCD(d, qq + 1) where qq is Isqrt(q)>;
ClassicalCentreOrder["orthogonalcircle"] := func<d, q | 1>;
ClassicalCentreOrder["orthogonalplus"] := func<d, q |
    IsEven(q) select 1 else (IsEven(d * (q - 1) div 4) select 2 else 1)>;
ClassicalCentreOrder["orthogonalminus"] := func<d, q |
    IsEven(q) select 1 else (IsOdd(d * (q - 1) div 4) select 2 else 1)>;

ChevalleyGroupOrders := AssociativeArray();
ChevalleyGroupOrders["A"] := func<r, q | q^(r * (r + 1) div 2) *
    &*[(q^(i + 1) - 1) : i in [1 .. r]]>;
ChevalleyGroupOrders["B"] := func<r, q | q^(r^2) * &*[(q^(2 * i) - 1) :
    i in [1 .. r]] div GCD(2, q - 1)>;
ChevalleyGroupOrders["C"] := func<r, q | q^(r^2) * &*[(q^(2 * i) - 1) :
    i in [1 .. r]]>;

ChevalleyGroupOrders["D"] := func<r, q |
    r eq 1 select (q - 1) div (IsOdd(q) select 2 else 1) else
    q^(r * (r - 1)) * (q^r - 1) * &*[(q^(2 * i) - 1) : i in [1 .. r - 1]]
    div GCD(4, q^r - 1) * ClassicalCentreOrder["orthogonalplus"](2 * r, q)>;

ChevalleyGroupOrders["E"] := function(r, q)
    if r eq 6 then
        return q^36 * (q^12 - 1) * (q^9 - 1) * (q^8 - 1) * (q^6 - 1) *
	    (q^5 - 1) * (q^2 - 1);
    elif r eq 7 then
	return q^63 * (q^18 - 1) * (q^14 - 1) * (q^12 - 1) * (q^10 - 1) *
	    (q^8 - 1) * (q^6 - 1) * (q^2 - 1);
    elif r eq 8 then
	return q^120 * (q^30 - 1) * (q^24 - 1) * (q^20 - 1) * (q^18 - 1) *
	    (q^14 - 1) * (q^12 - 1) * (q^8 - 1) * (q^2 - 1);
    else
	error "No such Chevalley group";
    end if;
end function;

ChevalleyGroupOrders["F"] := func<r, q |
    q^24 * (q^12 - 1) * (q^8 - 1) * (q^6- 1) * (q^2 - 1)>;

ChevalleyGroupOrders["G"] := func<r, q | q^6 * (q^6 - 1) * (q^2 - 1)>;

ChevalleyGroupOrders["2A"] := func<r, qq | q^(r * (r + 1) div 2) *
    &*[q^(i + 1) - (-1)^(i + 1) : i in [1 .. r]] where q is Isqrt(qq)>;

ChevalleyGroupOrders["2D"] := func<r, q |
    r eq 1 select (q + 1) div (IsOdd(q) select 2 else 1) else
    q^(r * (r - 1)) * (q^r + 1) * &*[(q^(2 * i) - 1) : i in [1 .. r - 1]] div
    GCD(4, q^r + 1) * ClassicalCentreOrder["orthogonalminus"](2 * r, q)>;

ChevalleyGroupOrders["2E"] := func<r, qq |
    q^36 * (q^12 - 1) * (q^9 + 1) * (q^8 - 1) * (q^6 - 1) *
    (q^5 + 1) * (q^2 - 1) div GCD(3, q + 1) where q is Isqrt(qq)>;

ChevalleyGroupOrders["3D"] := function(r, qq)
    f := Factorization(qq);
    p := f[1][1];
    k := f[1][2] div 3;
    q := p^k;
//    print qq, p, k, q;
    return q^12 * (q^2 - 1) * (q^8 + q^4 + 1) * (q^6 - 1);
end function;

ChevalleyGroupOrders["2B"] := func<r, q | q^2 * (q^2 + 1) * (q - 1)>;
ChevalleyGroupOrders["2G"] := func<r, q | q^3 * (q^3 + 1) * (q - 1)>;
ChevalleyGroupOrders["2F"] := func<r, q |
    q^12 * (q^6 + 1) * (q^4 - 1) * (q^3 + 1) * (q - 1)>;


// Used in HBClassicalGroupOrder
ClassicalGroupOrders := AssociativeArray();
ClassicalGroupOrders["linear"] := func<d, q |
    ChevalleyGroupOrder("A", d - 1, q)>;
ClassicalGroupOrders["symplectic"] := func<d, q |
    ChevalleyGroupOrder("C", d div 2, q)>;
ClassicalGroupOrders["unitary"] := func<d, q |
    ChevalleyGroupOrder("2A", d - 1, q)>;
ClassicalGroupOrders["orthogonalcircle"] := func<d, q |
    ChevalleyGroupOrder("B", (d - 1) div 2, q)>;
ClassicalGroupOrders["orthogonalminus"] := func<d, q |
    ChevalleyGroupOrder("2D", d div 2, q)>;
ClassicalGroupOrders["orthogonalplus"] := func<d, q |
    ChevalleyGroupOrder("D", d div 2, q)>;

intrinsic HBChevalleyGroupOrder(name :: MonStgElt, rank :: RngIntElt, F :: FldFin) -> RngIntElt
{The order of the corresponding group returned by ChevalleyGroup.}

    // Try to create the group, or generate error
    G := ChevalleyGroup(name, rank, F);

    return ChevalleyGroupOrders[name](rank, #F);
end intrinsic;

intrinsic HBChevalleyGroupOrder(name :: MonStgElt, rank :: RngIntElt,
    q :: RngIntElt) -> RngIntElt
{The order of the corresponding group returned by ChevalleyGroup. }

    // Try to create the group, or generate error
    G := ChevalleyGroup(name, rank, q);

    return ChevalleyGroupOrders[name](rank, q);
end intrinsic;

intrinsic HBClassicalGroupOrder(type :: MonStgElt, d :: RngIntElt,
    q :: RngIntElt) -> RngIntElt
{The order of SL, Sp, SU or Omega^\epsilon }
    return ClassicalGroupOrders[type](d, q);
end intrinsic;

intrinsic HBClassicalGroupOrder(type :: MonStgElt, d :: RngIntElt,
    F :: FldFin) -> RngIntElt
{The order of SL, Sp, SU or Omega^\epsilon }
  q := #F;
  if type eq "unitary" then
    flag, q := IsSquare(q);
    require flag: "field order must be a square";
  end if;
  return ClassicalGroupOrders[type](d, q);
end intrinsic;


