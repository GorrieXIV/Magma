freeze;

function IsRingExt(O)
    return Type(O) in {RngOrd, RngCyc, RngQuad, RngFunOrd};
end function;

///////////////////////////////////////////////////////////////////////////////
//   Different                                                               //
///////////////////////////////////////////////////////////////////////////////
function RingExtDifferent(O)
//Computes the Different of the maximal order O.

  return Different(1*O);
end function;


function RingExtEltDifferent(a)
//Computes the Different of a.

  p := CharacteristicPolynomial(a);
  if Degree(p) eq Degree(Parent(a)) then
    return Evaluate(Derivative(p), a);
  else
    return Parent(a)!0;
  end if;  
end function;

///////////////////////////////////////////////////////////////////////////////
//   IsAbsolute                                                              //
///////////////////////////////////////////////////////////////////////////////

function RingExtIsAbsoluteOrder(O)
// Whether the coefficient ring of O is an extension
// CF: Careful: when extending RngQuad (or RngCyc), the types differ...
    return not ISA(Type(BaseRing(O)),Type(O));
end function;  

///////////////////////////////////////////////////////////////////////////////
//   Inert                                                                   //
///////////////////////////////////////////////////////////////////////////////

function RingExtIsInertIdeal(P)
//{Returns true iff P is inert over the BaseRing}
    return Degree(P) eq Degree(Order(P));
end function;

function RingExtIsInert(P, O)
//{Returns true iff P is inert in the extension O of its order}
    l := DecompositionType(O, P); 
    return exists(x){x[1] : x in l | x[1] eq Degree(O)};
end function;

///////////////////////////////////////////////////////////////////////////////
//   Ramification                                                            //
///////////////////////////////////////////////////////////////////////////////

function RingExtIsRamifiedIdeal(P)
//{Returns true iff P is ramified over the BaseRing}
  return RamificationIndex(P) ne 1;
end function; 

function RingExtIsRamified(P, O)
//{Returns true iff P is ramified in the extension O of its order}
  if Type(O) eq RngFunOrd then
    l := Factorisation(O*P); 
  else
    l := Decomposition(O, P); 
  end if;
  return exists(x){x[1] : x in l | IsRamified(x[1])};
end function; 

///////////////////////////////////////////////////////////////////////////////
//   Split                                                                   //
///////////////////////////////////////////////////////////////////////////////

function RingExtIsSplitIdeal(P)
// Returns true iff P splits over the BaseRing
  O := Order(P);
  if RingExtIsAbsoluteOrder(O) then
    return #DecompositionType(O, Minimum(P)) ge 2;
  else  
    return #DecompositionType(O, P meet BaseRing(O)) ge 2;
  end if;  
end function;

function RingExtIsSplit(P, O)
// Returns true iff P splits in the extension O of its order
  l := DecompositionType(O, P); 
  return #l ge 2;
end function;

///////////////////////////////////////////////////////////////////////////////
//   Tame Ramification                                                       //
///////////////////////////////////////////////////////////////////////////////

function RingExtIsTamelyRamifiedIdeal(P)
// Returns true iff P is tamly ramified over the BaseRing
  F := ResidueClassField(P);
  if Characteristic(F) eq 0 then
    return RamificationIndex(P) gt 1;
  else
    return RamificationIndex(P) gt 1 and
           RamificationIndex(P) mod Characteristic(F) ne 0;
  end if;
end function;

function RingExtIsTamelyRamified(P, O)
// Returns true iff P is tamly ramified in the extension O of its order
  if Type(O) eq RngFunOrd then
    l := Factorisation(O*P); 
  else
    l := Decomposition(O, P); 
  end if;
  F := ResidueClassField(l[1][1]);
  if Characteristic(F) eq 0 then
    return exists(x){x[2] : x in l | x[2] gt 1};
  else
    return exists(x){x[2] : x in l | x[2] gt 1} and
           forall(x){x[2] : x in l | (x[2] gt 1
                     and x[2] mod Characteristic(F) ne 0)};
  end if;                      
end function;

function RingExtIsTamelyRamifiedOrder(O)
// Returns true iff O is tamely ramified
  LP := Factorisation(Discriminant(O));
  return forall(x){x[1] : x in LP | RingExtIsTamelyRamified(x[1], O)};
end function;

///////////////////////////////////////////////////////////////////////////////
//   Total Ramification                                                      //
///////////////////////////////////////////////////////////////////////////////

function RingExtIsTotallyRamifiedIdeal(P)
// Returns true iff P is totally ramified over the BaseRing
  return RamificationIndex(P) eq Degree(Order(P));
end function;

function RingExtIsTotallyRamified(P, O)
// Returns true iff P is totally ramified in the extension O of its order
  l := DecompositionType(O, P); 
  return exists(x){x[2] : x in l | x[2] eq Degree(O)};
end function;

function RingExtIsTotallyRamifiedOrder(O)
// Returns true iff O is totally ramified
  return exists(x){x[1] : x in Factorisation(Discriminant(O)) 
					 | RingExtIsTotallyRamified(x[1], O)};
end function;

///////////////////////////////////////////////////////////////////////////////
//   Totally Split                                                           //
///////////////////////////////////////////////////////////////////////////////

function RingExtIsTotallySplitIdeal(P)
// Returns true iff P splits totally over the BaseRing
  O := Order(P);
  if RingExtIsAbsoluteOrder(O) then
    return #DecompositionType(O, Minimum(P)) eq Degree(O);
  else  
    return #DecompositionType(O, P meet BaseRing(O)) eq Degree(O);
  end if;  
end function;

function RingExtIsTotallySplit(P, O)
// Returns true iff P splits totally in the extension O of its order
  l := DecompositionType(O, P); 
  return #l eq Degree(O);
end function;

///////////////////////////////////////////////////////////////////////////////
//   Unramified                                                              //
///////////////////////////////////////////////////////////////////////////////

function RingExtIsUnramifiedIdeal(P) 
// Returns true iff P is unramified over the BaseRing
  return RamificationIndex(P) eq 1;
end function;

function RingExtIsUnramified(P, O)
// Returns true iff P is unramified in the extension O of its order
  l := DecompositionType(O, P); 
  return not exists(x){x[2] : x in l | x[2] ge 2};
end function;

function RingExtIsUnramifiedOrder(O) 
// Returns true iff O is unramified at the finite places
  d := Discriminant(O);
  if ISA(Type(d), RngElt) then
    return IsUnit(d);
  else
    return d eq 1*BaseRing(O);
  end if;  
end function;

///////////////////////////////////////////////////////////////////////////////
//   Wild Ramification                                                       //
///////////////////////////////////////////////////////////////////////////////

function RingExtIsWildlyRamifiedIdeal(P) 
// Returns true iff P is wildly ramified over the BaseRing
    c := Characteristic(ResidueClassField(P));
    if c eq 0 then
	return false;
    else
	return RamificationIndex(P) mod c eq 0;
    end if;
end function;

function RingExtIsWildlyRamified(P, O) 
// Returns true iff P is wildly ramified in the extension O of its order
    c := Characteristic(O);
    if c eq 0 and Type(P) eq RngIntElt then
	c := P;    
    elif c eq 0 and Type(P) eq RngOrdIdl then
        c := Minimum(P);
    end if;
    if c eq 0 then
	return false;
    else
      l := DecompositionType(O, P); 
      return exists(x){x[2] : x in l | x[2] mod c eq 0};
    end if;
end function;

function RingExtIsWildlyRamifiedOrder(O) 
// Returns true iff O is wildly ramified}
  return exists(x){x[1] : x in Factorisation(Discriminant(O)) 
					 | RingExtIsWildlyRamified(x[1], O)};
end function;

/*
///////////////////////////////////////////////////////////////////////////////
//   Conductor                                                               //
///////////////////////////////////////////////////////////////////////////////

intrinsic Conductor(O::RngOrd) -> RngOrdIdl
{Computes the Conductor of O in its MaximalOrder.}
  require Category(BaseRing(O)) eq RngInt or
          IsMaximal(BaseRing(O)) : "BaseRing(O) must be Z or a maximal order.";

  M := MaximalOrder(O);
  FO := FieldOfFractions(O);

  if Category(BaseRing(O)) eq RngInt then
    B := [FO| x: x in Basis(M) ];
    den := LCM([Denominator(x) : x in B ] );
    B := [ Transpose(AbsoluteRepresentationMatrix(O!(x*den))) : x in B ];
    B := VerticalJoin(B);
    B := BasisMatrix(Image(B));
    B := Matrix(FieldOfFractions(BaseRing(O)), B);
    B := B^-1*den;
    B := Matrix(BaseRing(O), B);
    return ideal<O | Transpose(B)>; 
  else
    n := Degree(O);
    k := FieldOfFractions(BaseRing(O));
    B := [FO| x: x in Basis(M) ];
    B := [ Transpose(RepresentationMatrix(x)) : x in B ];
    B := VerticalJoin(B);
    idO := [ x[1] : x in PseudoBasis(Module(O)) ];
    idM := [ x[1] : x in PseudoBasis(Module(M)) ];
    id := [ idM[j] / idO[i] : i in [1..n], j in [1..n] ];
    B := [ car<PowerIdeal(k),
               RSpace(k, n)> |
               <id[i], B[i]> : i in [1..n*n] ];
    B := Module(B);
    B := Dual(B);
    return ideal<O | B>;
  end if;

end intrinsic; 

///////////////////////////////////////////////////////////////////////////////
//   subset                                                                  //
///////////////////////////////////////////////////////////////////////////////

intrinsic 'subset'(I1::RngOrdIdl, I2::RngOrdIdl) -> BoolElt
{True iff I1 is a subset of I2}
  require Order(I1) eq Order(I2) : "Ideals must belong to the same order";

  return I1 meet I2 eq I1;
end intrinsic;  

///////////////////////////////////////////////////////////////////////////////
//   pSelmer                                                                 //
///////////////////////////////////////////////////////////////////////////////

intrinsic pSelmerGroup (O::RngOrd, p::RngIntElt, S::SetEnum) -> GrpAb, Map
{Computes the (p, S)-Selmer group of O.}
  require IsPrime(p): "2nd argument must be a prime number";
  require IsMaximal(O) and IsAbsoluteOrder(O)
               : "1st argument must be an absolute maximal order";
  require Category(Representative(Universe(S))) eq RngOrdIdl and
          Order(Representative(Universe(S))) eq O and
          &and { IsPrime(x) : x in S } 
               : "3rd argument must contain prime ideals of the 1st argument";

  IdealGenerator := function(I)
    _,a := IsPrincipal(I);
    return a;
  end function;

  MatrixIndex := function(M)
    if #M eq 0 or #M lt Ncols(M[1]) then
      return 0;
    end if;  
    M := Matrix(Parent(M[1][1]), 
           #M, Ncols(M[1]), &cat [ Eltseq(x) : x in M ]);
    M := EchelonForm(M);
    return &* [ M[i][i] : i in [1..Minimum(Nrows(M), Ncols(M))] ];
  end function;  


  G, m := ClassGroup(O: Proof := "Current");

  M := DiagonalMatrix(AbelianInvariants(G));
  for i in S do
    M := VerticalJoin(M, Vector(Eltseq(i@@m)));
  end for; 

  M := VerticalJoin(M, p*IdentityMatrix(Integers(), Ncols(M)));

  M := HermiteForm(M);

  gens := [O|];

  T, tm := SUnitGroup([x : x in S] );

  if Order(T.1) mod p eq 0 then
    Append(~gens, T.1 @ tm);
  end if;

  for i in [2..#Generators(T)] do
    Append(~gens, T.i @ tm);
  end for;

  if &* [Integers() | M[i][i] : i in [1..Ncols(M)] ] mod p eq 0 then
    j := [ IdealGenerator((G.i @ m)^(Order(G.i))) : i in [1..#Generators(G)]];
  end if;  

  for i in [1..Ncols(M)] do
    if M[i][i] mod p eq 0 then
      Append(~gens, j[i]);
    end if;
  end for;  

  one_ideal := function(P, elt)
    FF, map := ResidueClassField(P);
    elt := map(elt);
    elt := elt^((Norm(P)-1) div p);
    elt := Log(elt);
    return GF(p)!((elt * p) div (Norm(P)-1)) ;
  end function;

  data := [RSpace(GF(p), #gens)| ];
  ideal := [ PowerIdeal(O) | ];
  P := NextPrime(1000);
  repeat
    lp := Factorisation(P*O);
    for i in lp do
      if not i[1] in S and not O!p in i[1] and Norm(i[1]) mod p eq 1 then
        Append(~data, [ one_ideal(i[1], x) : x in gens ]);
        Append(~ideal, i[1]);
      end if;
    end for;
    P := NextPrime(P);
  until MatrixIndex(data) ne 0;
  

  G := AbelianGroup([ p: x in gens ]);

  disc_log := function(x)
    if Parent(x) ne O then
      error "Argument must be an element of ", O;
    end if;

    mat := Matrix(Parent(data[1][1]), 0, Ncols(data[1]), [ ]);
    rgh := [Parent(data[1][1])|];
    for i in [1..#data] do
      if not x in ideal[i] then
        mat := VerticalJoin(mat, data[i]);
        Append(~rgh, one_ideal(ideal[i], x));
      end if;
    end for;

    rgh := Matrix(Parent(rgh[1]), 1, #rgh, rgh);

    sol, ker := Solution(Transpose(mat), rgh);
    if Rank(ker) eq 0 then 
      return G![Integers()| x : x in Eltseq(sol)];
    end if;  
    PP := P;
    while Rank(ker) ne 0 do
      lp := Factorisation(P*O);
      for i in lp do
        if not i[1] in S and not O!p in i[1] and Norm(i[1]) mod p eq 1 
           and not x in i[1] then
          mat := VerticalJoin(mat, 
                  Vector([ one_ideal(i[1], x) : x in gens ]));
          rgh := Eltseq(rgh);
          Append(~rgh, one_ideal(i[1], x));
          rgh := Matrix(Parent(rgh[1]), 1, #rgh, rgh);
        end if;
      end for;
      PP := NextPrime(PP);
      sol, ker := Solution(Transpose(mat), rgh);
    end while; 

    sol;
    return G![Integers()| x : x in Eltseq(sol)];
  end function;  

  disc_exp := function(x)
    x := Eltseq(x);
    return &* [ gens[i] ^ x[i]: i in [1..#gens] ];
  end function;  

  return G, map<O -> G| x:-> disc_log(x), y :-> disc_exp(y)>;
end intrinsic; 

///////////////////////////////////////////////////////////////////////////////
//   Total Ramification                                                      //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsTotallyRamified(K::FldAlg) -> BoolElt
{Returns true iff K is totally ramified}
  O := MaximalOrder(K);
  return IsTotallyRamified(O);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Wild Ramification                                                       //
///////////////////////////////////////////////////////////////////////////////
intrinsic IsWildlyRamified(K::FldAlg) -> BoolElt
{Returns true iff K is wildly ramified}
  O := MaximalOrder(K);
  return IsWildlyRamified(O);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Tame Ramification                                                       //
///////////////////////////////////////////////////////////////////////////////
intrinsic IsTamelyRamified(K::FldAlg) -> BoolElt
{Returns true iff K is wildly ramified}
  return not IsWildlyRamified(K);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Unramified                                                              //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsUnramified(K::FldAlg) -> BoolElt
{Returns true iff K is wildly ramified}
  return IsUnramified(MaximalOrder(K));
end intrinsic;


*/

///////////////////////////////////////////////////////////////////////////////
//   AbsoluteDiscriminant                                                    //
///////////////////////////////////////////////////////////////////////////////

function RingExtAbsoluteDiscriminant(O)
//Computes the discrimant of O over the denominator ring

    d := Discriminant(O);
    t := AbsoluteDegree(O);
    while IsRingExt(BaseRing(O)) do
	n := t div AbsoluteDegree(O) * Degree(O);
	O := BaseRing(O);
	d := Norm(d) * Discriminant(O)^n;
    end while;
    return d;
end function;

