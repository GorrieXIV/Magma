freeze;

declare attributes FldAlg : Conjugate, Signature;

intrinsic ChangePrecision(x::FldReElt, p::RngIntElt) -> FldReElt
{The given element to precision p}

  return RealField(p)!x;
end intrinsic;

intrinsic ChangePrecision(x::FldComElt, p::RngIntElt) -> FldReElt
{"} // "
  return ComplexField(p)!x;
end intrinsic;

intrinsic Conjugate(a::FldAlgElt[FldRat], s::[RngIntElt]: Prec := GetKantPrecision() ) -> FldElt
{Given an element 'a' in a number field K defined as a tower with n steps, and a sequence
s containing n positive integers, this returns the image of 'a' under the complex embedding
determined by s}

  require #s eq 1 : "The second argument should be a sequence containing 1 integer";

  if Type(a) eq FldCycElt then
    c := Conjugates(a:Precision := Prec)[s[1]];
  else
    c := Conjugate(a, s[1] : Precision:=Prec);
  end if;
  if IsReal(c) then
    c := Re(c);
  end if;
  return c;
end intrinsic;

function GetDepth(K)
  d := 0;
  while Type(K) ne FldRat do
    d +:= 1;
    K := CoefficientField(K);
  end while;
  return d;
end function;

function GetIndex(C, s)
//  "GetIndex(", C, ", ", s, ");";
  if #s gt 1 then
    return GetIndex(C[s[1]], s[2..#s]);
  else
    return C[s[1]];
  end if;
end function;

procedure SetIndex(~C, s, v)
//  "SetIndex(", C, ", ", s, ");";
  if #s gt 1 then
    if not IsDefined(C, s[1]) then
      C[s[1]] := [];
    end if;
    SetIndex(~C[s[1]], s[2..#s], v);
  else
    C[s[1]] := v;
  end if;
end procedure;

intrinsic IsDefined(L::List, p::RngIntElt) -> BoolElt
  {True iff the list L has length at least p}
  if p le #L then
    return true;
  else
    return false;
  end if;
end intrinsic;

function IsDefinedIndex(C, s)
//  "IsDefinedIndex(", C, ", ", s, ");";
  if not IsDefined(C, s[1]) then
    return false;
  end if;
  if #s eq 1 then
    return IsDefined(C, s[1]);
  end if;
  return IsDefinedIndex(C[s[1]], s[2..#s]);
end function;
 
intrinsic Precision(L::SeqEnum[FldComElt]) -> RngIntElt
  {The precision of the universe of the sequence L}
  return Precision(Universe(L));
end intrinsic;

intrinsic Precision(L::SeqEnum[FldReElt]) -> RngIntElt
  {"} // "
  return Precision(Universe(L));
end intrinsic;


function  ConjugateIsReal(K, s)
  if Type(s) eq RngIntElt then
    return s le Signature(K);
  elif #s eq 1 then
    return s[1] le Signature(K); 
  else
    if not ConjugateIsReal(CoefficientRing(K), s[1..#s-1]) then
      return false;
    else
      return GetIndex(K`Signature, s);
    end if;
  end if;
end function;

function GetLocalSignature(K, s)
  // s describes a conjugate of the CoefficientField of K
  if not assigned K`Conjugate or not IsDefinedIndex(K`Conjugate, s) then
    _ := Conjugate(K.1, s cat [1]); // to ensure the neccessary data is computed.
  end if;

  if ConjugateIsReal(CoefficientField(K), s) then
    c := GetIndex(K`Conjugate, s);
    if IsSimple(K) then
      r1 := #[ x : x in c | IsReal(x)];
      r2 := (#c - r1) div 2;
      return r1, r2;
    else
      r1 := #[ x : x in c | forall(y){y: y in x | IsReal(y)}];
      r2 := (Degree(K) - r1) div 2;
      return r1, r2;
    end if;
  else
    return Degree(K), 0;
  end if;
end function;

function ConjugateToPlace(K, s)
  if not assigned K`Conjugate or not IsDefinedIndex(K`Conjugate, s) then
    _ := Conjugate(K.1, s);
  end if;
  if ConjugateIsReal(K, s) then
    return InternalInfinitePlaceCreate(K, s);
  end if;
  if ConjugateIsReal(CoefficientField(K), s[1..#s-1]) then
    r1, r2 := GetLocalSignature(K, s[1..#s-1]);
    if s[#s] gt r1 then
      if s[#s] - r1 gt r2 then
        s[#s] -:= r2;
      end if;
    end if;
    return InternalInfinitePlaceCreate(K, s);
  else
    return InternalInfinitePlaceCreate(K, s);
  end if;
end function;

intrinsic Conjugate(a::FldAlgElt[FldAlg], s::[RngIntElt]: Prec := GetKantPrecision() ) -> FldElt
{Given an element 'a' in a number field K defined as a tower with n steps, and a sequence
s containing n positive integers, this returns the image of 'a' under the complex embedding
determined by s}

  K := Parent(a);
  require #s eq GetDepth(K) :
    "The sequence must have length ", GetDepth(K), " to describe a conjugate";
  d := #s;  
  repeat
    require s[d] le Degree(K) and s[d] ge 1:
      "Position ", d, " should be between 1 and ", Degree(K), " to describe a conjugate";
    K := CoefficientField(K);
    d -:= 1;
  until Type(K) eq FldRat;

  K := Parent(a);

  if not assigned K`Conjugate then
    K`Conjugate := [];
  end if;
  if not assigned K`Signature then
    K`Signature := [];
  end if;
  C := K`Conjugate;
  S := K`Signature;
  if (not IsDefinedIndex(C, s)) or Precision(GetIndex(C, s)) lt Prec then
    if IsSimple(K) then
      prec := Prec;
      repeat
        f := Polynomial([Conjugate(x/1, s[1..#s-1] : Prec := prec) 
                                    : x in Eltseq(DefiningPolynomial(K))]);
        r := Roots(f, ComplexField(prec));
        Sort(~r, func<a,b| Sign(Arg(a[1]) - Arg(b[1]))*2 + 
                                    Sign(Abs(a[1])-Abs(b[1]))>);
        if ConjugateIsReal(CoefficientField(K), s[1..#s-1]) then
          eps := RealField(prec)!2^(-prec div 2);
          rr := [];
          ri := [];
          for i in r do
            if Abs(Im(i[1])) le eps then
              Append(~rr, Re(i[1]));
            else
              if forall(x){x : x in ri | Abs(Im(x+i[1])) gt eps} then
                Append(~ri, i[1]);
              end if;
            end if;
          end for;
          SetIndex(~S, s[1..#s-1], 
            [true : x in rr] cat [false : x in ri] cat [ false : x in ri]);
        else
          rr := [x[1] : x in r];
          ri := [];
          SetIndex(~S, s[1..#s-1], [false : x in rr]);
        end if;
        r1 := #rr;
        r2 := #ri;
        prec := Round(prec * 1.2);
        if r1 + 2*r2 gt Degree(K) then
          error "Error: too many conjugates found";
        end if;
      until r1 + 2*r2 eq Degree(K);
      r := [* x : x in rr *] cat [* x : x in ri *] cat
                                 [* ComplexConjugate(x) : x in ri*];
    else
      prec := Prec;
      repeat
        r := [];
        CR := ComplexField(prec);

        for i in DefiningPolynomial(K) do
          f := Polynomial([Conjugate(x, s[1..#s-1]: Prec := Prec)
                                    : x in Eltseq(i)]);
              
          f := Roots(f, CR);                          
          Sort(~f, func<a,b| Sign(Arg(a[1]) - Arg(b[1]))*2 + 
                                      Sign(Abs(a[1])-Abs(b[1]))>);
          f := [x[1] : x in f]; 
          if #r gt 0 then
            ChangeUniverse(~r, PowerSequence(CoveringStructure(Universe(r[1]), Universe(f))));
          end if;
          Append(~r, f);
        end for;
        r := [* [y : y in x] : x in CartesianProduct(r) *];

        if ConjugateIsReal(CoefficientField(K), s[1..#s-1]) then
          eps := RealField(prec)!2^(-prec div 2);
          rr := [];
          ri := [];
          for i in r do
            if &+ [ Abs(Im(j)) : j in i] le eps then
              Append(~rr, [ Re(j): j in i]);
            else
              if forall(x){x : x in ri | 
                   &+ [ Abs(Im(x[j]+i[j])) : j in [1..#x]] gt eps} then
                Append(~ri, i);
              end if;
            end if;
          end for;
          SetIndex(~S, s[1..#s-1], 
            [true : x in rr] cat [false : x in ri] cat [ false : x in ri]);
        else
          rr := r;
          ri := [];
          SetIndex(~S, s[1..#s-1], [false : x in rr]);
        end if;
        r1 := #rr;
        r2 := #ri;
        prec := Round(prec * 1.2);
        if r1 + 2*r2 gt Degree(K) then
          error "Error: too many conjugates found";
        end if;
      until r1 + 2*r2 eq Degree(K);
      r := [* x : x in rr *] cat [* x : x in ri *] cat
                                 [* [ ComplexConjugate(y) : y in x] : x in ri*];

    end if;

    SetIndex(~C, s[1..#s-1], r );
  end if;

  K`Conjugate := C;
  K`Signature := S;
  c := GetIndex(C, s);
  if ISA(Type(c), FldElt) then
    P := Parent(c);
  else
    P := Universe(c);
  end if;
  return ChangePrecision(hom<K -> P |
    map<CoefficientField(K) -> P | x :-> Conjugate(x, s[1..#s-1] 
                            : Prec := Prec)>, GetIndex(C, s)>(a),
    Prec);
end intrinsic;

//intrinsic Decomposition(K::FldNum[FldRat], p::[Infty]) -> []
//  {}
//  return Decomposition(K, p[1]);
//end intrinsic;
intrinsic Decomposition(K::FldAlg[FldAlg], p::PlcNumElt) -> []
  {The decomposition in K of the infinite place p}
  k := NumberField(p);
  require CoefficientField(K) cmpeq k:
    "The place must be from the coefficient field of the first argument";
  
  f, s := IsInfinite(p);
  require f :
    "The place must be an infinite place of the coefficient field";
  
 if Type(s) cmpeq RngIntElt then
   s := [s];
 end if;
 r1, r2 := GetLocalSignature(K, s);
 if IsReal(p) then
   return [ <InternalInfinitePlaceCreate(NumberField(K), s cat [i]), 1> : i in [1..r1]]
     cat  [ <InternalInfinitePlaceCreate(NumberField(K), s cat [i+r1]), 2> : i in [1..r2]];
 else
   return [ <InternalInfinitePlaceCreate(NumberField(K), s cat [i]), 1> : i in [1..r1]];
 end if;
end intrinsic;

intrinsic IsReal(p::PlcNumElt) -> BoolElt
  {Returns true iff p is an infinite real place}
  f, s := IsInfinite(p);
  if not f then
    return false;
  end if;
  return ConjugateIsReal(NumberField(p), s);
end intrinsic;

intrinsic IsComplex(p::PlcNumElt) -> BoolElt
  {Returns true iff p is an infinite complex place}
  f, s := IsInfinite(p);
  if not f then
    return false;
  end if;
  return not ConjugateIsReal(NumberField(p), s);
end intrinsic;

intrinsic InfinitePlaces(K::FldAlg) -> SeqEnum
{The infinite places of the number field K}
    
    i := InfinitePlaces(CoefficientField(K));
    return &cat [ [ p[1] : p in Decomposition(K, j) ] : j in i];
end intrinsic;

intrinsic InfinitePlaces(O::RngOrd) -> SeqEnum
{The infinite places of the order O}
    return InfinitePlaces(NumberField(O));
end intrinsic;

intrinsic RealPlaces(F::FldAlg) -> SeqEnum
{The real places of the field F.}
    if IsAbsoluteField(F) then
        r := Signature(F);
        return InfinitePlaces(F)[1..r];
    else
        // TO DO more directly
        return [v : v in InfinitePlaces(F) | IsReal(v)];
    end if;
end intrinsic;

intrinsic RealPlaces(F::FldRat) -> SeqEnum
{"} //"
    return InfinitePlaces(F);
end intrinsic;


intrinsic Evaluate(x::RngElt, p::PlcNumElt : Precision := 0) -> RngElt
{The image of x in the residue class field of p when p is a finite place,
 or in the completion at p when p is an infinite place}

    K := NumberField(p);
    coercible, x := IsCoercible(K, x);
    require coercible : "The first argument must be an element of " *
                        "the number field of the second argument";

    infinite, i := IsInfinite(p);
    if infinite then

        if Type(i) eq RngIntElt then
          i := [i];
        end if;
	if Precision eq 0 then return Conjugate(x, i); end if;

	require Precision ge 4  or Precision eq 0 : "Parameter Precision must be at least 4";

	xp := Conjugate(x, i:Prec := Precision);
	return xp;
    end if;

    require Valuation(x, p) ge 0 : "Element must have non-negative valuation";
    _, m := ResidueClassField(Ideal(p));
    return m(x);
end intrinsic;

intrinsic Generators(K::FldAlg, k::FldAlg) -> {}
  {A set of k-generators for K, assuming K is a direct extension of k}
  if BaseField(K) cmpeq k then
    return Generators(K);
  end if;
  L := BaseField(K);
  while L cmpne k and Type(L) ne FldRat do
    L := BaseField(L);
  end while;
  require k cmpeq L: "K must be an direct extension of k!";
    
  if AbsoluteDegree(BaseField(K)) gt AbsoluteDegree(k) then
    return Generators(K) join Generators(CoefficientField(K), k);
  else
    require false:
      "K must be an direct extension of k!";
  end if;
end intrinsic;

intrinsic Generators(K::FldAlg, k::FldRat) -> {}
  {"} // "
  if IsAbsoluteField(K) then
    return Generators(K);
  else
    return Generators(K) join Generators(CoefficientField(K), k);
  end if;
end intrinsic;

intrinsic GeneratorsSequence(K::FldAlg, k::FldAlg) -> []
  {A sequence of k-generators for K, assuming K is a direct extension of k}
  if BaseField(K) cmpeq k then
    return GeneratorsSequence(K);
  end if;
  L := BaseField(K);
  while L cmpne k and Type(L) ne FldRat do
    L := BaseField(L);
  end while;
  require k cmpeq L: "K must be an direct extension of k!";
    
  if AbsoluteDegree(BaseField(K)) gt AbsoluteDegree(k) then
    return GeneratorsSequence(K) cat GeneratorsSequence(CoefficientField(K), k);
  else
    require false:
      "K must be an direct extension of k!";
  end if;
end intrinsic;

intrinsic GeneratorsSequence(K::FldAlg, k::FldRat) -> []
  {"} // "
  if IsAbsoluteField(K) then
    return GeneratorsSequence(K);
  else
    return GeneratorsSequence(K) cat GeneratorsSequence(CoefficientField(K), k);
  end if;
end intrinsic;

intrinsic NumberOfGenerators(K::FldAlg, k::FldAlg) -> RngIntElt
  {The number of k-generators for K}

   if BaseField(K) cmpeq k then
    return NumberOfGenerators(K);
  end if;
  L := BaseField(K);
  while L cmpne k and Type(L) ne FldRat do
    L := BaseField(L);
  end while;
  require k cmpeq L: "K must be an direct extension of k!";
    
  if AbsoluteDegree(BaseField(K)) gt AbsoluteDegree(k) then
    return NumberOfGenerators(K) + NumberOfGenerators(CoefficientField(K), k);
  else
    require false:
      "K must be an direct extension of k!";
  end if;
end intrinsic;

intrinsic NumberOfGenerators(K::FldAlg, k::FldRat) -> []
  {"} // "
  if IsAbsoluteField(K) then
    return NumberOfGenerators(K);
  else
    return NumberOfGenerators(K) + NumberOfGenerators(CoefficientField(K), k);
  end if;
end intrinsic;

  
intrinsic Distance(x::FldReElt, L::[FldComElt] : Max:=Infinity())
 -> FldReElt,RngIntElt
{The Distance between x and L, ie. the minimal distance between x
 and an element of L. The Position of this element is also returned.}
 require #L ne 0: "Array must be nonempty";
 m,pos:=Minimum([Abs(x-y) : y in L]); if m ge Max then m:=Max; pos:=0; end if;
 return m,pos; end intrinsic;

intrinsic Distance(x::FldReElt, L::[FldReElt] : Max:=Infinity())
 -> FldReElt,RngIntElt  {"} // "
 require #L ne 0: "Array must be nonempty";
 m,pos:=Minimum([Abs(x-y) : y in L]); if m ge Max then m:=Max; pos:=0; end if;
 return m,pos; end intrinsic;

intrinsic Distance(x::FldComElt, L::[FldReElt] : Max:=Infinity())
 -> FldReElt,RngIntElt  {"} // "
 require #L ne 0: "Array must be nonempty";
 m,pos:=Minimum([Abs(x-y) : y in L]); if m ge Max then m:=Max; pos:=0; end if;
 return m,pos; end intrinsic;

intrinsic Distance(x::FldComElt, L::[FldComElt] : Max:=Infinity())
 -> FldReElt,RngIntElt  {"} // "
 require #L ne 0: "Array must be nonempty";
 m,pos:=Minimum([Abs(x-y) : y in L]); if m ge Max then m:=Max; pos:=0; end if;
 return m,pos; end intrinsic;

intrinsic Diameter(L::[FldReElt]:Eps := 0,Max:=Infinity()) -> FldReElt
 {The diameter of L, ie. the shortest distance between two different elements}
 A:=[Abs(x-y) : x,y in L | Abs(x-y) gt Eps];
 if #A eq 0 then return Eps; end if; m:=Min(A);
 if m ge Max then m:=Max; end if; return m; end intrinsic;

intrinsic Diameter(L::[FldComElt]:Eps := 0,Max:=Infinity()) -> FldReElt {"}// "
 A:=[Abs(x-y) : x,y in L | Abs(x-y) gt Eps];
 if #A eq 0 then return Eps; end if; m:=Min(A);
 if m ge Max then m:=Max; end if; return m; end intrinsic;

intrinsic Extends(P::PlcNumElt, p::PlcNumElt) -> BoolElt
  {Determines if P is an extension of p}


  K := NumberField(P);
  k := NumberField(p);

  if IsFinite(P) ne IsFinite(p) then
      return false;
  end if;
    

  g := Generators(k, Rationals());
  if not CanChangeUniverse(g, K) then
    return false;
  end if;
  if IsFinite(P) then 
    return forall{x : x in Basis(Ideal(p)) | (K!x) in Ideal(P)};
  end if;

  lK := InfinitePlaces(K);
  if #lK eq 1 then return true; end if;
  lp := Position(lK, P);
  for i in g do
    L := [Evaluate(i, j:Precision := 300) : j in lK];
    l := Evaluate(i, p:Precision := 300);
    m := Minimum(Distance(l,L:Max:=1),Distance(ComplexConjugate(l),L:Max:=1));
    d := Diameter(L:Eps := 2^-150,Max:=1);
    if m ge d*10^-4 then return false; end if;
    if Abs(L[lp] -l) gt d * 10^-4 and 
       Abs(ComplexConjugate(L[lp])-l) gt d*10^-4 then return false; end if; 
  end for;
  return true;
end intrinsic;

intrinsic Valuation(x::RngElt, P::PlcNumElt) -> RngElt
  {The Valuation of x at P}
  K := NumberField(P);
  f, x := IsCoercible(K, x);
  require f:
    "The 1st argument must be coercible into the number field of the 2nd argument";
  if IsFinite(P) then
    return Valuation(x, Ideal(P));
  else
    return Log(Abs(Evaluate(x, P)));
  end if;
end intrinsic;

intrinsic Signature(x::FldAlgElt[FldRat]) -> []
  {The signature if x, ie the sign of each real embedding}
  
  r1 := Signature(Parent(x));
  c := Conjugates(x:Precision := 10);
  return [Sign(Re(c[i])) : i in [1..r1]];
end intrinsic;

