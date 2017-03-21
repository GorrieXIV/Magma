freeze;
////////////////////////////////////////////////////////////////////
//                                                                //  
//                            Witt Rings                          //
//                            David Kohel                         // 
//                            patched by                          //
//                           Claus Fieker                         //
//                                                                // 
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
//                                                                //
//                     Attribute declarations                     //
//                                                                // 
////////////////////////////////////////////////////////////////////

declare type RngWitt[RngWittElt];

declare attributes RngWitt:
   BaseRing,
   Length,
   CodomainRing,
   CoAddition,
   CoMultiplication,
   LocalRingMap;

declare attributes RngWittElt:
   Parent,
   Element;

////////////////////////////////////////////////////////////////////
//                                                                // 
//                       Creation functions                       // 
//                                                                //
////////////////////////////////////////////////////////////////////

function WR_elt_create(W, S)
  x := New(RngWittElt);
  x`Parent := W;
  x`Element := S; 
  return x;  
end function;


// Pass in a sequence here to evaluate at and make use of the repetition
// This might not work so well as it won't take advantage of the cancellation
// SLPolys will also miss the cancellation

function CoAddn(P,p,n)
   A := [ P.1 + P.(n+1) ];
   a := []; b := [P.1]; c := [P.(n+1)];
   for i in [1..n-1] do
      // -F(A+/-B)^(i-1)
      for k in [1 .. #a] do
	a[k] *:= A[k]^(p^(i-k+1) - p^(i-k));
      end for;
      Append(~a, -p^(i-1)*A[i]^p);
      //a := - &+[ p^(j-1)*A[j]^(p^(i+1-j)) : j in [1..i] ];
      // F(A)^(i-1)
      for k in [1 .. #b] do
	b[k] *:= P.k^(p^(i-k+1)-p^(i-k));
      end for;
      Append(~b, p^i*P.(i+1));
      //b :=  &+[ p^(j-1)*P.j^(p^(i+1-j)) : j in [1..i+1] ];
      // F(B)^(i-1)
      for k in [1 .. #c] do
	c[k] *:= P.(n+k)^(p^(i-k+1)-p^(i-k));
      end for;
      Append(~c, p^i*P.(n+i+1));
      //c := &+[ p^(j-1)*P.(n+j)^(p^(i+1-j)) : j in [1..i+1] ];
      A[i+1] := (&+a  +   &+b   +    &+c) div p^i;      
   end for;
   // print "A =", A;
   return A;
end function; 

function CoMult(P,p,n)
   M := [ P.1 * P.(n+1) ]; 
   for i in [1..n-1] do
      M[i+1] := ( - &+[ p^(j-1)*M[j]^(p^(i+1-j)) : j in [1..i] ] + 
         &+[ p^(j-1)*P.j^(p^(i+1-j)) : j in [1..i+1] ] *       
         &+[ p^(j-1)*P.(n+j)^(p^(i+1-j)) : j in [1..i+1] ]) div p^i;
   end for;
   // print "M =", M;
   return M;
end function; 

intrinsic WittRing(F::Fld,n::RngIntElt) -> RngWitt
   {The finite Witt ring of length n over F.}
   p := Characteristic(F);
   require p ne 0: "F must be of finite characteristic";
   W := New(RngWitt);
   W`BaseRing := F;
   W`Length := n;
   P := SLPolynomialRing(Integers(),2*n);
   PI := PolynomialRing(Integers(),2*n);
   AssignNames(~PI,
      [ "X" cat IntegerToString(i) : i in [0..n-1] ] cat 
      [ "Y" cat IntegerToString(i) : i in [0..n-1] ] );
   P := PolynomialRing(F, 2*n);
   AssignNames(~P,
      [ "X" cat IntegerToString(i) : i in [0..n-1] ] cat 
      [ "Y" cat IntegerToString(i) : i in [0..n-1] ] );
   W`CodomainRing := P;
   W`CoAddition := [P!x : x in CoAddn(PI,p,n)];
   W`CoMultiplication := [P!x : x in CoMult(PI,p,n)];
   h := hom< F -> W | x :-> [ x^(p^i) : i in [0..n-1] ] >;
   return W, h;   
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                         Coercions                              //
//                                                                // 
////////////////////////////////////////////////////////////////////

intrinsic IsCoercible(W::RngWitt,S::.) -> BoolElt, RngWittElt
   {}
   if Type(S) eq RngWittElt then
      if Parent(S) eq W then return true, S; end if;
   elif Type(S) eq RngIntElt then
      p := Characteristic(BaseRing(W));
      if S eq -1 and p eq 2 then
         R := W`BaseRing; 
         x := New(RngWittElt);
         x`Parent := W;
         x`Element := [ R | 1 : i in [1..Length(W)] ]; 
         return true, x;   
      elif S in {-1,0,1} then
         R := W`BaseRing; 
         x := New(RngWittElt);
         x`Parent := W;
         x`Element := [R!S] cat [ R | 0 : i in [1..Length(W)-1] ]; 
         return true, x;   
      end if;  
      return true, S*(W!1); 
   elif Type(S) eq Type(W`BaseRing) then
      R := W`BaseRing; 
      if S in R then
         x := New(RngWittElt);
         x`Parent := W;
         x`Element := [R!S] cat [ R | 0 : i in [1..Length(W)-1] ]; 
         return true, x;   
      end if;
   elif Type(S) eq SeqEnum then
      R := W`BaseRing; 
      f, S := CanChangeUniverse(S, R);
      if f and #S eq Length(W) then
         return true, WR_elt_create(W, S);   
      end if;
   end if;
   return false, "Illegal coercion.";
end intrinsic;

intrinsic '.'(W::RngWitt,i::RngIntElt) -> RngWittElt
   {The ith noncentral basis element.}
   F := BaseRing(W); 
   require Degree(F) gt 1 and i eq 1: "Illegal index.";
   x := F.1;
   p := Characteristic(F);
   n := Length(W);
   return -W ! [ x^(p^i) : i in [0..n-1] ];
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                           Printing                             //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic Print(W::RngWitt, level::MonStgElt)
   {}
   printf "Witt ring of length %o over %o", Length(W), BaseRing(W);
end intrinsic;

intrinsic Print(x::RngWittElt, level::MonStgElt)
   {}
   printf "%o", Vector(x`Element);
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    Membership and Equality                     //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., X::RngWitt) -> BoolElt
   {Returns true if x is in X.}
   if Type(x) eq RngWittElt then
      return x`Parent eq X;
   end if;
   return false;
end intrinsic;

intrinsic Parent(x::RngWittElt) -> RngWitt
   {}
   return x`Parent;
end intrinsic;

intrinsic 'eq' (W::RngWitt,V::RngWitt) -> BoolElt
   {}
   return W`BaseRing eq V`BaseRing and W`Length eq V`Length;  
   return W cmpeq V;
end intrinsic;

intrinsic 'eq' (x::RngWittElt,y::RngWittElt) -> BoolElt
   {}
   return Parent(x) eq Parent(y) and x`Element eq y`Element;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    Attribute Access Functions                  //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic BaseRing(W::RngWitt) -> Rng
   {}
   return W`BaseRing;
end intrinsic;
intrinsic BaseField(W::RngWitt) -> Rng
   {The defining ring of W.}
   return W`BaseRing;
end intrinsic;

intrinsic Length(W::RngWitt) -> Rng
   {The length of the finite Witt ring W.}
   return W`Length;
end intrinsic;

intrinsic Eltseq(x::RngWittElt) -> SeqEnum
   {}
   return x`Element;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    Arithmetic and Functionality                //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic Unity(W::RngWitt) -> RngWittElt 
   {The identity element of R.}
   return W!1;
end intrinsic;

intrinsic Zero(W::RngWitt) -> RngWittElt
   {The zero element of R.}
   return W!0;
end intrinsic;

intrinsic '-' (x::RngWittElt) -> RngWittElt
   {}
   if IsZero(x) then
    return x;
   end if;
   return (Parent(x)!-1)*x;
end intrinsic;

intrinsic '-' (x::RngWittElt,y::RngIntElt) -> RngWittElt
   {}
   if y eq 0 then
    return x;
   end if;
   return x + Parent(x)!-y;
end intrinsic;

intrinsic '-' (x::RngIntElt,y::RngWittElt) -> RngWittElt
   {}
   if x eq 0 then
    return -y;
   end if;
   return Parent(y)!x - y;
end intrinsic;

intrinsic '-' (x::RngWittElt,y::RngWittElt) -> RngWittElt
   {}
   W := Parent(x);
   require W cmpeq Parent(y): "Arguments have different parents.";
   return x + (-y);
end intrinsic;

intrinsic '+' (x::RngWittElt,y::RngIntElt) -> RngWittElt
   {}
   if y eq 0 then
    return x;
   end if; 
   return x + Parent(x)!y;
end intrinsic;

intrinsic '+' (x::RngIntElt,y::RngWittElt) -> RngWittElt
   {}
   if x eq 0 then
    return y;
   end if;
   return Parent(y)!x + y;
end intrinsic;

intrinsic '+' (x::RngWittElt,y::RngWittElt) -> RngWittElt
   {}
   if IsZero(x) then
    return y;
   end if;
   if IsZero(y) then
    return x;
   end if; 
   W := Parent(x);
   require W cmpeq Parent(y): "Arguments have different parents.";
   a := x`Element;
   b := y`Element;
   A := W`CoAddition;
   return WR_elt_create(W, Evaluate(A, a cat b)); 
   return WR_elt_create(W,[ Evaluate(A[i], a cat b) : i in [1..Length(W)] ]); 
end intrinsic;

intrinsic '*' (x::RngWittElt,n::RngIntElt) -> RngWittElt
   {}
   return n*x;
end intrinsic;

intrinsic '*' (n::RngIntElt,x::RngWittElt) -> RngWittElt
   {}
   if IsZero(x) then
    return x;
   end if;
   if n lt 0 then
      return -((-n)*x);
   elif n eq 0 then
      return Parent(x)!0;
   elif n eq 1 then
      return x;
   elif n eq 2 then
      return x + x;
   elif n eq Characteristic(BaseRing(Parent(x))) then
      return FrobeniusImage(VerschiebungImage(x));
   end if;
   b := IntegerToSequence(n,2);
   y := Parent(x)!0;
   for i in [1..#b] do
      y := y + b[i]*x;
      x +:= x; 
   end for;
   return y;
end intrinsic;

intrinsic '*' (x::RngWittElt,y::RngWittElt) -> RngWittElt
   {}
   if IsZero(x) then
    return x;
   end if;
   if IsZero(y) then
    return y;
   end if;
   W := Parent(x);
   require W cmpeq Parent(y): "Arguments have different parents.";
   a := x`Element;
   b := y`Element;
   M := W`CoMultiplication;
   return WR_elt_create(W, Evaluate(M, a cat b)); 
   return WR_elt_create(W, [ Evaluate(M[i], a cat b) : i in [1..Length(W)] ]); 
end intrinsic;

intrinsic '^' (x::RngWittElt,n::RngIntElt) -> RngWittElt
   {}
   if IsZero(x) or IsOne(x) then
    return x;
   end if;
   if IsMinusOne(x) then
    if n mod 2 eq 0 then
	return Parent(x)!1;
    else
	return x;
    end if;
   end if;
   require n ge 0: "Argument 2 must be positive.";
   if n eq 0 then 
      return Parent(x)!1;
   elif n eq 1 then 
      return x;
   elif n eq 2 then
      return x*x;
   end if;
   b := IntegerToSequence(n,2);
   y := x^b[1]; 
   for i in [2..#b] do 
      x := x^2;  
      if b[i] eq 1 then
         y := x*y;
      end if;
   end for;
   return y;
end intrinsic;

////////////////////////////////////////////////////////////////////
//								  //
//				Predicates			  //
//								  //
////////////////////////////////////////////////////////////////////

intrinsic IsZero(x::RngWittElt) -> BoolElt
{Return whether the Witt vector x is the zero vector};
    return &and[IsZero(e) : e in x`Element];
end intrinsic;

intrinsic IsOne(x::RngWittElt) -> BoolElt
{Return whether the Witt vector x is the one vector of its parent space};
    return IsOne(x`Element[1]) and &and[IsOne(e) : e in x`Element[2 .. #x`Element]];
end intrinsic;

intrinsic IsMinusOne(x::RngWittElt) -> BoolElt
{Return whether the Witt vector x is the negative of the one vector of its parent space};
    if Characteristic(BaseRing(Parent(x))) eq 2 then
	return &and[IsOne(e) : e in x`Element];
    else
	return IsMinusOne(x`Element[1]) and &and[IsOne(e) : e in x`Element[2 .. #x`Element]];
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                            Morphisms                           //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic FrobeniusMap(W::RngWitt) -> Map
   {}
   p := Characteristic(W`BaseRing);
   return hom< W -> W | x :-> [ c^p : c in Eltseq(x) ] >;
end intrinsic;

intrinsic FrobeniusImage(e::RngWittElt) -> RngWittElt
   {}
   W := Parent(e);
   p := Characteristic(W`BaseRing);
   return W![ c^p : c in Eltseq(e) ];
end intrinsic;


intrinsic VerschiebungMap(W::RngWitt) -> Map
   {}
   n := Length(W);
   F := hom< W -> W | x :-> 
           [ 0 ] cat [ c[i] : i in [1..n-1] ] where c := Eltseq(x) >;
   return F;
end intrinsic;

intrinsic VerschiebungImage(e::RngWittElt) -> RngWittElt
   {}
   W := Parent(e);  
   n := Length(W);
   return W!([ 0 ] cat [ c[i] : i in [1..n-1] ] where c := Eltseq(e)); 
end intrinsic;

intrinsic Random(W::RngWitt) -> RngWittElt
{}
  k := BaseRing(W);
  require IsFinite(k):
    "W must be definied over a finite ring";
  return W![Random(k) : x in [1..Length(W)]];
end intrinsic

intrinsic Random(W::RngWitt, i::RngIntElt) -> RngWittElt
{}
  k := BaseRing(W);
  return W![Random(k, i) : x in [1..Length(W)]];
end intrinsic;

///////////
// connections with local rings:
// We should have W(GF(p), n) = pAdicRing(p, n)
// with the Teichmueller system...
//

intrinsic TeichmuellerSystem(R::Rng) -> []
{A multiplicative closed system of representatives for the residue class field}
  require Type(R) in {RngPad, RngPadRes, RngPadResExt, RngSerExt, RngSerPow, RngLocA} : "Argument 1 must be a local ring";
  require IsFinite(Precision(R)) : 
    "Argument 1 must be a finite precision local ring";
  Fp := ResidueClassField(R);
  n := Characteristic(Fp)^Precision(R);
  repeat
    S := [(R!x)^n : x in Fp];
    n := n*n;;
    until true or forall{x : x in S | x^p in S where p := Characteristic(Fp)};
  return S;
end intrinsic;

intrinsic LocalRing(W::RngWitt) -> RngPad, Map
{The local ring isomorphic to the Witt ring}
  if assigned W`LocalRingMap then
    return Domain(W`LocalRingMap), W`LocalRingMap;
  end if;
  Fq := BaseRing(W);
  p := Characteristic(Fq);
  require Type(BaseRing(W)) eq FldFin :
      "Witt ring must be defined over a finite field";
  n := Length(W);
  R := UnramifiedQuotientRing(Fq, n);
  FFq := ResidueClassField(R);
  assert Fq eq FFq;
//  Embed(Fq, FFq);
  q := #FFq;
  f := Degree(FFq);
  
//  S := TeichmuellerSystem(R); 
//  replace by TeichmuellerRepresentative that can be computed on demand
//  maybe use the multiplicative structure to make it fast?
  n := Characteristic(Fq)^Length(W);

  W_to_R := function(e)
    e := Eltseq(e);
    return &+ [ (R!((FFq!e[i+1])^(p^((f-i) mod q))))^n*p^i : i in [0..#e-1]];
  end function;  

  W`LocalRingMap := hom<W->R | x :-> W_to_R(x)>;

  return R,W`LocalRingMap;
end intrinsic;

intrinsic ArtinSchreierMap(W::RngWitt) -> Map
{The map: x -> Frobenius(x) - x.}
  p := Characteristic(BaseRing(W));
  F := FrobeniusMap(W);
  return hom<W -> W | x :-> F(x) - x>;
end intrinsic;

intrinsic ArtinSchreierImage(e::RngWittElt) -> RngWittElt
{FrobeniusImage(e) - e.}
  return FrobeniusImage(e) - e;
end intrinsic;

