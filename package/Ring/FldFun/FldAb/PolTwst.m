freeze;
/* <example>
 k := GF(4);
 K := FunctionField(k);
 x := Numerator(K.1);
 AssignNames(~K, ["x"]);
 R := TwistedPolynomials(K);
 p := x^2 + x + k.1^2;

 CarlitzModule(R, p);
 P := Polynomial($1);
 Q, mQ := quo<Parent(P)|P>;
// q, mq := RayResidueRing(Places(K, 2)[1]);
 q, mq := quo<Parent(p)|p>;

 // we should have:
 // Evaluate(P, Q!Polynomial(CarlitzModule(R, f))) eq 0 where
 //    f is any polynomial in x:
 for i in q do 
   <i, CarlitzModule(R, i@@mq), 
     Evaluate(P, Q!Polynomial(CarlitzModule(R,i@@mq)))>; 
 end for;

 p := p^2;
 



   </example>
*/
////////////////////////////////////////////////////////////////////
//                                                                //  
//                           Claus Fieker                         //
//                                                                // 
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
//                                                                //
//                     Attribute declarations                     //
//                                                                // 
////////////////////////////////////////////////////////////////////

declare type RngUPolTwst[RngUPolTwstElt];

declare attributes RngUPolTwst:
   BaseRing,
   PolRing,  
   q;

declare attributes RngUPolTwstElt:
   Parent,
   Element;

////////////////////////////////////////////////////////////////////
//                                                                // 
//                       Creation functions                       // 
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic TwistedPolynomials(F::Rng:q := false) -> RngUPolTwst
   {The ring of twisted polynomials over F.}
   W := New(RngUPolTwst);
   W`BaseRing := F;
   W`PolRing := PolynomialRing(F);
   if q cmpeq false then
     W`q := Characteristic(F);
   else 
     W`q := q;
   end if;
   AssignNames(~W`PolRing, ["T_" cat IntegerToString(W`q)]);
   return W;  
end intrinsic;

intrinsic AssignNames(~F :: RngUPolTwst, S::[MonStgElt])
  {}
  AssignNames(~F`PolRing, S);
end intrinsic;

intrinsic Name(F::RngUPolTwst, i::RngIntElt) -> RngUPolTwstElt
  {The i-th name.}
  require i eq 1: "Argument must be 1";
  return F![0,1];
end intrinsic;



////////////////////////////////////////////////////////////////////
//                                                                //
//                         Coercions                              //
//                                                                // 
////////////////////////////////////////////////////////////////////

intrinsic IsCoercible(W::RngUPolTwst,S::.) -> BoolElt, RngUPolTwstElt
   {}
   if Type(S) eq RngUPolTwstElt then
      if Parent(S) eq W then return true, S; end if;
   elif Type(S) eq RngIntElt then
      p := Characteristic(BaseRing(W));
         R := W`PolRing; 
         x := New(RngUPolTwstElt);
         x`Parent := W;
         x`Element := R!S;
         return true, x;   
   elif Type(Parent(S)) eq Type(W`BaseRing) then
       R := W`PolRing; 
       x := New(RngUPolTwstElt);
       x`Parent := W;
       x`Element := R!S;
       return true, x;   
   elif Type(S) eq SeqEnum  or Type(S) eq RngUPolElt then
     f, y := IsCoercible(W`PolRing, S);
     if f then
       x := New(RngUPolTwstElt);
       x`Parent := W;
       x`Element := y;
       return true, x;
     end if;
   elif Type(S) eq FldFunRatUElt then
     if Denominator(S) eq 1 then
       return true, W!Numerator(S);
     end if;
   end if;
   return false, "Illegal coercion.";
end intrinsic;

intrinsic '.'(W::RngUPolTwst,i::RngIntElt) -> RngUPolTwstElt
   {}
   require i eq 1: "Illegal index.";
   return W!W`PolRing.1;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                           Printing                             //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic Print(W::RngUPolTwst, level::MonStgElt)
   {}
   printf "Ring of twisted polynomial rings over %o\n", W`BaseRing;
end intrinsic;

intrinsic Print(x::RngUPolTwstElt, level::MonStgElt)
   {}
   printf "%o", x`Element;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    Membership and Equality                     //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., X::RngUPolTwst) -> BoolElt
   {Returns true if x is in X.}
   if Type(x) eq RngUPolTwstElt then
      return x`Parent eq X;
   end if;
   return false;
end intrinsic;

intrinsic Parent(x::RngUPolTwstElt) -> RngUPolTwst
   {}
   return x`Parent;
end intrinsic;

intrinsic 'eq' (W::RngUPolTwst,V::RngUPolTwst) -> BoolElt
   {}
   return W`PolRing eq V`PolRing;
end intrinsic;

intrinsic 'eq' (x::RngUPolTwstElt,y::RngUPolTwstElt) -> BoolElt
   {}
   return Parent(x) eq Parent(y) and x`Element eq y`Element;
end intrinsic;

intrinsic IsZero(x::RngUPolTwstElt) -> BoolElt
  {}
  return IsZero(x`Element);
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    Attribute Access Functions                  //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic BaseRing(W::RngUPolTwst) -> Rng
   {}
   return CoefficientRing(W`PolRing);
end intrinsic;
intrinsic BaseRing(x::RngUPolTwstElt) -> Rng
   {}
   return CoefficientRing(x`Element);
end intrinsic;

intrinsic Eltseq(x::RngUPolTwstElt) -> SeqEnum
   {}
   return Eltseq(x`Element);
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    Arithmetic and Functionality                //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic Unity(W::RngUPolTwst) -> RngUPolTwstElt 
   {The identity element of R.}
   return W!1;
end intrinsic;

intrinsic Zero(W::RngUPolTwst) -> RngUPolTwstElt
   {The zero element of R.}
   return W!0;
end intrinsic;

intrinsic '-' (x::RngUPolTwstElt) -> RngUPolTwstElt
   {}
   return (Parent(x)!-1)*x;
end intrinsic;

intrinsic '-' (x::RngUPolTwstElt,y::RngIntElt) -> RngUPolTwstElt
   {}
   return x + Parent(x)!-y;
end intrinsic;

intrinsic '-' (x::RngIntElt,y::RngUPolTwstElt) -> RngUPolTwstElt
   {}
   return Parent(y)!x - y;
end intrinsic;

intrinsic '-' (x::RngUPolTwstElt,y::RngUPolTwstElt) -> RngUPolTwstElt
   {}
   W := Parent(x);
   require W cmpeq Parent(y): "Arguments have different parents.";
   return x + (-y);
end intrinsic;

intrinsic '+' (x::RngUPolTwstElt,y::RngIntElt) -> RngUPolTwstElt
   {}
   return x + Parent(x)!y;
end intrinsic;

intrinsic '+' (x::RngIntElt,y::RngUPolTwstElt) -> RngUPolTwstElt
   {}
   return Parent(y)!x + y;
end intrinsic;

intrinsic '+' (x::RngUPolTwstElt,y::RngUPolTwstElt) -> RngUPolTwstElt
   {}
   W := Parent(x);
   require W cmpeq Parent(y): "Arguments have different parents.";
   a := x`Element;
   b := y`Element;
   A := a+b;
   return W!A;
end intrinsic;

intrinsic '*' (x::RngUPolTwstElt,y::RngUPolTwstElt) -> RngUPolTwstElt
   {}
   W := Parent(x);
   require W cmpeq Parent(y): "Arguments have different parents.";
   a := Eltseq(x`Element);
   b := Eltseq(y`Element);
   q := W`q;
//   M := [ &+ [W`BaseRing| a[i]*b[j]^q^(i-1) : i in [1..#a], j in [1..#b] 
//                                   | i+j-1 eq k ] : k in [1..#a+#b-1]];
   M := 0;
   T := (W.1)`Element;
   for i in [1..#a] do
     for j in [1..#b] do
       M +:= a[i]*b[j]^q^(i-1) * T^(i-1+j-1);
     end for;
   end for;
       
   return W!M;
end intrinsic;

intrinsic '^' (x::RngUPolTwstElt,n::RngIntElt) -> RngUPolTwstElt
   {}
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

intrinsic LeadingCoefficient(a::RngUPolTwstElt) -> RngElt
  {}
  return LeadingCoefficient(a`Element);
end intrinsic;

intrinsic ConstantCoefficient(a::RngUPolTwstElt) -> RngElt
  {}
  return ConstantCoefficient(a`Element);
end intrinsic;

intrinsic Degree(a::RngUPolTwstElt) -> RngIntElt
  {}
  return Degree(a`Element);
end intrinsic;

intrinsic Quotrem(a::RngUPolTwstElt, b::RngUPolTwstElt) -> RngUPolTwstElt, RngUPolTwstElt
  {The right divison: a = q*b+r.}
  
  bl := LeadingCoefficient(b);  
  W := Parent(a);
  require Parent(a) eq W: "Polynomials must be from the same ring";
  require bl eq 1 or IsField(CoefficientRing(W)) : "Polynomial ring must be over a field";
  T := W.1;
  q := W`q;

  m := Degree(a);
  n := Degree(b);
  if n gt m then
    return W!0, a;
  end if;

  Q := [];
  for i := m to n by -1 do
    if a eq W!0 or Degree(a) lt i then
      c := 0;
    else
      d := Degree(a);
      c := LeadingCoefficient(a) / bl^q^(i-n);
      if IsWeaklyZero(c) then
        c := 0;
      end if;
      a := a - (W!c)*T^(i-n) * b;
      if IsZero(a) or IsWeaklyZero(LeadingCoefficient(a)) then
        a := Parent(a)!Eltseq(a)[1..Degree(a)];
      end if;
      assert(Degree(a)) lt d;
    end if;
    Append(~Q, c);
  end for;

  return W!Reverse(Q), a;
end intrinsic;

intrinsic GCD(a::RngUPolTwstElt, b::RngUPolTwstElt) -> RngUPolTwstElt
  {A right gcd g: a = x * g and b = y*g.}
  
  W := Parent(a);
  require Parent(b) eq W : "Polynomials must be from the same ring";
  repeat
    _,c := Quotrem(a,b);
    a := b;
    b := c;
  until c eq W!0 or Degree(c) eq 0 and IsWeaklyZero(LeadingCoefficient(c));
  a`Element := Normalize(a`Element);
  return a;
end intrinsic;

intrinsic Random(W::RngUPolTwst, i::RngIntElt) -> RngUPolTwstElt
{}
  k := BaseRing(W);
  return W![Random(k) : x in [1..i]];
end intrinsic;

intrinsic CarlitzModule(W::RngUPolTwst, e:: FldFunRatUElt) -> RngUPolTwstElt
  {}
  require Denominator(e) eq 1:
    "2nd argument must be integral!";

  if Denominator(e) eq 1 then
    return CarlitzModule(W, Numerator(e));
  end if;
end intrinsic;

intrinsic CarlitzModule(W::RngUPolTwst, e:: RngUPolElt) -> RngUPolTwstElt
  {}
  x := Eltseq(e);
  i := (W!W`BaseRing.1) + W.1;
  s := W!0;
  for a in Reverse(x) do
    s := i*s + W![a];
  end for;
  return s;
end intrinsic;

intrinsic Polynomial(e::RngUPolTwstElt) -> RngUPolElt
  {}
  W := e`Parent;
  x := Eltseq(e`Element);
  x := &+ [W`PolRing| W`PolRing.1^(W`q^(i-1))*x[i] : i in [1..#x]];
  return x;
end intrinsic;

intrinsic SpecialEvaluate(f::RngUPolElt, a::.) -> .
  {Horner's scheme for sparse polynomials}
  x := Eltseq(f);
  x := Reverse(x);
  v := x[1];
  i := 2;
  while i le #x do
    j := i+1;
    while j le #x and IsWeaklyZero(x[j]) do
      j +:= 1;
    end while;
    v *:= a^(j-i+1);
    if j le #x then
      v +:= x[j];
    end if;
    i := j+1;
  end while;
  return v;
end intrinsic;
    
intrinsic SpecialEvaluate(f::RngUPolTwstElt, a::RngElt) -> RngElt
  {Evalute(Polynomial(f), a)...}

  // should be done better...

  return &+ Eltseq(f*Parent(f)!a);
end intrinsic;
