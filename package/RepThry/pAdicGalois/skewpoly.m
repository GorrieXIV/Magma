
freeze;

/*
This package provides basic tools for computing with skew polynomials over finite fields.
*/

declare type SkwPolRng [SkwPolRngElt];
declare attributes SkwPolRng: BaseRing, Variable, VarName, Frobenius;

declare type SkwPolRngElt;
declare attributes SkwPolRngElt: Coefficients, Parent;

declare attributes RngUPol: IsCentreOf;

/*
Creation functions
*/


intrinsic '.'(R::SkwPolRng,n::RngIntElt) -> SkwPolRngElt
  {Return the generator of a skew polynomial ring}
  require n eq 1: "Generators start at 1";
  return R`Variable;
end intrinsic;

intrinsic Centre(R::SkwPolRng) -> RngUPol
  {Return the centre of a skew polynomial ring}
  k:=R`BaseRing;
  p:=Characteristic(k);
  r:=R`Frobenius;
  d:=Degree(k);
  k0:=GF(p,GCD(d,r));
  A:=PolynomialRing(k0);
  A`IsCentreOf:=R;
  return A;
end intrinsic;

intrinsic 'eq'(R::SkwPolRng,S::SkwPolRng) -> BoolElt
  {Equality test between skew polynomial rings}
  return R`BaseRing eq S`BaseRing and R`Frobenius eq S`Frobenius;
end intrinsic;

intrinsic IsCoercible(R::SkwPolRng, P::SkwPolRngElt) -> BoolElt
  {Test if a skew polynomial P lies in a given skew polynomial ring R}
  if P`Parent ne R then return false,"Illegal coercion";
  else return true,P;
  end if;
end intrinsic;

intrinsic IsCoercible(R::SkwPolRng,a::RngIntElt) -> BoolElt
  {Coerces an integer into a skew polynomial ring}
  return true, R![a];
end intrinsic;

intrinsic IsCoercible(R::SkwPolRng, a::FldFinElt) -> BoolElt
  {Test if an element of a finite field is coerible in a ring of skew polynomials}
  b,m:=IsCoercible(R`BaseRing,a);
  if b then return true, R![m];
    else return false, "Illegal coercion";
  end if;
end intrinsic;

intrinsic IsCoercible(R::SkwPolRng, f::RngUPolElt) -> BoolElt
  {Test if a commutative polynomial can be mapped into a ring of skew polynomials}
  C:=Centre(R);
  b,e:=IsCoercible(C,f);
  require b: "Polynomial must be coercible into the center of the skew polynomial ring";
  E:=Eltseq(e);
  k:=R`BaseRing;
  d:=Degree(k) div Degree(CoefficientRing(C));
  Cf:=[];
  if E eq [] then
    return true,R![0];
  end if;
  for i in [1..#E - 1] do
    Append(~Cf,E[i]);
    for j in [1..d-1] do
      Append(~Cf,0);
    end for;
  end for;
  Append(~Cf,E[#E]);
  Rf:=R!Cf;
  return true, Rf;
end intrinsic;

intrinsic IsCoercible(R::SkwPolRng,E::SeqEnum) -> BoolElt, .
  {Test if a sequence is coercible into a skew polynomial ring}
  if &and[IsCoercible(R`BaseRing, E[i]) : i in [1..#E]] then
    x :=New(SkwPolRngElt);
    x`Parent:=R;
    xC := E;
    while xC ne [] and xC[#xC] eq 0 do
      Prune(~xC);
    end while;
    x`Coefficients:= [(R`BaseRing)!xC[i] : i in [1..#xC]];
    return true, x;
  else
    return false, "Illegal coercion";
  end if;
end intrinsic;

intrinsic 'in'(x::SkwPolRngElt,R::SkwPolRng) -> BoolElt
  {Test if a skew polynomial lies in a skew polynomial ring}
  if IsCoercible(R,x) then
    return true;
  end if;
end intrinsic;

intrinsic SkewPolynomialRing(k::FldFin,Fr::RngIntElt) -> SkwPolRng
  {Create the skew polynomial ring k[var,F^r]}
  X:=New(SkwPolRng);
  X`BaseRing:=k;
  X`Frobenius:=Fr;
  X`Variable:=X![k|0,1];
  return X;
end intrinsic;

intrinsic Print(R::SkwPolRng)
  {Print the skew polynomial ring R}
  printf "Skew Polynomial Ring over %o with Frob^%o",R`BaseRing,R`Frobenius;
end intrinsic;

intrinsic AssignNames(~R::SkwPolRng,S::[MonStgElt])
{Assign the name of the variable for a skew polynomial ring}
 require #S eq 1: "Only one variable for skew polynomial rings";
 R`VarName:=S[1];
end intrinsic;

intrinsic Name(R::SkwPolRng,i::RngIntElt) -> SkwPolRngElt
{Return the name of the variable}
 require i eq 1: "Only one variable for skew polynomial rings";
 return R.1;
end intrinsic;

intrinsic Print(f::SkwPolRngElt)
{Print a skew polynomial element}
 A:=f`Coefficients; b:=false;
 if assigned Parent(f)`VarName then var:=Parent(f)`VarName;
 else var:="$.1"; end if; // should get name of ring -- don't know how!
 if A eq [] then print "0"; end if;
 for i in [1..#A] do c:=A[i]; if c eq 0 then continue; end if;
  if not b then b:=true; else printf " + "; end if; d:=i-1;
  if d eq 0 or c ne 1 then printf "%o",c; end if;
  if d gt 0 and c ne 1 then printf "*"; end if;
  if d gt 0 then printf "%o",var; end if;
  if d gt 1 then printf "^%o",d; end if; end for;
end intrinsic; 

intrinsic Parent(f::SkwPolRngElt) -> SkwPolRng
  {Return the parent of a skew polynomial}
  return f`Parent;
end intrinsic;

intrinsic 'eq'(f::SkwPolRngElt,g::SkwPolRngElt) -> BoolElt
  {Test equality in a skew polynomial ring}
  return (f`Coefficients eq g`Coefficients) and (f`Parent eq g`Parent);
end intrinsic;

intrinsic Eltseq(f::SkwPolRngElt) -> SeqEnum
  {Convert an element of a skew polynomial ring into a sequence}
  return f`Coefficients;
end intrinsic;

/*
Basic attributes
*/

intrinsic Degree(f::SkwPolRngElt) -> RngInt
  {Return the degree of f}
  d := #(f`Coefficients);
  if d eq 0 then
    return -1;
  end if;
  while (d ge 1) and (f`Coefficients[d] eq 0) do
    d := d - 1;
    Prune(~f`Coefficients);
  end while;
  return d-1;
end intrinsic;

intrinsic LeadingCoefficient(f::SkwPolRngElt) -> FldFinElt
  {Return the leading coefficient of a skew polynomial}
  E:=f`Coefficients;
  d:= #E;
  while (E[d] eq 0) and (d ge 0) do
     d:=d-1;
  end while;
  if d ne -1 then return E[d];
  end if;
end intrinsic

intrinsic Coefficient(P::SkwPolRngElt,i::RngIntElt) -> FldFinElt
  {Returns the i-th coefficient of a skew polynomial}
  require i ge 0: "Only nonnegative coefficients";
  E:=P`Coefficients;
  k:=(P`Parent)`BaseRing;
  if i ge #E then
    return  k!0;
  else
    return E[i+1];
  end if;
end intrinsic;

intrinsic Coefficients(P::SkwPolRngElt) -> SeqEnum
  {Returns the list of coefficients of a skew polynomial}
  return P`Coefficients;
end intrinsic;

intrinsic '+'(f::SkwPolRngElt, g::RngElt) -> SkwPolRngElt
  {Addition operator}
  b,e:=IsCoercible(Parent(f)`BaseRing,g);
  require b: "Ring element must coerce into base field of skew polynomial";
  b,e:=IsCoercible(Parent(f),[e]); assert b;
  return f+e;
end intrinsic;

intrinsic '+'(f::RngElt, g::SkwPolRngElt) -> SkwPolRngElt
  {Addition operator}
  b,e:=IsCoercible(Parent(g)`BaseRing,f);
  require b: "Ring element must coerce into base field of skew polynomial";
  b,e:=IsCoercible(Parent(g),[e]); assert b;
  return e+g;
end intrinsic;

intrinsic '+'(P::SkwPolRngElt, Q::SkwPolRngElt) -> SkwPolRngElt
  {Addition operator}
  CP:=P`Coefficients;
  CQ:=Q`Coefficients;
  CS:= [];
  if #CP lt #CQ then
    for i in [1..#CP] do
      Append(~CS, CP[i] + CQ[i]);
    end for;
    for i in [#CP+1..#CQ] do
      Append(~CS, CQ[i]);
    end for;
  else
    for i in [1..#CQ] do
      Append(~CS, CP[i] + CQ[i]);
    end for;
    for i in [#CQ+1..#CP] do
      Append(~CS, CP[i]);
    end for;
  end if;    
  return (P`Parent)!CS;
end intrinsic;

intrinsic '-'(f::SkwPolRngElt) -> SkwPolRngElt
  {Negative operator}
  return f`Parent!0-f;
end intrinsic;

intrinsic '-'(f::SkwPolRngElt, g::RngElt) -> SkwPolRngElt
  {Substraction operator}
  b,e:=IsCoercible(Parent(f)`BaseRing,g);
  require b: "Ring element must coerce into base field of skew polynomial";
  b,e:=IsCoercible(Parent(f),[e]); assert b;
  return f-e;
end intrinsic;

intrinsic '-'(P::SkwPolRngElt, Q::SkwPolRngElt) -> SkwPolRngElt
  {Substraction operator}
  CP:=P`Coefficients;
  CQ:=Q`Coefficients;
  CS:= [];
  if #CP ge #CQ then
    for i in [1..#CQ] do
      Append(~CS, CP[i] - CQ[i]);
    end for;
    for i in [#CQ + 1 .. #CP] do
      Append(~CS,CP[i]);
    end for;
  else
    for i in [1..#CP] do
      Append(~CS, CP[i] - CQ[i]);
    end for;
    for i in [#CP + 1 .. #CQ] do
      Append(~CS,-CQ[i]);
    end for;
  end if;
  d:=Maximum(#CP,#CQ);
  while (d ge 1) and (CS[d] eq 0) do
    Prune(~CS);
    d := d-1;
  end while;
  return (P`Parent)!CS;
end intrinsic;

intrinsic '*'(f::SkwPolRngElt, g::RngElt) -> SkwPolRngElt
  {Multiplication operator}
  b,e:=IsCoercible(Parent(f)`BaseRing,g);
  require b: "Ring element must coerce into base field of skew polynomial";
  b,e:=IsCoercible(Parent(f),[e]); assert b;
  return f*e;
end intrinsic;

intrinsic '*'(f::RngElt, g::SkwPolRngElt) -> SkwPolRngElt
  {Multiplication operator}
  b,e:=IsCoercible(Parent(g)`BaseRing,f);
  require b: "Ring element must coerce into base field of skew polynomial";
  b,e:=IsCoercible(Parent(g),[e]); assert b;
  return e*g;
end intrinsic;

intrinsic '*'(P::SkwPolRngElt, Q::SkwPolRngElt) -> SkwPolRngElt
  {Multiplication operator}
  R:=P`Parent;
  if (Q eq R!0 or P eq R!0) then return P`Parent!0;
  end if;
  r:=(P`Parent)`Frobenius;
  CP:=P`Coefficients;
  CQ:=Q`Coefficients;
  dP:=#CP;
  dQ:=#CQ;
  for i in [1.. dP + dQ] do
      Append(~CP,0);
      Append(~CQ,0);
  end for;
  CS:= [];
  for i in [1..(dQ+dP - 1)] do
    Append(~CS, &+[CP[j]*Frobenius(CQ[i - j +1],r*(j-1)) : j in [1..i]]);
  end for;
  return (P`Parent)!CS; 
end intrinsic;

intrinsic '^'(f::SkwPolRngElt,n::RngIntElt) -> SkwPolRngElt
 {Exponentiation operator}
 require n ge 0: "Exponent must be nonnegative";
 if n eq 1 then return f; end if; if n eq 0 then return Parent(f)![1]; end if;
 // stupid, for now
 g:=f; for i in [2..n] do g:=g*f; end for; return g; end intrinsic;

/*
Arithmetics in skew polynomial rings
*/


intrinsic RQuotrem(P::SkwPolRngElt, Q::SkwPolRngElt) -> SkwPolRngElt,SkwPolRngElt
  {Return the quotient and remainder of the right Euclidean division of skew polynomials}
  R:=Q`Parent;
  require Q ne R!0: "Division by 0";
  s:=R`Frobenius;
  CP:=P`Coefficients;
  CQ:=Q`Coefficients;
  dP:=Degree(P);
  dQ:=Degree(Q);
  tt:=LeadingCoefficient(Q);
  CT:=[];
  while dQ le dP do
    c:=CP[dP+1]/Frobenius(tt,s*(dP - dQ));
    Append(~CT,c);
    for i in [0..dQ] do
      CP[dP - i  + 1] := CP[dP - i +1] - c*Frobenius(CQ[dQ -i +1],s*(dP - 
dQ));
    end for;
    Prune(~CP);      
    dP := dP - 1;
  end while; 
  T:=(P`Parent)!Reverse(CT);
  R:=(P`Parent)!CP;
  return T,R;  
end intrinsic;    

intrinsic 'div'(P::SkwPolRngElt, Q::SkwPolRngElt) -> SkwPolRngElt
  {Compute the quotient of the right-division of two skew polynomials}
  T,R:=RQuotrem(P,Q);
  return T;
end intrinsic;

  
intrinsic 'mod'(P::SkwPolRngElt, Q::SkwPolRngElt) -> SkwPolRngElt
  {Compute the remainder of the right-division of two skew polynomials}
  T,R:=RQuotrem(P,Q);
  return R;  
end intrinsic;

intrinsic ExtendedRGCD(P::SkwPolRngElt,Q::SkwPolRngElt) -> SkwPolRngElt, SkwPolRngElt, SkwPolRngElt
  {Compute the extended right gcd of two skew polynomials}
  Ring:=P`Parent;
  A:=P;
  B:=Q;
  U:=Ring!0;
  V:=Ring!1;
  U1:= Ring!1;
  V1 := Ring!0;
  T,R :=RQuotrem(P,Q);
  while Degree(R) ge 0 do
    A:=B;
    B:=R;
    U2:= U-T*U1;
    V2:=V-T*V1;
    U := U1;
    V := V1;
    U1:=U2;
    V1:=V2;
    T,R:=RQuotrem(A,B);
  end while;
  b:=LeadingCoefficient(B)^(-1);
  return b*B,b*V1,b*U1;
end intrinsic;

intrinsic LLCM(P::SkwPolRngElt,Q::SkwPolRngElt) -> SkwPolRngElt, SkwPolRngElt, SkwPolRngElt
  {Compute the left lcm of two skew polynomials}
  Ring:=P`Parent;
  A:=P;
  B:=Q;
  U:=Ring!0;
  V:=Ring!1;
  U1:= Ring!1;
  V1 := Ring!0;
  T,R := RQuotrem(P,Q);
  while Degree(R) ge 0 do
    A:=B;
    B:=R;
    U2:= U-T*U1;
    V2:=V-T*V1;
    U := U1;
    V := V1;
    U1:=U2;
    V1:=V2;
    T,R:=RQuotrem(A,B);
  end while;
  U1:=U - T*U1;
  L:=U1*Q;
  return LeadingCoefficient(L)^(-1)*L;
end intrinsic;

intrinsic RGCD(P::SkwPolRngElt,Q::SkwPolRngElt) -> SkwPolRngElt
  {Compute the right gcd of two skew polynomials}
  R:=P`Parent;
  if P eq R!0 then return Q; end if;
  if Q eq R!0 then return P; end if;
  A:=P;
  B:=Q;
  T,R:=RQuotrem(P,Q);
  while Degree(R) ge 0 do
    A:=B;
    B:=R;
    Q,R:=RQuotrem(A,B);
  end while;
  return LeadingCoefficient(B)^(-1)*B;
end intrinsic;

/*
Irrreductibility tests
*/

intrinsic Norm(P::SkwPolRngElt) -> RngElt
  {Return the norm of a skew polynomial}
  C:=Centre(P`Parent);
  k:=(P`Parent)`BaseRing;
  list:=P`Coefficients;
  d:=#list;
  while (d ge 1) and (list[d] eq 0) do
    d:=d-1;
    Prune(~list);
  end while;
  if list eq [] then
    return C!0;
  end if;
  if #list eq 1 then
    return Norm(list[1]);
  else
    M:=ZeroMatrix(k,d-1,d-1);
    for i in [1..d-2] do
      M[i+1,i]:=1;
      M[i+1,d-1]:=-list[i+1]/list[d];
    end for;
    M[1,d-1]:=-list[1]/list[d];
    s:=Degree(k) div GCD((P`Parent)`Frobenius, Degree(k));
    N:=M;
    for i in [1..s-1] do
      for j in [1..d-1] do
        N[j,d-1] := Frobenius(N[j,d-1],(P`Parent)`Frobenius);
      end for;
      M:=M*N;
    end for;
    return C!(Norm(list[d])*CharacteristicPolynomial(M));
  end if;
end intrinsic;

intrinsic IsSimilar(P::SkwPolRngElt,Q::SkwPolRngElt) -> BoolElt
  {Test if two skew polynomials are similar}
  k:=(P`Parent)`BaseRing;
  listP:=P`Coefficients;
  listQ:=Q`Coefficients;
  d:=#listP;
  while (d ge 1) and (listP[d] eq 0) do
    d:=d-1;
    Prune(~listP);
  end while;
  if d ne #listQ then return false;
  end if;
  MP:=ZeroMatrix(k,d-1,d-1);
  for i in [1..d-2] do
    MP[i+1,i]:=1;
    MP[i+1,d-1]:=-listP[i+1]/listP[d];
  end for;
  MP[1,d-1]:=-listP[1]/listP[d];
  MQ:=ZeroMatrix(k,d-1,d-1);
  for i in [1..d-2] do
    MQ[i+1,i]:=1;
    MQ[i+1,d-1]:=-listQ[i+1]/listQ[d];
  end for;
  MQ[1,d-1]:=-listQ[1]/listQ[d];
  s:=Degree(k) div GCD((P`Parent)`Frobenius, Degree(k));
  NP:=MP;
  NQ:=MQ;
  for i in [1..s-1] do
    for j in [1..d-1] do
      NP[j,d-1] := Frobenius(NP[j,d-1],(P`Parent)`Frobenius);
      NQ[j,d-1] := Frobenius(NQ[j,d-1],(P`Parent)`Frobenius);     
    end for;
    MP:=MP*NP;
    MQ:=MQ*NQ;
  end for;
  return InvariantFactors(MP) eq InvariantFactors(MQ);
end intrinsic;

intrinsic IsIrreducible(P::SkwPolRngElt) -> BoolElt
  {Test irreducibility for a skew polynomial}
  return IsIrreducible(Norm(P));
end intrinsic;

/*
Factorization
*/


RandomSkewPolynomial:=function(R,d);
  k:=R`BaseRing;
  coeff:=[Random(k) : i in [0..d]];
  P:=New(SkwPolRngElt);
  P`Parent :=R;
  P`Coefficients := coeff;
  return P;
end function;

FindFactorSS:=function(P,N)
  R:=P`Parent;
  k:=R`BaseRing;
  d:=Degree(k);
  deg:=Degree(P);
  r:=GCD(d,R`Frobenius);
  l:=d div r;
  m:=Characteristic(k)^(r*Degree(N));
  CN:=[];
  listN:=Eltseq(N);
  for i in [1..Degree(N)] do
    Append(~CN,listN[i]);
    for j in [1..l-1] do
      Append(~CN,0);
    end for;
  end for;
  Append(~CN,listN[Degree(N)+1]);
  NR:=R!CN;
  S:=RQuotrem(NR,P);
  if Characteristic(k) ne 2 then
    while true do    
      Rand:=RandomSkewPolynomial(R,deg);
      x:=S*Rand mod P;
      t:=R![1];
        exp:=(m-1) div 2;
        while exp ne 0 do
          if exp mod 2 eq 1 then
            t:=x*t mod P;
          end if;
            x:= x*x mod P;
          exp:=exp div 2;
        end while;
        Am:= RGCD(t-R![1],P) ;
        if Degree (Am) eq Degree(N) then
          return Am;
        end if;
        Ap:=RGCD(t+R![1],P);
        if Degree(Ap) eq Degree(N) then
          return Ap;
        end if;
    end while;
  else
    while true do    
      Rand:=RandomSkewPolynomial(R,deg);
      x:=S*Rand mod P;
      t:=R![1];
        exp:=m-1;
        while exp ne 0 do
            x:= x*x mod P;
	    t:= t +x;
          exp:=exp -1;
        end while;
        Am:= RGCD(t,P) ;
        if Degree (Am) eq Degree(N) then
          return Am;
        end if;
        Ap:=RGCD(t+R![1],P);
        if Degree(Ap) eq Degree(N) then
          return Ap;
        end if;
    end while;
  end if;    
end function;

RandomRetraction := function(R)
  k:=R`BaseRing;
  C:=Centre(R);
  k0:=CoefficientRing(C);
  proj:=[Random(k0) : i in [1..Degree(k,k0)]];
  ret:=function(a)
    seq := Eltseq(a,k0);
    return &+[seq[i]*proj[i] : i in [1..Degree(k,k0)]];
  end function;
  return ret;
end function;

FindFactor:=function(P,N)
  R:=P`Parent;
  k:=R`BaseRing;
  d:=Degree(k);
  l:=GCD(d,R`Frobenius);
  r:=d div l;
  e:=Degree(P) div Degree(N);
  if e eq 1 then return P;
  end if;
  m:=Characteristic(k)^(l*Degree(N));
  CN:=[];
  listN:=Eltseq(N);
  if Degree(N) gt 1 then
    E<b>:=ext<CoefficientRing(N)|N>;
  else
    E:=CoefficientRing(N);
    b:= -Coefficient(N,0);
  end if;
  for i in [1..Degree(N)] do
    Append(~CN,listN[i]);
    for j in [1..r-1] do
      Append(~CN,0);
    end for;
  end for;
  Append(~CN,listN[Degree(N)+1]);
  NR:= R!CN;
  S:= RQuotrem(NR,P);
  a:=1;
  while true do
    print "coucou";
    Rand:=RandomSkewPolynomial(R,Degree(N)*e-1);
    while true do
      print "coucou2";
      f:=RandomRetraction(R);
      R0:=(Rand*S) mod R!N;
      R1:=S;
      M:=IdentityMatrix(E,e);
      for v in [1..e] do
        vec:=Matrix(E,e,1, [&+[b^j* f(Coefficient(R1,r*j + i)) : j in [0..Degree(N) - 1]] : i in [0..e-1]]);
        InsertBlock(~M,vec,1,v);
        R1:=(R1*R0) mod R!N;
      end for;
      R1:=R1*R0;
      vec:=Matrix(E,e,1, [&+[b^j*f(Coefficient(R1,r*j + i)) : j in [0..Degree(N) - 1]] : i in [0..e-1]]);
      print M;
      vecsol:= Transpose(Solution(Transpose(M),Transpose(vec)));
      if M* vec ne vecsol then
        f:=RandomRetraction(R);
      end if;
      break;
    end while;
    F:=PolynomialRing(E)!Append(Eltseq(vecsol),-1);
    T:=PolynomialRing(E).1;
    T0:=T;
    delta :=Degree(N)*Degree(CoefficientRing(N));
    roots := Roots(F,E);
    if (roots ne []) and (roots[1][2] eq 1) then
      P0:=S*Rand - R!(Centre(R)!Eltseq(roots[1][1]));
      D:=RGCD(P0,P);
      if Degree(D) eq 0 then continue;
      end if;
    end if;
  end while;
end function;

intrinsic Factorization(P::SkwPolRngElt) -> SeqEnum
  {Return a factorization of (the normalization of) a skew polynomial as a product of monic irreducible polynomials}
  R:=P`Parent;
  k:=R`BaseRing;
  z:=R.1;
  p:=Characteristic(k);
  d:=Degree(k);
  r:=R`Frobenius;
  l:=LCM(r,d) div r;
  Q:=Norm(P);
  fac:=Factorization(Q);
  nb:=#fac;
  listfact:=[];
  for i in [1..nb] do
    list:=Eltseq(fac[i][1]);
    CQi:=[];  
    for i in [1..#list-1] do
      Append(~CQi,list[i]);
      for j in [1..l-1] do
        Append(~CQi,0);
      end for;
    end for;
      Append(~CQi,list[#list]);
    Qi:=R!CQi;
    Pi:=RGCD(Qi,P);
    while Degree(Pi) gt 0 do
      while Degree(Pi) gt Degree(fac[i][1]) do
        T:=FindFactorSS(Pi,fac[i][1]);
        Pi:=RQuotrem(Pi,T);
        P:=RQuotrem(P,T);
        Append(~listfact,T);
      end while;
      Append(~listfact,Pi);
      P:=RQuotrem(P,Pi);
      Pi:=RGCD(Qi,P);
    end while;
  end for;
  return Reverse(listfact);
end intrinsic;

SkewFactorization_list:=function(list,s)
  k:=Parent(list[1]);
  R:=SkewPolynomialRing(k,s);
  P:=R!list;
  a:=LeadingCoefficient(P);
  P:=a^(-1)*P;
  listfac_list:=[];
  listfac:=Factorization(P);
  for i in [1..#listfac] do
    Append(~listfac_list,Eltseq(listfac[i]));
  end for;
  return listfac_list;
end function;

/********************************
    Karatstuba multiplication
********************************/

function KarMul(P,Q)
  dP:=Degree(P);
  dQ:=Degree(Q);
  R:=P`Parent;
  s:=R`Frobenius;
  k:=R`BaseRing;
  a:=Degree(k);
  r:=LCM(a,s) div s;
  if (P eq R!0) or (Q eq R!0) then
    return R!0;
  end if;
  if (dP lt r) or (dQ lt r) then
    return P*Q;
  end if;
  mP:=dP div (2*r) + 1;
  mQ:=dQ div (2*r) + 1;
  m:=Minimum(mP,mQ);
  P0:=R![Coefficient(P,i):i in [0..r*m -1]];
  P1:=R![Coefficient(P,i):i in [r*m..dP ]];
  Q0:=R![Coefficient(Q,i):i in [0..r*m -1]];
  Q1:=R![Coefficient(Q,i):i in [r*m..dQ]];
  R0:=KarMul(P0,Q0);
  R2:=KarMul(P1,Q1);
  R1:=KarMul(P0+P1,Q0+Q1) - R0 - R2;
  list1:=Coefficients(R1);
  list2:=Coefficients(R2);
  Reverse(~list1);
  Reverse(~list2);
  for i in [0..m*r-1] do
    Append(~list1,0);
  end for;
  for i in [0..2*m*r-1] do
    Append(~list2,0);
  end for;
  Reverse(~list1);
  Reverse(~list2);
  return R0 + R!list1 + R!list2;
end function;
