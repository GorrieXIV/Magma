freeze;
 
declare verbose QuarticMinimise,2;

function QuarticLevel(A,p) v4:=QuarticIInvariant(A); v6:=QuarticJInvariant(A);
 assert(v4 ne 0 or v6 ne 0);
 if (v4 eq 0) then return v4,v6,Valuation(v6,p : Check:=false) div 6; end if;
 if (v6 eq 0) then return v4,v6,Valuation(v4,p : Check:=false) div 4; end if;
 return v4,v6,Min(Valuation(v4,p : Check:=false) div 4,
                  Valuation(v6,p : Check:=false) div 6); end function;

function QRev(q)
 return &+[Coefficient(q,t)*Parent(q).1^(4-t): t in [0..4]]; end function;

function QuarticMinimiseOnceAtPrime(q0,p) q:=q0;
 x:=Parent(q).1; M:=DiagonalMatrix([1,1]);
 vv:=[Valuation(Coefficient(q,4-n),p : Check:=false) : n in [0..4]];
 vq:=Min(vv); v4,v6,lev:=QuarticLevel(q,p);
 vprintf QuarticMinimise,2: "v4=%o v6=%o lev=%o\n",v4,v6,lev;
 if (lev eq 0) then return true,DiagonalMatrix([1,1]),q; end if;

 // "Critical case" (where the algorithm would flip endlessly) ==> minimal.
 // (This only occurs for locally insoluble curves).  Added June 2008, SRD.
 if (vv[1] eq 1 and vv[2] ge 2 and vv[3] ge 2 and vv[4] ge 3 and vv[5] eq 3) or
    (vv[1] eq 3 and vv[2] ge 3 and vv[3] ge 2 and vv[4] ge 2 and vv[5] eq 1) then
  assert lev eq 1; return true,DiagonalMatrix([1,1]),q; end if;

 if p eq 3 then
  V4:=Valuation(v4,3); V6:=Valuation(v6,3); VD:=Valuation(4*v4^3-v6^2,3)-3;
  if not ((V4 ge 5 and V6 ge 9) or (V4 eq 4 and V6 eq 6 and VD ge 12))
   then return true,DiagonalMatrix([1,1]),q; end if; end if;
 if (vq ge 2) then return false,DiagonalMatrix([1,1]),q; end if;
 if &and[vv[i] ge (i-1) : i in [2..5]] then
  return false,Matrix([[p,0],[0,1]]),Evaluate(q,p*x); end if;
 if &and[vv[i] ge (5-i) : i in [1..4]] then
  return false,Matrix([[0,1],[p,0]]),Evaluate(QRev(q),p*x); end if;
 if &and[vv[i] ge (2*i-4) : i in [3..5]] then
  return false,Matrix([[p^2,0],[0,1]]),Evaluate(q,p^2*x); end if;
 if &and[vv[i] ge (8-2*i) : i in [1..3]] then
  return false,Matrix([[0,1],[p^2,0]]),Evaluate(QRev(q),p^2*x); end if;

 q1:=q div (p^vq); pf:=PolynomialRing(GF(p))!q1; QUAD:=true;
 if Degree(pf) eq 0 then q:=QRev(q); M:=Matrix([[0,1],[1,0]]); end if;
 if Degree(pf) eq 1 then //triple root at infinity
  s:=Integers()!((-Coefficient(pf,0))/Coefficient(pf,1)); QUAD:=false;
  q:=QRev(Evaluate(q,x+s)); M:=Matrix([[s,1],[1,0]]); end if;
 if Degree(pf) eq 3 then //single root at infinity
  s:=Integers()!Roots(pf)[1][1]; QUAD:=false;
  q:=Evaluate(q,x+s); M:=Matrix([[1,s],[0,1]]); end if;
 if Degree(pf) eq 4 then R:=Roots(pf);
  if #R eq 1 then s:=Integers()!R[1][1];
   q:=Evaluate(q,x+s); M:=Matrix([[1,s],[0,1]]); end if;
  if #R eq 2 then r1:=R[1]; r2:=R[2]; QUAD:=false;
   if r2[2] eq 3 then u:=r2[1]; v:=r1[1]; else u:=r1[1]; v:=r2[1]; end if;
   u:=Integers()!(1/(u-v)); v:=Integers()!v;
   q:=Evaluate(QRev(Evaluate(q,x+v)),x+u); M:=Matrix([[v,u*v+1],[1,u]]);
   end if; end if;
 if (QUAD eq true) then
  if p ne 2 then return false,M*Matrix([[p,0],[0,1]]),Evaluate(q,p*x); end if;
  q:=Evaluate(q,p*x);
  vq:=Min([Valuation(Coefficient(q,4-n),p : Check:=false) : n in [0..4]]);
  if vq ge 4 then return false,M*Matrix([[p,0],[0,1]]),Evaluate(q,x);
   else return true,Matrix([[1,0],[0,1]]),q0; end if; end if;
  if p ne 3 then
   s:=Integers()!Integers(p^2)!(-Coefficient(q,2)/(3*Coefficient(q,3)));
   q:=Evaluate(q,x+s); M:=M*Matrix([[1,s],[0,1]]);
   if (vq eq 0) then return false,M*Matrix([[p,0],[0,1]]),Evaluate(q,p*x);
    else return false,M*Matrix([[p^2,0],[0,1]]),Evaluate(q,p^2*x); end if;
  else // p is 3
   if vq eq 1 then
    return false,M*Matrix([[p,0],[0,1]]),Evaluate(q,p*x); end if;
   if v4 eq 4 then
    t:=Integers()!Integers(3)!(-Coefficient(q,0)/Coefficient(q,3)/27);
   else t:=Integers()!Integers(27)!(-Coefficient(q,2)/Coefficient(q,3)/9);
   end if;
  q:=Evaluate(q,x+3*t); M:=M*Matrix([[1,3*t],[0,1]]);
  return false,M*Matrix([[p^2,0],[0,1]]),Evaluate(q,p^2*x); end if;
end function;

intrinsic QuarticMinimise(q::RngUPolElt) -> RngUPolElt, AlgMatElt
{A minimal model of the binary quartic q (in the sense of Cremona-Stoll)}
 R:=BaseRing(q); t:=Type(R);
 require t in {RngInt, FldRat, FldFunRat} :
        "Only implemented for quartics over Z, Q or a rational function field";
 if t eq FldFunRat then m,T:=Minimise(GenusOneModel(Reverse(Coefficients(q)))); 
  return Parent(q)!Reverse(Eltseq(m)),T[2],T[1]; end if; // or Transpose(T) ?
 if BaseRing(q) ne Integers() then q := PolynomialRing(Integers())!q; end if; 
 q0:=q; sl2:=Matrix(2,2,[1,0,0,1]); dq:=Discriminant(q); bp:=PrimeDivisors(dq);
 bp:=[<p,Valuation(dq,p : Check:=false)> : p in bp];
 Sort(~bp,func<x,y|y[2]-x[2]>); bp:=[x : x in bp | x[2] ge 12];
 for p in bp do b:=false;
  vprintf QuarticMinimise,1: "Minimising at %o : valuation %o\n",p[1],p[2];
  while not b do b,mat,q:=QuarticMinimiseOnceAtPrime(q,p[1]);
   e:=Min([Valuation(x,p[1] : Check:=false) : x in Coefficients(q)]) div 2;
   q:=q div p[1]^(2*e); sl2:=sl2*mat; end while; end for;
 q1:=q0^sl2; r:=LeadingCoefficient(q)/LeadingCoefficient(q1); 
 assert ChangeRing(q,Rationals()) eq r*ChangeRing(q1,Rationals());
 b,sb:=IsSquare(r); require b: "QuarticMinimise did an illegal transformation";
 return q,sl2,sb; end intrinsic;

intrinsic QuarticMinimise(q::RngMPolElt) -> RngMPolElt, AlgMatElt
{"} // "
 P:=Parent(q); R:=BaseRing(P); t:=Type(R); 
 require Rank(Parent(q)) eq 2: "The quartic should be in a 2-variable polynomial ring";
 require t in {RngInt, FldRat, FldFunRat} :
        "Only implemented for quartics over Z, Q or a rational function field";
 P1:=PolynomialRing(R); q1:=Evaluate(q,[P1.1,1]); q1m,t,s:=QuarticMinimise(q1);
 d:=Degree(q1m); c:=Coefficients(q1m); 
 return &+[c[i+1]*P.1^i*P.2^(d-i): i in [0..d]],t,s; end intrinsic;
