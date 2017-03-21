freeze;

import "misc.m": ProcessPresentation; 

Group5_60 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "5.60 valid only for p>5"; return false; end if;

class:=5;

w:=0;
F:=FiniteField(p);
for i in [2..p-1] do
a:=F!i;
S:={a};
for j in [2..p-1] do
  Include(~S,a^j);
end for;
if #S eq p-1 then
  w:=i;
  break;
end if;
end for;
vprint Orderp7, 2:"p equals",p;
vprint Orderp7, 2:"w equals",w;

r:=Integers()!((F!(-6))^-1);
w2:=w^2 mod p;
w3:=w^3 mod p;
w4:=w^4 mod p;
w5:=w^5 mod p;
w6:=w^6 mod p;
w7:=w^7 mod p;

CUBES:={};
T3:={};
for x in [1..p-1] do
  y:=x^3 mod p;
  if y notin CUBES then
    Include(~CUBES,y);
    Include(~T3,x);
  end if;
end for;

L:=[]; Nmr := 0;
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p, b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=d, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=d*e, b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=d*e^w, b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=p+6;
if p mod 4 eq 1 then
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=d*e^w2, b^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=d*e^w3, b^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=p+8;
end if;
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p, b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e, b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e^w, b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e^x, b^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p, b^p=d^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e, b^p=d^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e^w, b^p=d^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e^x, b^p=d^w*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
if p mod 4 eq 1 then
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p, b^p=d^w2>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e, b^p=d^w2>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e^w, b^p=d^w2>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e^x, b^p=d^w2*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p, b^p=d^w3>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e, b^p=d^w3>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e^w, b^p=d^w3>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=e^-r, a^p=e^x, b^p=d^w3*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
end if;
//print count,(p+4)*(1+Gcd(p-1,4));
count1:=count;
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p, b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p, b^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p, b^p=e^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p, b^p=e^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p, b^p=e^w4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p, b^p=e^w5>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
for x in [0..p-1] do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d^w, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
if p mod 3 eq 1 then
for x in [0..p-1] do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d^w2, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r,a^p=d^w3, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d^w4, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d^w5, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
end if;
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^w2, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^w3, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
if p mod 8 eq 1 then
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^w4, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^w5, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^w6, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^w7, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
for x in T3 do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d*e^x, b^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d^w*e^x, b^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
if p mod 3 eq 1 then
for x in T3 do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d^w2*e^x, b^p=e^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d^w3*e^x, b^p=e^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d^w4*e^x, b^p=e^w4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=d^w5*e^x, b^p=e^w5>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
end if;
//print count-count1,2*p-1+2*(p+1)*Gcd(p-1,3)+Gcd(p-1,8);
count1:=count;
if p mod 4 eq 3 then
for x in [0..p-1] do
for y in [0..p-1] do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^x, b^p=d*e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^x, b^p=d^w*e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end for;
end if;
if p mod 4 eq 1 then
for x in [0..p-1] do
for y in [0..(p-1) div 2] do
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^x, b^p=d*e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^x, b^p=d^w*e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^x, b^p=d^w2*e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,d,e | d=(b,a,a,a,a), e=(b,a,a,a,b), (b,a,b)=d*e^-r, a^p=e^x, b^p=d^w3*e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
end for;
end if;
//print count-count1,2*p^2+p*(Gcd(p-1,4)-2);

vprint Orderp7, 1: "Group 5.60 has",count,"descendants of order p^7 and class 5";

vprint Orderp7, 2: "Total number of groups is 2p^2 + p + 3 + 2(p+1)gcd(p-1,3) + (2p+4)gcd(p-1,4) + gcd(p-1,8) = ",
2*p^2+p+3+2*(p+1)*Gcd(p-1,3)+(2*p+4)*Gcd(p-1,4)+Gcd(p-1,8);

if Process then return Nmr; else return L; end if;

end function;

Children21 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_60 (p: Process:=Process, Select:=Select);
end function;

