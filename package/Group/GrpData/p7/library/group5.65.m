freeze;

import "misc.m": ProcessPresentation; 

Group5_65 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "5.65 valid only for p>5"; return false; end if;

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

w2:=w^2 mod p;
w3:=w^3 mod p;
w4:=w^4 mod p;
w5:=w^5 mod p;

FIFTH:={};
T5:={};
for x in [1..p-1] do
  y:=x^5 mod p;
  if y notin FIFTH then
    Include(~FIFTH,y);
    Include(~T5,x);
  end if;
end for;

FOURTH:={};
T4:={};
for x in [1..p-1] do
  y:=x^4 mod p;
  if y notin FOURTH then
    Include(~FOURTH,y);
    Include(~T4,x);
  end if;
end for;

r:=F!(7)*(F!(6))^-1;
r:=Integers()!r;

L:=[]; Nmr := 0;
count:=0;
for x in T4 do
for y in [0..p-1] do
for z in [0..p-1] do
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^x*e^y, b^p=d*e^z>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^x*e^y, b^p=d^w*e^z>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
  if p mod 4 eq 1 then
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^x*e^y, b^p=d^w2*e^z>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^x*e^y, b^p=d^w3*e^z>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
end for;
end for;
for x in [0..p-1] do
for y in T4 do
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=d*e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=d^w*e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
  if p mod 4 eq 1 then
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=d^w2*e^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=d^w3*e^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
end for;
if p mod 4 eq 3 then
for x in [1..p-1] do
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=d^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end if;
if p mod 4 eq 1 then
for x in [1..(p-1) div 2] do
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=d^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=d^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=d^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
end if;
GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p, b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p, b^p=d^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p, b^p=d^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p, b^p=d^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
if p mod 5 eq 1 then
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^w, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^w2, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^w3, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^w4, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
end if;
for x in [0..p-1] do
for y in T5 do
  count:=count+1;
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d*e^y, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 5 eq 1 then
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^w*e^y, b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^w2*e^y, b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^w3*e^y, b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=d^w4*e^y, b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+4;
  end if;
end for;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p, b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 5 eq 1 then
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p, b^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p, b^p=e^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p, b^p=e^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p, b^p=e^w4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
for x in T5 do
  count:=count+1;
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 5 eq 1 then
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=e^w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=e^w2>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=e^w3>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^x, b^p=e^w4>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+4;
  end if;
end for;
GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^w2, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^w3, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^w4, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(c,b),(b,a,b)=c*d^-1*e^r, a^p=e^w5, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;

vprint Orderp7, 1: "Group 5.65 has",count,"descendants of order p^7 and class 5";

vprint Orderp7, 2:"Total number of groups is p^3 + p^2 + p - 2 + 2gcd(p-1,3) + gcd(p-1,4) + (p+1)gcd(p-1,5) =",
p^3+p^2+p-2+2*Gcd(p-1,3)+Gcd(p-1,4)+(p+1)*Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;

Children22 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_65 (p: Process:=Process, Select:=Select);
end function;
