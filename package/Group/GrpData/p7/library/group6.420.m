freeze;

import "misc.m": ProcessPresentation; 

Group6_420 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.420 is valid only for p>5"; return false; end if;

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

r:=-(F!6)^-1; r:=Integers()!r;
w2:=w^2 mod p;
w3:=w^3 mod p;

L:=[]; Nmr := 0;
count:=0;

for x in [0..p-1] do
  GR:=Group<a,b,c,d|c=(b,a,a),d=(b,a,b,b,b),(b,a,b,b,a), a^p=c*d^x, 
                     b^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a),d=(b,a,b,b,b),(b,a,b,b,a), a^p=c*d^x, 
                     b^p=d^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c|c=(b,a,a),(b,a,b,b,a), a^p=c, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a),d=(b,a,b,b,b),(b,a,b,b,a), a^p=c*d, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a),d=(b,a,b,b,b),(b,a,b,b,a), a^p=c*d^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d|c=(b,a,a),d=(b,a,b,b,b),(b,a,b,b,a), a^p=c*d^w2, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a),d=(b,a,b,b,b),(b,a,b,b,a), a^p=c*d^w3, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

for x in [0..p-1] do
  GR:=Group<a,b,c,d|c=(b,a,a),d=(b,a,b,b,a),(b,a,b,b,b), a^p=c*d^r, 
                     b^p=d^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a),d=(b,a,b,b,a),(b,a,b,b,b)=d, a^p=c*d^r,
                     b^p=d^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a),d=(b,a,b,b,a),(b,a,b,b,b)=d^w, a^p=c*d^r,
                     b^p=d^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
end for;

vprint Orderp7, 1: "Group 6.420 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 5p + 1 + gcd(p-1,4) =",
5*p+1+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
