freeze;

import "misc.m": ProcessPresentation; 

Group6_111 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.111 valid only for p>3"; return false; end if;

class:=3;

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

SQ:={};
for x in [0..((p-1) div 2)] do
  Include(~SQ,x^2 mod p);
end for;

L:=[]; Nmr := 0;
count:=0;

for x in [1..p-1] do
  y:=(1+4*x) mod p;
  if y in SQ then continue; end if;
  GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,a), (b,a,b), a^p=e^x, b^p=d*e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,a), (b,a,c), a^p=e^x, b^p=d*e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(c,b),f=(b,a,b),(b,a,a), (b,a,c), a^p=e^x, b^p=d*e*f, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(c,b),f=(b,a,b),(b,a,a), (b,a,c), a^p=e^x, b^p=d*e*f^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,a), (b,a,c), a^p=e^x, b^p=d*e, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+5;
  if p mod 3 eq 1 then
    GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,a), (b,a,c), a^p=e^x, b^p=d*e, c^p=(b,a,b)^w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,a), (b,a,c), a^p=e^x, b^p=d*e, c^p=(b,a,b)^w2>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;

vprint Orderp7, 1: "Group 6.111 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is (p-1)(4 + gcd(p-1,3))/2 =",
(p-1)*(4+Gcd(p-1,3))/2;

if Process then return Nmr; else return L; end if;

end function;
