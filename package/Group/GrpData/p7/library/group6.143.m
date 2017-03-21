freeze;

import "misc.m": ProcessPresentation; 

Group6_143 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.143 valid only for p>3"; return false; end if;

class:=4;

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
L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e|d=(b,a,b),e=(d,b),(c,a)=d*e^-1, (c,b), a^p, b^p=(b,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,b),e=(d,b),(c,a)=d*e^-1, (c,b), a^p=e, b^p=(b,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(d,b),(c,a)=d*e^-1, (c,b), a^p=e^w, b^p=(b,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(d,b),(c,a)=d*e^-1, (c,b), a^p=e^w2, b^p=(b,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(d,b),(c,a)=d*e^-1, (c,b), a^p=e^x, b^p=(b,a,a)^w, c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.143 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (p+3)/2 + gcd(p-1,3) =",
(p+3)/2+Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
