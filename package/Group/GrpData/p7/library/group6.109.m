freeze;

import "misc.m": ProcessPresentation; 

Group6_109 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.109 valid only for p>3"; return false; end if;

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
r:=(p-1) div 2;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e,f|d=(c,a),e=(c,b),f=(c,a,a),(b,a,a), (b,a,b), a^p=d*e*f^r, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,a), (c,a,a), a^p=d*e, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=(c,b),f=(b,a,b),(b,a,a), (c,a,a), a^p=d*e, b^p=e*f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=(c,b),f=(b,a,b),(b,a,a), (c,a,a), a^p=d*e, b^p=e*f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,a), (c,a,a), a^p=d*e, b^p=e, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=5;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,a), (c,a,a), a^p=d*e, b^p=e, c^p=(b,a,b)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,a), (c,a,a), a^p=d*e, b^p=e, c^p=(b,a,b)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,b), (c,a,a), a^p=d*e, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=(c,b),f=(b,a,a),(b,a,b), (c,a,a), a^p=d*e, b^p=e*f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=(c,b),f=(b,a,a),(b,a,b), (c,a,a), a^p=d*e, b^p=e*f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,b), (c,a,a), a^p=d*e, b^p=e, c^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,b), (c,a,a), a^p=d*e, b^p=e, c^p=(b,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(c,a),e=(c,b),(b,a,b), (c,a,a), a^p=d*e, b^p=e, c^p=(b,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.109 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 7 + 2gcd(p-1,3) =",
7+2*Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
