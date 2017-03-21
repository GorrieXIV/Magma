freeze;

import "misc.m": ProcessPresentation; 

Group6_110 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.110 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (b,a,a), (b,a,b), a^p=(c,b)^w, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (c,b,b), a^p=(c,b)^w, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (c,b,b), a^p=(c,b)^w, b^p=(c,a), c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (b,a,a), (c,b,b), a^p=(c,b)^w, b^p=(c,a), c^p=(b,a,b)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a), (c,b,b), a^p=(c,b)^w, b^p=(c,a), c^p=(b,a,b)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=5;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e | d=(c,a),e=(b,a,b),(b,a,a), (c,b,b), a^p=(c,b)^w, b^p=d*e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(c,a),e=(b,a,b),(b,a,a), (c,b,b), a^p=(c,b)^w, b^p=d*e^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;

vprint Orderp7, 1: "Group 6.110 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 2 + gcd(p-1,3) + gcd(p-1,4)/2 =",
2+Gcd(p-1,4)/2+Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
