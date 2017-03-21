freeze;

import "misc.m": ProcessPresentation; 

Group6_100 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.100 valid only for p>3"; return false; end if;

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

r:=(p-1) div 2; r:=(r*w) mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (b,a,a), (c,a,a), (c,b), b^p=(c,a)^w, c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p,(b,a,a), (c,a,a), (c,b)=d^p, b^p=(c,a)^w, c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=(c,a),f=(e,a),(b,a,a), d^p, (c,b), b^p=e^w*f^r, c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.100 has 3 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 3";

if Process then return Nmr; else return L; end if;

end function;
