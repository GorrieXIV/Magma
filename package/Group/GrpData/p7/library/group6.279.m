freeze;

import "misc.m": ProcessPresentation; 

Group6_279 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.279 valid only for p>3"; return false; end if;
 
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

r:=(p+1) div 2;

L:=[]; Nmr := 0;

for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(e,a),(c,b)=e^w*f^-w, (c,a,c)=f^x, 
                 a^p=d*f^r, b^p=e*f^-1, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.279 has",p,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p =",p;

if Process then return Nmr; else return L; end if;

end function;
