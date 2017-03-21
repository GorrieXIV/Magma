freeze;

import "misc.m": ProcessPresentation; 

Group6_448 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.448 is valid only for p>5"; return false; end if;

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

L:=[]; Nmr := 0;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(d,a),(b,a,b), c^p, b^p=d*e^(x-1)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=(p+1) div 2;
vprint Orderp7, 1: "Group 6.448 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is (p+1)/2 =",(p+1)/2;

if Process then return Nmr; else return L; end if;

end function;
