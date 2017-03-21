freeze;

import "misc.m": ProcessPresentation; 

Group6_424 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.424 is valid only for p>5"; return false; end if;

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

r:=(F!3)^-1; r:=Integers()!r;

L:=[]; Nmr := 0;
count:=0;

for x in [0..p-1] do
x1:=(r+x) mod p;
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | c=(b,a,a),d=(b,a,b,b),e=(d,a),a^p=c*d^x*e^x1,b^p=d*e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;

vprint Orderp7, 1: "Group 6.424 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is p^2 =",p^2;

if Process then return Nmr; else return L; end if;

end function;
