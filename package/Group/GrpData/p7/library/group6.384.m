freeze;

import "misc.m": ProcessPresentation; 

Group6_384 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.384 is valid only for p>3"; return false; end if;

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

r:=(p-1) div 2;
s:=F!(3); s:=s^-1; s:=Integers()!s;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d | c=(b,a),d=(c,a),(b,a,a,a), b^p=c*d^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|c=(b,a),d=a^p,e=(c,a),f=d^p,f^p,b^p=c*e^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.384 has 2 descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 2";

if Process then return Nmr; else return L; end if;

end function;
