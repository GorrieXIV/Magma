freeze;

import "misc.m": ProcessPresentation; 

Group6_228 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.228 valid only for p>3"; return false; end if;
 
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

L:=[]; Nmr := 0;

for x in [0..p-1] do
  GR:=Group<a,b,c,e,f,g | e=c^p,f=e^p,g=f^p,(c,a), (c,b)=g^x, a^p=(b,a), b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,e,f | e=c^p,f=e^p,(c,a)=f^p, (c,b), a^p=(b,a), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.228 has",p+1,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p+1 =",p+1;

if Process then return Nmr; else return L; end if;

end function;
