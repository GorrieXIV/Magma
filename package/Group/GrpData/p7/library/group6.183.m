freeze;

import "misc.m": ProcessPresentation; 

Group6_183 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.183 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c,d,e | d=a^p,e=b^p,(b,a)=d^p, (c,a), (c,b), e^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=b^p,f=d^p,(b,a)=f,(c,a),(c,b)=f^p,e^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.183 has 2 descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 2";

if Process then return Nmr; else return L; end if;

end function;
