freeze;

import "misc.m": ProcessPresentation; 

Group6_431 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.431 is valid only for p>5"; return false; end if;

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
GR:=Group<a,b | (b,a,a), (b,a,b), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | c=a^p,d=c^p,e=d^p,f=e^p, (b,a,a), (b,a,b)=f, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | c=a^p,d=c^p,e=d^p,f=e^p, (b,a,a), (b,a,b)=f^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | c=a^p,d=c^p,e=d^p,f=e^p, (b,a,a)=f, (b,a,b), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.431 has 4 descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 4";

if Process then return Nmr; else return L; end if;

end function;
