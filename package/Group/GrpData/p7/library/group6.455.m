freeze;

import "misc.m": ProcessPresentation; 

Group6_455 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.455 is valid only for p>5"; return false; end if;

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

r:=(F!6)^-1; r:=Integers()!r;

L:=[]; Nmr := 0;
GR:=Group<a,b,c|c=a^p,(b,a,a)=(b,a,b,b,a)^r, c^p, b^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a)=(b,a,b,b,a)^r, c^p=(b,a,b,b,a), b^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=e^r, c^p, b^p=d*e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=e^r, c^p, b^p=d*e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.455 has 4 descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 4";

if Process then return Nmr; else return L; end if;

end function;
