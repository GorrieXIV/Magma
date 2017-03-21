freeze;

import "misc.m": ProcessPresentation; 

Group6_212 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "5.15 valid only for p>3"; return false; end if;
 
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

GR:=Group<a,b,c | (c,a), (c,b), b^p, c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,e,f | e=a^p,f=e^p,(c,a)=f^p,(c,b),b^p,c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,e,f | e=a^p,f=e^p,(c,a),(c,b)=f^p,b^p,c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,e,f,g | e=a^p,f=e^p,g=f^p,(c,a),(c,b)=g^w,b^p,c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.212 has 4 descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 4";

if Process then return Nmr; else return L; end if;

end function;
