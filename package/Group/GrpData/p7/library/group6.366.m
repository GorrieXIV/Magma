freeze;

import "misc.m": ProcessPresentation; 

Group6_366 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.366 is valid only for p>3"; return false; end if;

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

w2:=w^2 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d|c=b^p,d=c^p,(b,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|c=b^p,d=c^p,e=a^p,f=e^p,(b,a)=f^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,e,f|e=a^p,f=e^p,(b,a)=f,f^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|c=b^p,d=c^p,e=a^p,(b,a)=e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Groups 6.366 and 6.367 each have 2 descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 4";

if Process then return Nmr; else return L; end if;

end function;
