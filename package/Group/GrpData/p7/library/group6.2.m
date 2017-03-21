freeze;

import "misc.m": ProcessPresentation; 

Group6_2 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.2 valid only for p>3"; return false; end if;

class:=3;

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
GR:=Group<a,b,c,d,e | (b,a),(c,a),(d,a),(e,a),(c,b),(d,b),(e,b),(d,c),
(e,c), (e,d), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | f=a^p,g=f^p,(b,a)=g, (c,a), (d,a), (e,a), (c,b), (d,b), (e,b),
(d,c), (e,c), (e,d), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | f=a^p,g=f^p,(b,a), (c,a), (d,a), (e,a), (c,b)=g, (d,b), (e,b),
(d,c), (e,c), (e,d), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | f=a^p,g=f^p,(b,a), (c,a), (d,a)=g, (e,a), (c,b)=g, (d,b),
(e,b), (d,c), (e,c), (e,d), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | f=a^p,g=f^p,(b,a), (c,a), (d,a), (e,a), (c,b)=g, (d,b), (e,b),
(d,c), (e,c), (e,d)=g, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.2 has 5 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 5";

if Process then return Nmr; else return L; end if;

end function;
