freeze;

import "misc.m": ProcessPresentation; 

Group6_88 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.88 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c,d | d=b^p,(b,a,a), (b,a,b), d^p, (c,a), (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=b^p,e=c^p,(b,a,a), (b,a,b), d^p, (c,a), (c,b)=e^p, a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=b^p,e=c^p,(b,a,a), (b,a,b), d^p, (c,a)=e^p, (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,e | e=c^p,(b,a,a), (b,a,b), e^p, (c,a), (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=b^p,e=c^p,(b,a,a), (b,a,b), e^p, (c,a), (c,b)=d^p, a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=b^p,e=c^p,(b,a,a), (b,a,b), e^p, (c,a)=d^p, (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,b),(b,a,a), d^p, e^p, (c,a), (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,b),(b,a,a), d^p, e^p, (c,a)=f, (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,b),(b,a,a), d^p, e^p, (c,a), (c,b), a^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,b),(b,a,a), d^p, e^p, (c,a)=f, (c,b), a^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,b),(b,a,a), d^p, e^p, (c,a), (c,b), a^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,b),(b,a,a), d^p, e^p, (c,a)=f, (c,b), a^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,b),(b,a,a), d^p, e^p=f, (c,a), (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,b),(b,a,a), d^p, e^p=f, (c,a)=f, (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,b),(b,a,a), d^p=f, e^p, (c,a), (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,b),(b,a,a), d^p=f, e^p, (c,a)=f, (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,a),(b,a,b), d^p, e^p, (c,a), (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,a),(b,a,b), d^p, e^p, (c,a), (c,b), a^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,a),(b,a,b), d^p, e^p, (c,a), (c,b)=f, a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,a),(b,a,b), d^p, e^p, (c,a), (c,b)=f, a^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,a),(b,a,b), d^p, e^p=f, (c,a), (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,a),(b,a,b), d^p, e^p=f, (c,a), (c,b)=f, a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,a),(b,a,b), d^p=f, e^p, (c,a), (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,a),(b,a,b), d^p=f, e^p, (c,a), (c,b)=f, a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,a),(b,a,b), d^p=f^w, e^p, (c,a), (c,b), a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=b^p,e=c^p,f=(b,a,a),(b,a,b), d^p=f^w, e^p, (c,a), (c,b)=f, a^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.88 has 26 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 26";

if Process then return Nmr; else return L; end if;

end function;
