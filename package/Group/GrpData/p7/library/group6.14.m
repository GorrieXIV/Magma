freeze;

import "misc.m": ProcessPresentation; 

Group6_14 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.14 valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d|(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=c^p,(b,a,a),(b,a,b),(c,a)=e^p,(c,b),(d,a),(d,b),(d,c),a^p,b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=c^p,(b,a,a),(b,a,b),(c,a),(c,b),(d,a)=e^p,(d,b),(d,c),a^p,b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=c^p,(b,a,a),(b,a,b),(c,a),(c,b)=e^p,(d,a)=e^p,(d,b),(d,c),a^p,b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=c^p,(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e^p,a^p,b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=c^p,(b,a,a),(b,a,b),(c,a),(c,b),(d,a)=e^p,(d,b),(d,c)=e^p,a^p,b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p,e^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p=f,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p=f^w,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c),a^p=f,b^p,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b)=f,(d,a),(d,b),(d,c),a^p,b^p,e^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b)=f,(d,a),(d,b),(d,c),a^p,b^p=f,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b)=f,(d,a),(d,b),(d,c),a^p,b^p=f^w,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b)=f,(d,a),(d,b),(d,c),a^p,b^p,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b)=f,(d,a),(d,b),(d,c),a^p=f,b^p,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c),a^p,b^p,e^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c),a^p,b^p=f,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c),a^p,b^p=f^w,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c),a^p,b^p,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c),a^p=f,b^p,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p,e^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p=f,e^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p=f^w,e^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p=f,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p=f^w,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=f,a^p=f,b^p,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c)=f,a^p,b^p,e^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c)=f,a^p,b^p=f,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c)=f,a^p,b^p=f^w,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c)=f,a^p,b^p,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c)=f,a^p=f,b^p,e^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p,e^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b)=f,(d,a),(d,b),(d,c),a^p,b^p,e^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c),a^p,b^p,e^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p,e^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f,(d,c)=f,a^p,b^p,e^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=(b,a,a),(b,a,b),(c,a),(c,b),(d,a),(d,b)=f^w,(d,c)=f,a^p,b^p,e^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.14 has 39 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 39";

if Process then return Nmr; else return L; end if;

end function;
