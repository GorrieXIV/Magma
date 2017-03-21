freeze;

import "misc.m": ProcessPresentation; 

Group6_3 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.3 valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d,e | (c,a), (c,b), (b,a,b), (d,a), (d,b), (d,c), (e,a), 
(e,b), (e,c), (e,d), a^p, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(c,a), (c,b), (b,a,b), (d,a), (d,b), (d,c), (e,a), 
(e,b), (e,c), (e,d), a^p=f, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(c,a), (c,b), (b,a,b), (d,a), (d,b), (d,c), (e,a), 
(e,b), (e,c), (e,d), a^p, b^p=f, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(c,a), (c,b), (b,a,b), (d,a), (d,b), (d,c), (e,a), 
(e,b), (e,c), (e,d), a^p, b^p=f^w, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(c,a), (c,b), (b,a,b), (d,a), (d,b), (d,c), (e,a), 
(e,b), (e,c), (e,d), a^p, b^p, c^p=f, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(c,a), (c,b)=f, (b,a,b), (d,a), (d,b), (d,c), 
(e,a), (e,b), (e,c), (e,d), a^p, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(c,a), (c,b)=f, (b,a,b), (d,a), (d,b), (d,c), 
(e,a), (e,b), (e,c), (e,d), a^p=f, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(c,a), (c,b)=f, (b,a,b), (d,a), (d,b), (d,c), 
(e,a), (e,b), (e,c), (e,d), a^p, b^p=f, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(c,a), (c,b)=f, (b,a,b), (d,a), (d,b), (d,c), 
(e,a), (e,b), (e,c), (e,d), a^p, b^p=f^w, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(c,a), (c,b)=f, (b,a,b), (d,a), (d,b), (d,c), 
(e,a), (e,b), (e,c), (e,d), a^p, b^p, c^p=f, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(c,a), (c,b)=f, (b,a,b), (d,a), (d,b), (d,c), 
(e,a), (e,b), (e,c), (e,d), a^p, b^p, c^p, d^p=f, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b), (e,c), (e,d), a^p, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b), (e,c), (e,d), a^p=f, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b), (e,c), (e,d), a^p, b^p=f, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b), (e,c), (e,d), a^p, b^p=f^w, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b), (e,c), (e,d), a^p, b^p, c^p=f, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b), (e,c), (e,d), a^p, b^p=f, c^p=f, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b), (e,c), (e,d), a^p, b^p=f^w, c^p=f, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b), (e,c), (e,d), a^p, b^p, c^p, d^p, e^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b)=f, (e,c), (e,d), a^p, b^p, c^p, d^p, e^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b)=f, (e,c), (e,d), a^p, b^p, c^p=f, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b)=f, (e,c), (e,d), a^p, b^p=f, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b)=f, (e,c), (e,d), a^p, b^p=f^w, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b)=f, (e,c), (e,d), a^p, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
(e,a), (e,b)=f, (e,c), (e,d), a^p=f, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.3 has 25 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 25";

if Process then return Nmr; else return L; end if;

end function;
