freeze;

import "misc.m": ProcessPresentation; 

Group6_11 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.11 valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d | (b,a,a), (b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), b^p,
c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | e=a^p,(b,a,a), (b,a,b), (c,a)=e^p, (c,b), (d,a), (d,b), 
(d,c), b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | e=a^p,(b,a,a), (b,a,b), (c,a), (c,b)=e^p, (d,a), (d,b), 
(d,c), b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | e=a^p,(b,a,a), (b,a,b), (c,a), (c,b)=e^p, (d,a)=e^p, 
(d,b), (d,c), b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | e=a^p,(b,a,a), (b,a,b), (c,a), (c,b), (d,a), (d,b), 
(d,c)=e^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p=f, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a), (c,b), (d,a), (d,b), (d,c), 
e^p=f, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a)=f, (c,b), (d,a), (d,b), (d,c), 
e^p=f, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p=f^w, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a), (c,b), (d,a), (d,b), (d,c), 
e^p=f^w, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a)=f, (c,b), (d,a), (d,b), (d,c), 
e^p=f^w, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p, b^p, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p, b^p=f, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a), (c,b), (d,a), (d,b), (d,c), e^p, b^p, 
c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a), (c,b), (d,a), (d,b), (d,c), e^p, 
b^p=f, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a), (c,b), (d,a), (d,b), (d,c), e^p, b^p, 
c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a)=f, (c,b), (d,a), (d,b), (d,c), 
e^p, b^p, c^p, d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a)=f, (c,b), (d,a), (d,b), (d,c), 
e^p, b^p, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a)=f, (c,b), (d,a), (d,b), (d,c), 
e^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,b),(b,a,a), (c,a)=f, (c,b), (d,a), (d,b), (d,c), 
e^p, b^p=f, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e | e=a^p,(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), 
e^p=(b,a,a), b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=f, (d,a), (d,b), (d,c), 
e^p=f, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p=f, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p, b^p=f, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p, b^p=f^w, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p, b^p, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p, b^p=f, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=f, 
e^p, b^p=f^w, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), e^p, b^p, 
c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), e^p, b^p, 
c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), e^p, 
b^p=f, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), e^p, 
b^p=f^w, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=f, (d,a), (d,b), (d,c), 
e^p, b^p, c^p, d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=f, (d,a), (d,b), (d,c), 
e^p, b^p, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=f, (d,a), (d,b), (d,c), 
e^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=f, (d,a), (d,b), (d,c), 
e^p, b^p=f, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | e=a^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=f, (d,a), (d,b), (d,c), 
e^p, b^p=f^w, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.11 has 39 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 39";

if Process then return Nmr; else return L; end if;

end function;
