freeze;

import "misc.m": ProcessPresentation; 

Group6_90 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.90 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p,(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b)=d^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p,(b,a,a), (b,a,b), (b,a,c), (c,a,c), d^p, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), d^p, 
                     (c,b)=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), d^p, (c,b), b^p, 
                      c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), d^p, 
                     (c,b)=e, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), d^p, (c,b), b^p, 
                      c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), d^p, 
                     (c,b)=e, b^p, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), d^p, (c,b), 
                      b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), d^p, 
                      (c,b)=e, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), d^p=e, 
                      (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), d^p=e, 
                      (c,b)=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), d^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), d^p, b^p, 
                       c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), d^p, 
                       b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), 
                       d^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), 
                       d^p=e^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p, b^p=e^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p=e^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), d^p, 
                       b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), d^p, 
                       b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), d^p, 
                       b^p=e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), 
                       d^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-w, (c,b), d^p,
                       b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-w, (c,b), d^p,
                       b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=a^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-w, (c,b), 
                       d^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.90 has 30 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 30";

if Process then return Nmr; else return L; end if;

end function;
