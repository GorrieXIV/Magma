freeze;

import "misc.m": ProcessPresentation; 

Group6_1 := function (p: Process:=true, Select:=func<x|true>)

class:=2;

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
GR:=Group<a,b,c,d,e,f | (b,a), (c,a), (d,a), (e,a), (f,a), (c,b), (d,b), 
(e,b), (f,b), (d,c), (e,c), (f,c), (e,d), (f,d), (f,e), b^p, c^p, d^p, e^p, f^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | (c,a), (d,a), (e,a), (f,a), (c,b), (d,b), (e,b), 
(f,b), (d,c), (e,c), (f,c), (e,d), (f,d), (f,e), a^p, b^p, c^p, d^p, e^p, f^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | (c,a), (d,a), (e,a), (f,a), (c,b), (d,b), (e,b), 
(f,b), (d,c), (e,c), (f,c), (e,d), (f,d), (f,e), a^p=(b,a), b^p, c^p, d^p, 
e^p, f^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | (c,a), (d,a), (e,a), (f,a), (c,b), (d,b), (e,b), 
(f,b), (d,c), (e,c), (f,c), (e,d), (f,d), (f,e), a^p, b^p, c^p=(b,a), d^p, 
e^p, f^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | (c,a), (d,a), (e,a), (f,a), (c,b), (d,b), (e,b), 
(f,b), (d,c)=(b,a), (e,c), (f,c), (e,d), (f,d), (f,e), a^p, b^p, c^p, d^p, 
e^p, f^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | (c,a), (d,a), (e,a), (f,a), (c,b), (d,b), (e,b), 
(f,b), (d,c)=(b,a), (e,c), (f,c), (e,d), (f,d), (f,e), a^p=(b,a), b^p, 
c^p, d^p, e^p, f^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | (c,a), (d,a), (e,a), (f,a), (c,b), (d,b), (e,b), 
(f,b), (d,c)=(b,a), (e,c), (f,c), (e,d), (f,d), (f,e), a^p, b^p, c^p, d^p, 
e^p=(b,a), f^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | (c,a), (d,a), (e,a), (f,a), (c,b), (d,b), (e,b), 
(f,b), (d,c)=(b,a), (e,c), (f,c), (e,d), (f,d), (f,e)=(b,a), a^p, b^p, 
c^p, d^p, e^p, f^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | (c,a), (d,a), (e,a), (f,a), (c,b), (d,b), (e,b), 
(f,b), (d,c)=(b,a), (e,c), (f,c), (e,d), (f,d), (f,e)=(b,a), 
a^p=(b,a), b^p, c^p, d^p, e^p, f^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 2:"There are 9 six generator groups of order p^7 and p-class 2";

vprint Orderp7, 2: "Total number of groups is 9";

if Process then return Nmr; else return L; end if;

end function;
