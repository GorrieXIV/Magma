freeze;

import "misc.m": ProcessPresentation; 

Group6_33 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.33 valid only for p>3"; return false; end if;

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

w2:=w^2 mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),(d,c,d),
a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),(d,c,d),
a^p,b^p=(b,a,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),(d,c,d),
a^p=(b,a,b),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),(d,c,d),
a^p=(b,a,b)^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),(d,c,d),
a^p,b^p,c^p=(b,a,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),(d,c,d),
a^p,b^p=e,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),(d,c,d),
a^p=e,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),(d,c,d),
a^p=e^w,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p=e^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p,b^p=e,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p=e,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p=e^w,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p,b^p=e,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p=e,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a)=e,(d,b),(d,c,c),
(d,c,d),a^p=e^w,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p,c^p=e^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p=e,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p=e,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p=e,c^p=e^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p=e,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p=e,b^p,c^p=e^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p=e^w,b^p,c^p=e^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p,c^p=e^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p=e,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p=e,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p,b^p=e,c^p=e^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p=e,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p=e,b^p,c^p=e^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
(d,c,d)=e,a^p=e^w,b^p,c^p=e^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=40;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
   (d,c,d)=e,a^p,b^p=e,c^p,d^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,b),(b,a,a),(c,a)=e,(c,b),(d,a),(d,b),(d,c,c),
   (d,c,d)=e,a^p,b^p=e,c^p,d^p=e^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=42;
end if;

vprint Orderp7, 1: "Group 6.33 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 39+gcd(p-1,3) =",
39+Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
