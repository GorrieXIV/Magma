freeze;

import "misc.m": ProcessPresentation; 

Group6_67 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.67 valid only for p>3"; return false; end if;

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
w3:=w^3 mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), a^p, b^p, 
c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), a^p, 
b^p=e, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), a^p, 
    b^p=e^w, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), a^p, 
    b^p=e^w2, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=4;
end if;
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), a^p, b^p, 
c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c), 
a^p=e, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), (d,c), 
a^p, b^p, c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), (d,c), 
a^p, b^p=e, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), (d,c), 
    a^p, b^p=e^w, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), (d,c), 
    a^p, b^p=e^w2, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), (d,c), 
a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), (d,c), 
a^p=e, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), (d,c), 
a^p=e^w, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), (d,c), 
    a^p=e^w2, b^p, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), (d,c), 
    a^p=e^w3, b^p, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b)=e, (d,a), (d,b), (d,c), 
a^p, b^p, c^p, d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b)=e, (d,a), (d,b), (d,c), 
a^p, b^p, c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b)=e, (d,a), (d,b), (d,c), 
a^p, b^p=e, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b)=e, (d,a), (d,b), (d,c), 
    a^p, b^p=e^w, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b)=e, (d,a), (d,b), (d,c), 
    a^p, b^p=e^w2, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b)=e, (d,a), (d,b), (d,c), 
a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b)=e, (d,a), (d,b), (d,c), 
a^p=e, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
(d,b), (d,c), a^p, b^p, c^p, d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
(d,b), (d,c), a^p, b^p, c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
(d,b), (d,c), a^p, b^p, c^p=e^w, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
(d,b), (d,c), a^p, b^p=e, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
    (d,b), (d,c), a^p, b^p=e^w, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
    (d,b), (d,c), a^p, b^p=e^w2, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
(d,b), (d,c), a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
(d,b), (d,c), a^p=e, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
(d,b), (d,c), a^p=e^w, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
    (d,b), (d,c), a^p=e^w2, b^p, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b)=e, (d,a), 
    (d,b), (d,c), a^p=e^w3, b^p, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=e, 
a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=e, 
a^p, b^p, c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=e, 
a^p, b^p=e, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=e, 
a^p, b^p=e, c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=e, 
    a^p, b^p=e^w, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=e, 
    a^p, b^p=e^w, c^p=e, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=e, 
    a^p, b^p=e^w2, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=e, 
    a^p, b^p=e^w2, c^p=e, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b), (c,a), (c,b), (d,a), (d,b), (d,c)=e, 
a^p=e, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
(d,c)=e, a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
(d,c)=e, a^p, b^p, c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
(d,c)=e, a^p, b^p=e, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
(d,c)=e, a^p, b^p=e, c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+5;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
    (d,c)=e, a^p, b^p=e^w, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
    (d,c)=e, a^p, b^p=e^w, c^p=e, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
    (d,c)=e, a^p, b^p=e^w2, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
    (d,c)=e, a^p, b^p=e^w2, c^p=e, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
(d,c)=e, a^p=e, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
(d,c)=e, a^p=e^w, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
    (d,c)=e, a^p=e^w2, b^p, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|e=(b,a,a,a),(b,a,b)=e, (c,a), (c,b), (d,a), (d,b), 
    (d,c)=e, a^p=e^w3, b^p, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.67 has",count,"descendants or order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 18+8gcd(p-1,3)+3gcd(p-1,4) =",
18+8*Gcd(p-1,3)+3*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
