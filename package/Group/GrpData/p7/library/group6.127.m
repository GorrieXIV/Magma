freeze;

import "misc.m": ProcessPresentation; 

Group6_127 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.127 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c | (c,a), (c,b), a^p, b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a), (c,b), a^p=(b,a,a,a), b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a), (c,b), a^p, b^p=(b,a,a,a), c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,a), (c,b), a^p, b^p=(b,a,a,a)^w, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a), (c,b), a^p, b^p=(b,a,a,a)^w2, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=5;
end if;
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b), a^p, b^p, c^p=d*e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b), a^p=e, b^p, c^p=d*e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b), a^p=e^w, b^p, c^p=d*e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b), a^p=e^w2, b^p, c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b), a^p=e^w3, b^p, c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b), a^p, b^p=e, c^p=d*e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b), a^p, b^p=e^w, c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b), a^p, b^p=e^w2, c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a), a^p, b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a), a^p=(b,a,a,a), b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a), a^p=(b,a,a,a)^w, b^p, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a), a^p=(b,a,a,a)^w2, b^p, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a), a^p, b^p=(b,a,a,a), c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a), a^p, b^p=(b,a,a,a)^w, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a), a^p, b^p=(b,a,a,a)^w2, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b)=e, a^p, b^p=e^x, c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b)=e, a^p=e^x, b^p, c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a)^w, a^p, b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a)^w, a^p=(b,a,a,a), b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a)^w, a^p=(b,a,a,a)^w, b^p, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a)^w, a^p=(b,a,a,a)^w2, b^p, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a)^w, a^p, b^p=(b,a,a,a), c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a)^w, a^p, b^p=(b,a,a,a)^w, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a), (c,b)=(b,a,a,a)^w, a^p, b^p=(b,a,a,a)^w2, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b)=e^w, a^p, b^p=e^x, c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a), (c,b)=e^w, a^p=e^x, b^p, c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.127 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 3p + 4 + 6gcd(p-1,3) + gcd(p-1,4) =",
3*p+4+6*Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
