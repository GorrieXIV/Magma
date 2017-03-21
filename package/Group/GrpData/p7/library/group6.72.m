freeze;

import "misc.m": ProcessPresentation; 

Group6_72 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.72 valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c), a^p, b^p, c^p, d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c), a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c), a^p, b^p, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c), a^p, b^p=f, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c), a^p, b^p=f, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=5;
if p mod 3 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
    (d,c), a^p, b^p=f^w, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
    (d,c), a^p, b^p=f^w, c^p=f, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
    (d,c), a^p, b^p=f^w2, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
    (d,c), a^p, b^p=f^w2, c^p=f, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c), a^p=f, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c), a^p=f, b^p, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c), a^p, b^p, c^p, d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c), a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c), a^p, b^p, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c), a^p, b^p=f, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c), a^p, b^p=f, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+7;
if p mod 3 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c), a^p, b^p=f^w, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c), a^p, b^p=f^w, c^p=f, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c), a^p, b^p=f^w2, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c), a^p, b^p=f^w2, c^p=f, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c), a^p=f, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c)=f, a^p, b^p, c^p, d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c)=f, a^p, b^p, c^p, d^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c)=f, a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c)=f, a^p, b^p, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c)=f, a^p, b^p=f, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c)=f, a^p, b^p=f, c^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+7;
if p mod 3 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
    (d,c)=f, a^p, b^p=f^w, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
    (d,c)=f, a^p, b^p=f^w, c^p=f, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
    (d,c)=f, a^p, b^p=f^w2, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
    (d,c)=f, a^p, b^p=f^w2, c^p=f, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), (d,b),
(d,c)=f, a^p=f, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c)=f, a^p, b^p, c^p, d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c)=f, a^p, b^p, c^p, d^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c)=f, a^p, b^p=f^x, 
    c^p=f, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
if p mod 3 eq 1 then
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c)=f, a^p, b^p=f^x, 
    c^p=f^w, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c)=f, a^p, b^p=f^x, 
    c^p=f^w2, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c)=f, a^p, b^p=f, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
if p mod 3 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c)=f, a^p, b^p=f^w, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c)=f, a^p, b^p=f^w2, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c)=f, a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c)=f, a^p=f, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
(d,b)=f, (d,c)=f, a^p=f^w, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c)=f, a^p=f^w2, b^p, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(e,a),(c,a), (c,b)=e*f^-1, (b,a,b), (d,a), 
    (d,b)=f, (d,c)=f, a^p=f^w3, b^p, c^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;

vprint Orderp7, 1: "Group 6.72 has",count,"descendants of order p^7 and p-class 4";
vprint Orderp7, 2: "Total number of groups is 17+(p+7)gcd(p-1,3)+gcd(p-1,4) =",
17+(p+7)*Gcd(p-1,3)+Gcd(p-1,4);

assert count eq 17+(p+7)*Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
