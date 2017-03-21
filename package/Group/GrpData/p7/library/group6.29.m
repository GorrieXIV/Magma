freeze;

import "misc.m": ProcessPresentation; 

Group6_29 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.29 valid only for p>3"; return false; end if;

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
w3:=w^3 mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p,
c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p,
c^p=f,d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p,c^p,
d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f,b^p,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f^w,b^p,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p=f,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f,
b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f^w,
b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p,c^p,
d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f,b^p,
c^p,d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f^w,b^p,
c^p,d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p=f,
c^p,d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f,
b^p=f,c^p,d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f^w,
b^p=f,c^p,d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [1..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p,b^p,
    c^p=f^x,d^p=e*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=p+13;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p,b^p,
c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p,b^p,
c^p=f^w,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p,
b^p,c^p,d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),
a^p=f,b^p,c^p,d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),
a^p=f^w,b^p,c^p,d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+5;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p=f^x,
    b^p=f,c^p,d^p=e*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p,b^p,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),
a^p=f,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),
a^p=f^w,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p,
b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),
a^p=f,b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),
a^p=f^w,b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
    a^p=f^x,b^p,c^p=f,d^p=e*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p,
c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f,b^p,c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f^w,b^p,c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
    a^p=f^x,b^p,c^p,d^p=e*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
    a^p=f^x,b^p=f,c^p,d^p=e*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f^w,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,
b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f,b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f^w,b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,
    a^p=f^x,b^p,c^p=f,d^p=e*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,a^p,b^p,
c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,
a^p=f,b^p,c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,
a^p=f^w,b^p,c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,
    a^p=f^x,b^p,c^p,d^p=e*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,
    a^p=f^x,b^p=f,c^p,d^p=e*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,a^p,b^p,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,
a^p=f,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,
a^p=f^w,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,a^p,
b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,
a^p=f,b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f^w,
a^p=f^w,b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p,b^p,
c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p,b^p=f,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p,b^p=f^w,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p,b^p,c^p,
d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p=f,b^p,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f^w,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,a^p,
b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,a^p,
b^p=f^w,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,a^p,b^p,
c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,a^p,
b^p=f,c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,a^p,
b^p=f^w,c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),
(d,c)=f,a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),
(d,c)=f,a^p=f,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),
(d,c)=f,a^p=f^w,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+22;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),
    (d,c)=f,a^p=f^w2,b^p,c^p,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),
   (d,c)=f,a^p=f^w3,b^p,c^p,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),
(d,c)=f,a^p,b^p,c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),
    (d,c)=f,a^p,b^p,c^p=f^w,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),
    (d,c)=f,a^p,b^p,c^p=f^w2,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),
    (d,c)=f,a^p,b^p=f,c^p=f^x,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),
    (d,c)=f,a^p,b^p=f^w,c^p=f^x,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),a^p,b^p,
c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),a^p,
b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),a^p,
b^p=f^w,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),a^p,b^p,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),
a^p=f,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),a^p,b^p,
c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),a^p,
b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),a^p,
b^p=f^w,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),a^p,b^p,
c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),
a^p=f,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=f,
(d,c),a^p,b^p,c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+11;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=f,
    (d,c),a^p,b^p=f^x,c^p,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=f,
(d,c),a^p=f,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;

vprint Orderp7, 1: "Group 6.29 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 10p+69+gcd(p-1,3)+gcd(p-1,4) =",
10*p+69+Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
