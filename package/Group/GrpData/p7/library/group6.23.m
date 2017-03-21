freeze;

import "misc.m": ProcessPresentation; 

Group6_23 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.23 valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d|(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(c,a),
c^p,d^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(c,a),
c^p=(b,a,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(c,a),
c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=(b,a,b),
b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=(b,a,b)^w,
b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p,
b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f,
b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f^w,
b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,
b^p=(c,a),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,a),(c,b),(d,a),(d,b),(d,c)=(b,a,b),a^p,
b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f^w,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,a^p,
b^p=(c,a),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f,b^p=(c,a),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f^w,b^p=(c,a),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=15;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
    a^p=f^w2,b^p=(c,a),c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b),(d,c)=f,
    a^p=f^w3,b^p=(c,a),c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=17;
end if;
GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p,
b^p=(c,a),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p,
b^p=(c,a),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,a),(c,b),(d,a)=(b,a,b),(d,b),(d,c),a^p,
b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),
a^p=f,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b),(d,c),
a^p=f^w,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d|(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(c,a),
c^p,d^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(c,a),
c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p=(b,a,a),
b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(c,a),
c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+9;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d|(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(c,a),
    c^p*(b,a,a)^-w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|(b,a,b),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(c,a),
    c^p*(b,a,a)^-w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d|(b,a,b),(c,b),(d,a),(d,b)=(b,a,a),(d,c),a^p,
b^p=(c,a),c^p,d^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),a^p,
b^p=(c,a),c^p=f,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),a^p,
    b^p=(c,a),c^p=f^w,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),a^p,
    b^p=(c,a),c^p=f^w2,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d|(b,a,b),(c,b),(d,a),(d,b)=(b,a,a),(d,c),a^p,
b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),
a^p=f,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),a^p,
b^p=(c,a),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),a^p,
    b^p=(c,a),c^p=f^w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=f,(d,c),a^p,
    b^p=(c,a),c^p=f^w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,a^p,
b^p=(c,a),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),a^p,
b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,a^p,
b^p=(c,a),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,a^p,
    b^p=(c,a),c^p=f^w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b),(d,c)=f,a^p,
    b^p=(c,a),c^p=f^w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),a^p,
b^p=(c,a),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(b,a,b),(c,b)=(b,a,a),(d,a),(d,b),(d,c),a^p,
b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),
a^p=f,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),
a^p=f^w,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),
    a^p=f^w2,b^p=(c,a),c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),
    a^p=f^w3,b^p=(c,a),c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),a^p,
b^p=(c,a),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),a^p,
    b^p=(c,a),c^p=f^w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b),(d,c),a^p,
    b^p=(c,a),c^p=f^w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),(d,c),a^p,
b^p=(c,a),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),(d,c),a^p,
b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),(d,c),
a^p=f,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),(d,c),
a^p=f^w,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),(d,c),
    a^p=f^x,b^p=e*f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),(d,c),
    a^p=f^x,b^p=e*f^w,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),(d,c),a^p,
b^p=(c,a),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),(d,c),a^p,
    b^p=(c,a),c^p=f^w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),(d,c),a^p,
    b^p=(c,a),c^p=f^w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a)=f,(d,b),
(d,c),a^p,b^p=(c,a),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a)=f,(d,b),
(d,c),a^p,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a)=f,(d,b),
(d,c),a^p=f,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a)=f,(d,b),
(d,c),a^p=f^w,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a)=f,(d,b),
(d,c),a^p,b^p=(c,a),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+5;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a)=f,(d,b),
   (d,c),a^p,b^p=(c,a),c^p=f^w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a)=f,(d,b),
    (d,c),a^p,b^p=(c,a),c^p=f^w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),
    (d,c)=f,a^p,b^p=(c,a),c^p,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),
(d,c)=f,a^p=f,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),
(d,c)=f,a^p=f^w,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),
(d,c)=f,a^p,b^p=(c,a),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),
    (d,c)=f,a^p,b^p=(c,a),c^p=f^w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f|f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),
    (d,c)=f,a^p,b^p=(c,a),c^p=f^w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),
(d,c)=f,a^p,b^p=e*f,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b)=f,(c,b),(d,a),(d,b),
(d,c)=f,a^p,b^p=e*f^w,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;

vprint Orderp7, 1: "Group 6.23 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 3p + 41 + 8gcd(p-1,3) + 2gcd(p-1,4) =",
3*p+41+2*Gcd(p-1,4)+8*Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
