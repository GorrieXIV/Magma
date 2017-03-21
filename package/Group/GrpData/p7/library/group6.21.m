freeze;

import "misc.m": ProcessPresentation; 

Group6_21 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.21 valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(b,a),
c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(c,a,a),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(b,a),
c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f,
b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f^w,
b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=4;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f^x,
    b^p=(b,a),c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b),(d,c),a^p,
b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f,
b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f^w,
b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b),(d,c),a^p=f^x,
    b^p=e*f,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p,
    b^p=(b,a),c^p,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b),(d,c),a^p,
b^p=e*f,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b),(d,c),
a^p=f,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b),(d,c),
a^p=f^w,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b),(d,c),
    a^p=f^x,b^p=(b,a),c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),a^p,
b^p=(b,a),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),a^p,
b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),
a^p=f,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),
a^p=f^w,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),
    a^p=f^x,b^p=(b,a),c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=f,
    (d,c),a^p,b^p=(b,a),c^p,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=f,
(d,c),a^p,b^p=e*f,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=f,
(d,c),a^p,b^p=e*f^w,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=f,
(d,c),a^p=f,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=f,
(d,c),a^p=f^w,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=f,
    (d,c),a^p=f^x,b^p=(b,a),c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(b,a),
c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b),(d,c),a^p=f,
b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b),(d,c),a^p,b^p=(b,a),
    c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b),(d,c)=f,a^p,
b^p=(b,a),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b),(d,c)=f,
a^p=f,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b),(d,c)=f,a^p,
    b^p=(b,a),c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=f,(d,c),a^p,
    b^p=(b,a),c^p=f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=f,(d,c),
a^p=f,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=f,(d,c),a^p,
    b^p=(b,a),c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=f,
(d,c)=f,a^p,b^p=(b,a),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=f,
(d,c)=f,a^p=f,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=f,
    (d,c)=f,a^p,b^p=(b,a),c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b),(d,c),a^p,
b^p=(b,a),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b),(d,c),
a^p=f,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b),(d,c),a^p,
    b^p=(b,a),c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.21 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 13p+27 =",13*p+27;

if Process then return Nmr; else return L; end if;

end function;
