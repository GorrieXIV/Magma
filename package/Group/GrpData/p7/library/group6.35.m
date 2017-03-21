freeze;

import "misc.m": ProcessPresentation; 

Group6_35 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.35 valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=f,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=f,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=e,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=e,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=e*f,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=e*f,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=f^-1,b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=e,c^p=f,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=e,c^p=f^w,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=f,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=f,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p,b^p=e,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p,b^p=e,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p,b^p=e*f,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p,b^p=e*f,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p,b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=f^-1,b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p,b^p=e,c^p=f,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p,b^p=e,c^p=f^w,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=24;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
    a^p,b^p=e,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
    a^p,b^p=e,c^p=f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
    a^p,b^p=e*f,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
    a^p,b^p=e*f,c^p=f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p=f,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p=f,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p=f^-1,b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p=f^-1,b^p=e*f,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
for x in [1..((p-3) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
    a^p=f^x,b^p=e,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
    a^p=f^x,b^p=e*f,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
    a^p,b^p=e,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
    a^p,b^p=e,c^p=f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
    a^p,b^p=e*f,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
    a^p,b^p=e*f,c^p=f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
a^p=f,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
a^p=f,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
a^p=f^-1,b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
a^p=f^-1,b^p=e*f,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
for x in [1..((p-3) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
    a^p=f^x,b^p=e,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
    a^p=f^x,b^p=e*f,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;

vprint Orderp7, 1: "Group 6.35 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 10p + 26 =",10*p+26;

if Process then return Nmr; else return L; end if;

end function;
