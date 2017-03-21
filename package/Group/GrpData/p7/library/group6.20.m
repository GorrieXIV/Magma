freeze;

import "misc.m": ProcessPresentation; 

Group6_20 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.20 valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d|(c,b),(d,a),(d,b),(d,c),(c,a,a),a^p=(b,a),b^p,
c^p,d^p=(c,a,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(c,b),(d,a),(d,b),(d,c),(c,a,a),a^p=(b,a),
b^p=(c,a,c),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(c,b),(d,a),(d,b),(d,c),(c,a,a),a^p=(b,a),b^p,
c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(c,b),(d,a),(d,b),(d,c),(c,a,a),a^p=(b,a),b^p,
c^p=(c,a,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,b),(d,a),(d,b),(d,c),(c,a,a),
a^p=e*f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,b),(d,a),(d,b),(d,c),(c,a,a),
a^p=e*f,b^p,c^p=(c,a,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,b),(d,a),(d,b),(d,c),(c,a,a),
a^p=e*f^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,b),(d,a),(d,b),(d,c),(c,a,a),
a^p=e*f^w,b^p,c^p=(c,a,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(c,b),(d,a)=(c,a,c),(d,b),(d,c),(c,a,a),
a^p=(b,a),b^p,c^p,d^p=(c,a,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(c,b),(d,a)=(c,a,c),(d,b),(d,c),(c,a,a),
a^p=(b,a),b^p=(c,a,c),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(c,b),(d,a)=(c,a,c),(d,b),(d,c),(c,a,a),
a^p=(b,a),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(c,b),(d,a)=(c,a,c),(d,b),(d,c),(c,a,a),
a^p=(b,a),b^p,c^p=(c,a,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,b),(d,a),(d,b)=f,(d,c),(c,a,a),
a^p=(b,a),b^p,c^p,d^p=f^x>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=12+p;
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,b),(d,a),(d,b)=f,(d,c),(c,a,a),
a^p=(b,a),b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,c),(c,b),(d,a),(d,b)=f,(d,c),(c,a,a),
a^p=(b,a),b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,b),(d,a),(d,b)=(c,a,c),(d,c),(c,a,a),
a^p=e*f,b^p,c^p,d^p=f^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,b),(d,a),(d,b)=f,(d,c),(c,a,a),
a^p=e*f^w,b^p,c^p,d^p=f^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;

for x in [0..p-1] do
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),(c,a,c),
a^p=(b,a),b^p,c^p,d^p=f^x>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),(c,a,c),
a^p=(b,a),b^p,c^p=f,d^p=f^x>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),(c,a,c),
a^p=(b,a),b^p,c^p=f^w,d^p=f^x>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
end for;
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),(c,a,c),
a^p=(b,a),b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),(c,a,c),
a^p=(b,a),b^p=f,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b)=f,(d,c),(c,a,c),
a^p=(b,a),b^p=f,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c)=f,(c,a,c),
a^p=(b,a),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c)=f,(c,a,c),
a^p=(b,a),b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c)=f,(c,a,c),
a^p=(b,a),b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c)=f,(c,a,c),
a^p=(b,a),b^p=f,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c)=f,(c,a,c),
a^p=(b,a),b^p=f^w,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c)=f,(c,a,c),
a^p=(b,a),b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c)=f,(c,a,c),
a^p=(b,a),b^p,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b)=f,(d,a),(d,b),(d,c),(c,a,c),
a^p=(b,a),b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+11;
for x in [0..p-1] do
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b)=f,(d,a),(d,b),(d,c),(c,a,c),
a^p=(b,a),b^p,c^p=f^x,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b)=f,(d,a),(d,b),(d,c),(c,a,c),
a^p=(b,a),b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b)=f^w,(d,a),(d,b),(d,c),(c,a,c),
a^p=(b,a),b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b)=f^w,(d,a),(d,b),(d,c),(c,a,c),
a^p=(b,a),b^p,c^p=f^x,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b)=f^w,(d,a),(d,b),(d,c),(c,a,c),
a^p=(b,a),b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c),(c,a,c),a^p=(b,a),b^p,
c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c),(c,a,c),a^p=(b,a),b^p,
c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c),(c,a,c),a^p=(b,a),
b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c),(c,a,c),a^p=(b,a),b^p,
c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f|f=(c,a,a),(c,b),(d,a),(d,b),(d,c),(c,a,c),a^p=(b,a),b^p,
c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;

vprint Orderp7, 1: "Group 6.20 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 6p+35 =",6*p+35;

if Process then return Nmr; else return L; end if;

end function;
