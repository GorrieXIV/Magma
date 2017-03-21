freeze;

import "misc.m": ProcessPresentation; 

Group6_15 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.15 valid only for p>3"; return false; end if;

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
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=c^p,f=e^p,(c,a),(c,b)=f^x,(d,a),(d,b),(d,c),a^p=(b,a),b^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|e=c^p,f=e^p,(c,a)=f,(c,b),(d,a),(d,b),(d,c),a^p=(b,a),b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=c^p,f=e^p,(c,a),(c,b)=f^x,(d,a)=f,(d,b),(d,c),a^p=(b,a),b^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|e=c^p,f=e^p,(c,a),(c,b),(d,a),(d,b)=f,(d,c),a^p=(b,a),b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=e^p,(c,a)=f,(c,b),(d,a),(d,b)=f,(d,c),a^p=(b,a),b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=e^p,(c,a),(c,b),(d,a),(d,b),(d,c)=f,a^p=(b,a),b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=e^p,(c,a),(c,b),(d,a)=f,(d,b),(d,c)=f,a^p=(b,a),b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=c^p,f=e^p,(c,a),(c,b),(d,a),(d,b)=f,(d,c)=f,a^p=(b,a),b^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.15 has",2*p+6,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 2p+6 =",2*p+6;

if Process then return Nmr; else return L; end if;

end function;