freeze;

import "misc.m": ProcessPresentation; 

Group6_99 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.99 valid only for p>3"; return false; end if;

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

r:=(p-1) div 2;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e|d=(b,a),e=(c,a),(b,a,a), (c,a,a), (c,b), b^p=d*e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a),f=a^p,(b,a,a), (c,a,a), (c,b)=f^p, b^p=d*e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=a^p,g=f^p,(b,a,a),(c,a,a),(c,b)=g^w,b^p=d*e,c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=a^p,g=(e,a),(b,a,a),f^p,(c,b),b^p=d*e*g^r,c^p=e*g^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=a^p,g=(d,a),(c,a,a),f^p,(c,b),b^p=d*e*g^r,c^p=e*g^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.99 has",p+4,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is p+4 =",p+4;

if Process then return Nmr; else return L; end if;

end function;
