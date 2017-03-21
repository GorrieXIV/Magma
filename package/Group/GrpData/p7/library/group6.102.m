freeze;

import "misc.m": ProcessPresentation; 

Group6_102 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.102 valid only for p>3"; return false; end if;

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
s:=(p+1) div 2;

L:=[]; Nmr := 0;

for x in [0..p-1] do
  GR:=Group<a,b,c,d,e | d=b^p,e=d^p,(b,a,a), (c,b)=e^x, a^p=(c,a), c^p=(b,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f,g | d=(b,a),e=(c,a),f=(d,a),g=b^p,g^p, (c,b), a^p=e*f^s, 
                       c^p=d*f^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | d=(b,a),e=(c,a),f=(d,a),g=b^p,g^p=f, (c,b), a^p=e*f^s, 
                       c^p=d*f^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | d=(b,a),e=(c,a),f=(d,a),g=b^p,g^p=f^w, (c,b), a^p=e*f^s, 
                       c^p=d*f^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.102 has",p+3,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is p + 3 =",p+3;

if Process then return Nmr; else return L; end if;

end function;
