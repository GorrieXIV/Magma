freeze;

import "misc.m": ProcessPresentation; 

Group6_122 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.122 valid only for p>3"; return false; end if;
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

r:=(p-1) div 2;
s:=(p+1) div 2;
t:=(p+3) div 2;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e,f | d=(b,a,a),e=(b,a,b)^-1,f=(b,a,a,b),(c,a), (c,b), a^p=d*f^r, 
                      b^p=e*f^s, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a,a),e=(b,a,b)^-1,f=(b,a,a,b),(c,a), (c,b), a^p=d*f^r, 
                      b^p=e*f^s, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a,a),e=(b,a,b)^-1,f=(b,a,a,b),(c,a), (c,b), a^p=d*f^r, 
                      b^p=e*f^t, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [1..p-1] do
  y:=(s+x) mod p;
  GR:=Group<a,b,c,d,e,f | d=(b,a,a),e=(b,a,b)^-1,f=(b,a,a,b),(c,a), (c,b), a^p=d*f^s, 
                          b^p=e*f^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=p+2;

vprint Orderp7, 1: "Group 6.122 has",count,"descendants of order p^7 and class 4";

vprint Orderp7, 2: "Total number of groups is p + 2 =",p+2;

if Process then return Nmr; else return L; end if;

end function;
