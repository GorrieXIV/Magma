freeze;

import "misc.m": ProcessPresentation; 

Group6_101 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.101 valid only for p>3"; return false; end if;

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

SQ:={};
for x in [0..((p-1) div 2)] do
  Include(~SQ,x^2 mod p);
end for;

L:=[]; Nmr := 0;
count:=0;

for x in [1..p-1] do
  y:=(1+4*x) mod p;
  if y in SQ then continue; end if;
  GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a),(b,a,a), (c,a,a), (c,b), b^p=e^x, 
                              c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a),f=a^p,(b,a,a), (c,a,a), (c,b)=f^p, b^p=e^x, 
                              c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a),f=a^p,(b,a,a), f^p, (c,b), b^p=e^x, 
                              c^p=d*e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
end for;

vprint Orderp7, 1: "Group 6.101 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 3(p-1)/2 =",3*(p-1)/2;

if Process then return Nmr; else return L; end if;

end function;
