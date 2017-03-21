freeze;

import "misc.m": ProcessPresentation; 

Group6_290 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.290 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;
count:=0;

for x in [0..p-1] do
for y in [0..p-1] do
  GR:=Group<a,b,c,d,e | d=(c,a,a),e=(d,a),(c,b)=d*e^(x-1), (c,a,c), a^p, 
                              b^p=(b,a), c^p=e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(c,a,a),e=(d,a),(c,b)=d*e^-1, (c,a,c)=e, 
                              a^p=e^x, b^p=(b,a), c^p=e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(c,a,a),e=(d,a),(c,b)=d*e^(x-1), (c,a,c), 
                            a^p=e, b^p=(b,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.290 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 2p^2 + p =",2*p^2+p;

if Process then return Nmr; else return L; end if;

end function;
