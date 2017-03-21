freeze;

import "misc.m": ProcessPresentation; 

Group6_159 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.159 valid only for p>3"; return false; end if;

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

for x in [0..((p-1) div 2)] do
for y in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b,b),(c,a)=d*e^x, (c,b), a^p=d, b^p=d, c^p=e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
for x in [1..((p-1) div 2)] do
for y in [0..p-1] do
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b,b),(c,a)=d*e^x, (c,b), a^p=d*e^y, b^p=d*e^z, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
end for;
for y in [1..((p-1) div 2)] do
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b,b),(c,a)=d, (c,b), a^p=d*e^y, b^p=d*e^z, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
for z in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b,b),(c,a)=d, (c,b), a^p=d, b^p=d*e^z, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b,b),(c,a)=d, (c,b), a^p=d, b^p=d, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.159 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (p^3 + p^2)/2 =",
(p^3+p^2)/2;

if Process then return Nmr; else return L; end if;

end function;
