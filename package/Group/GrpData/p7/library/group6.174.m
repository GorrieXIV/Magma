freeze;

import "misc.m": ProcessPresentation; 

Group6_174 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.174 valid only for p>3"; return false; end if;

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

Z:=Integers();

L:=[]; Nmr := 0;

count:=0;

for x in [1..((p-1) div 2)] do
for y in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=e, (c,b)=d^w*f^-w, 
                            a^p=e*f^y, b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
for y in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=e, (c,b)=d^w*f^-w, 
                            a^p=e, b^p=f^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

for x in [1..p-1] do
for y in [0..((p-1) div 2)] do
for z in [1..((p-1) div 2)] do
  z2:=z^2 mod p; z2:=p-z2;
  r:=(F!(-z-z^2))*(F!2)^-1; r:=Z!r;
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=e*f^z2, 
                    (c,b)=d^w*f^-w, a^p=d^z*e*f^(y+r), b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
end for;
for y in [0..((p-1) div 2)] do
for z in [1..((p-1) div 2)] do
  z2:=z^2 mod p; z2:=p-z2;
  r:=(F!(-z-z^2))*(F!2)^-1; r:=Z!r;
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=e*f^z2, 
            (c,b)=d^w*f^-w, a^p=d^z*e*f^r, b^p=f^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;

vprint Orderp7, 1: "Group 6.174 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (p^3 + p^2 + p + 1)/4 =",
(p^3+p^2+p+1)/4;

if Process then return Nmr; else return L; end if;

end function;
