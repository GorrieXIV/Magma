freeze;

import "misc.m": ProcessPresentation; 

Group6_175 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.175 valid only for p>3"; return false; end if;

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
                            a^p=e^w*f^y, b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
for y in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=e, (c,b)=d^w*f^-w, 
                            a^p=e^w, b^p=f^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

for x in [1..p-1] do
for y in [0..((p-1) div 2)] do
for z in [1..((p-1) div 2)] do
  r:=(F!(-w*z-z^2))*(F!(2*w))^-1; r:=Z!r;
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|d=(b,a,a),e=(b,a,b),f=(d,a),g=(e,b),(c,a)=e*g^-1, 
                    (c,b)=d^w*f^-w, a^p=d^z*e^w*f^(y+r), b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
end for;
for y in [0..((p-1) div 2)] do
for z in [1..((p-1) div 2)] do
  r:=(F!(-w*z-z^2))*(F!(2*w))^-1; r:=Z!r;
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|d=(b,a,a),e=(b,a,b),f=(d,a),g=(e,b),(c,a)=e*g^-1, 
            (c,b)=d^w*f^-w, a^p=d^z*e^w*f^r, b^p=f^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;

vprint Orderp7, 1: "Group 6.175 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (p^3 + p^2 + p + 1)/4 =",
(p^3 + p^2 + p + 1)/4;

if Process then return Nmr; else return L; end if;

end function;

/*
Output from Baker-Campbell-Hausdorff
(b,a,a,a)^z*(b,a,a,b)^w = 1
(b,a,a,b)^z*(b,a,b,b)^w = 1
GR:=Group<a,b,c | (c,a)*(b,a,b)^-1*(b,a,b,b), (c,b)*(b,a,a)^-w*(b,a,a,a)^w, 
a^p*(b,a,a)^-z*(b,a,b)^-w*(b,a,a,a)^(-y+z)*(b,a,a,b)^(1/2*w+1/2*z)*(b,a,b,b)^w,
b^p, c^p*(b,a,a,a)^-x>;

GR:=Group<a,b,c | (c,a)*(b,a,b)^-1*(b,a,b,b), (c,b)*(b,a,a)^-w*(b,a,a,a)^w, 
a^p*(b,a,a)^-z*(b,a,b)^-w*(b,a,a,a)^z*(b,a,a,b)^(1/2*w+1/2*z)*(b,a,b,b)^w, 
b^p*(b,a,a,a)^-y, c^p>;
*/
