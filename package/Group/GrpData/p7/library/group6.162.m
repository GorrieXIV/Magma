freeze;

import "misc.m": ProcessPresentation; 

Group6_162 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.162 valid only for p>3"; return false; end if;

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
r:=(F!(w-1))*(F!(2*w))^-1; r:=Z!r; r:=p-r;
s:=(F!(2*w))^-1; s:=Z!s; s:=p-s;
u:=(F!w)^-1; u:=Z!u; u:=p-u;
v:=(F!2)*(F!w)^-1; v:=Z!v;

L:=[]; Nmr := 0;
count:=0;

for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=d*f^r, (c,b), 
                     a^p=d*e^w*f^r, b^p=e^-1*f^s, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..((p-1) div 2)] do
  t:=(F!x)-(F!(2*w))^-1; t:=Z!t;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=d*f^r, (c,b), 
                     a^p=d*e^w*f^r, b^p=e^-1*f^t, c^p=f^u>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=d*f^r, (c,b), 
                     a^p=d*e^w*f^r, b^p=e^-1*f^t, c^p=f^v>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;

vprint Orderp7, 1: "Group 6.162 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 2p - 1 =",2*p-1;

if Process then return Nmr; else return L; end if;

end function;
