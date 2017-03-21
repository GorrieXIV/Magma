freeze;

import "misc.m": ProcessPresentation; 

Group6_161 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.161 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;
count:=0;

for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=d, (c,b), a^p=d*e, 
                            b^p=e^-1*f^r, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f | d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=d, (c,b), a^p=d*e, 
                              b^p=e^-1*f^(r+x), c^p=f^-1>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=d, (c,b), a^p=d*e, 
                              b^p=e^-1*f^(r+x), c^p=f^2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;

vprint Orderp7, 1: "Group 6.161 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 2p - 1 =",2*p-1;

if Process then return Nmr; else return L; end if;

end function;
