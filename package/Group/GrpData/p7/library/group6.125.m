freeze;

import "misc.m": ProcessPresentation; 

Group6_125 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.125 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c,d,e,f | d=(b,a,a)^-w,e=(b,a,b)^-1,f=(b,a,a,a),(c,a),(c,b),a^p=e*f^-w,
                      b^p=d*f^w,c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=1;
temp:=[0:j in [1..p]];
for x in [0..p-1] do
for y in [0..p-1] do
z:=y^2-w*x^2;
t:=F!z;
z:=1+Integers()!t;
if temp[z] eq 0 then
  temp[z]:=1;
  count:=count+1;
  z2:=(w+y) mod p; z3:=(p+x-w) mod p;
  GR:=Group<a,b,c,d,e,f | d=(b,a,a)^-w,e=(b,a,b)^-1,f=(b,a,a,a),(c,a),(c,b),a^p=e*f^z3,
                            b^p=d*f^z2,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
end for;
end for;

vprint Orderp7, 1: "Group 6.125 has",count,"descendants of order p^7 and class 4";

vprint Orderp7, 2: "Total number of groups is p + 1 =",p+1;

if Process then return Nmr; else return L; end if;

end function;
