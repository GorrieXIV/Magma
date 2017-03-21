freeze;

import "misc.m": ProcessPresentation; 

Group6_148 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.148 valid only for p>3"; return false; end if;

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
SQ:={};
for i in [1..((p-1) div 2)] do
  Include(~SQ,i^2 mod p);
end for;
for i in [2..p-1] do
  if i notin SQ then lns:=i; break; end if;
end for;

L:=[]; Nmr := 0;
count:=0;

for x in [0,1,lns] do
for y in [0..p-1] do
for z in [0..p-1] do
for t in [0..p-1] do

new:=1;
index:=p^2*y+p*z+t;

for a in [1..p-1] do

x1:=Z!((F!a)^-2*(F!x));
if x1 ne x then continue; end if;
y1:=Z!((F!a)^-6*(F!y));
z1:=Z!((F!a)^-5*(F!z));
t1:=Z!((F!a)^-3*(F!t));

ind1:=p^2*y1+p*z1+t1;

if ind1 lt index then new:=0; break; end if;

end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^(x-1), (c,b), a^p=f^y,
                            b^p=f^z, c^p=d*f^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;

end for;
end for;
end for;
end for;

vprint Orderp7, 1: "Group 6.148 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p^3 + p^2 + p + (p+2)gcd(p-1,3) + gcd(p-1,5) =",
p^3+p^2+p+(p+2)*Gcd(p-1,3)+Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;
