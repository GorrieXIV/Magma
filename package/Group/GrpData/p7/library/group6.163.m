freeze;

import "misc.m": ProcessPresentation; 

Group6_163 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.163 valid only for p>3"; return false; end if;

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

SQ:={};
for i in [1..((p-1) div 2)] do
  Include(~SQ,i^2 mod p);
end for;
for i in [2..p-1] do
  if i notin SQ then lns:=i; break; end if;
end for;

Z:=Integers();

L:=[]; Nmr := 0;

/*
Baker-Campbell-Hausdorff gives:

GR[]:=Group<a,b,c | (c,a)*(b,a,a)^-1*(b,a,a,a)^-(u^-1*(-1/2*u+1/2)), (c,b), 
a^p*(b,a,a)^-1*(b,a,b)^-u*(b,a,a,a)^-(u^-1*(-u*x-1/2*u+1/2)), 
b^p*(b,a,a)^x*(b,a,b)*(b,a,a,a)^-(u^-1*(u*x+1/2*x-1/2)), c^p>;

GR[]:=Group<a,b,c | (c,a)*(b,a,a)^-1*(b,a,a,a)^(u^-2*(1/2*u^2-1/2*u)), (c,b), 
a^p*(b,a,a)^-1*(b,a,b)^-u*(b,a,a,a)^(u^-2*(1/2*u^2+1/2*u)), 
b^p*(b,a,a)^x*(b,a,b)^(u*x)*(b,a,a,a)^(u^-2*(-1/2*u^2*x-1/2*u*x)), c^p>;
*/

/*
Descendants of 6.163
<a,b,c|ca-baa,cb,pa-baa-ubab,pb+xbaa+bab,pc>
*/

gtotal:=0;
count:=0;
mats:=[];

//First get possible u,x for isomorphism classes of daddys
for u in [1,lns] do
uinv:=(F!u)^-1; uinv:=Z!uinv;
for x in [1..p-1] do

new:=1;
index:=p*u+x;

for a in [1..p-1] do
a1:=(F!a)^-1; a1:=Z!a1;

  u1:=(a^2*u) mod p;
  x1:=(a1^2*x) mod p;

if p*u1+x1 lt index then new:=0; break; end if;

  u1:=(a^2*x) mod p;
  x1:=(a1^2*u) mod p;

if p*u1+x1 lt index then new:=0; break; end if;

end for;

if new eq 1 then
  count:=count+1;
  //print u,x;
  Append(~mats,[u,x]);
end if;

end for;
end for;

//print count,3*(p-1)/2;
count:=0;

for A in mats do
u:=A[1]; x:=A[2];
uinv:=(F!u)^-1; uinv:=Z!uinv;

r:=(F!(1-u))*(F!(2*u))^-1; r:=Z!r;
s:=r-x;
s2:=(F!(x-1))*(F!(2*u))^-1+F!x; s2:=Z!s2;

for t in [0..p-1] do
for y in [0..p-1] do
for z in [0..p-1] do

new:=1;
index:=p^2*t+p*y+z;

//transformations of type (*)
for a in [1,p-1] do
for c in [0..p-1] do
for e in [0..p-1] do

if (u*x) mod p ne 1 or c eq (u*e) mod p then
  y1:=(e+c*uinv+a*y+c*t) mod p;
  z1:=F!(x*e-x*c*uinv-2*e*uinv+z*a+e*t); z1:=Z!z1;
  if p^2*t+p*y1+z1 lt index then new:=0; break; end if;
end if;

end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 0 then continue; end if;

//transformations of type (**)
for a in [1..p-1] do
  a1:=(F!a)^-1; a1:=Z!a1;
  u1:=(a^2*x) mod p;
  x1:=(a1^2*u) mod p;
  if u ne u1 or x ne x1 then continue; end if;
for c in [0..p-1] do
for e in [0..p-1] do

if (u*x) mod p ne 1 or c eq (u*e) mod p then
  y1:=-F!(x*c-x*a^2*e*uinv-2*c*uinv+z*a+c*t); y1:=Z!y1;
  z1:=-F!(c*a1^2+e*uinv+a1*y+e*t); z1:=Z!z1;
  t1:=F!(-t+uinv-x); t1:=Z!t1;
  if p^2*t1+p*y1+z1 lt index then new:=0; break; end if;
end if;

end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=d*f^r, (c,b), 
                            a^p=d*e^u*f^(s+y), b^p=d^-x*e^-1*f^(s2+z), c^p=f^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print u,x,y,z,t;
end if;

end for;
end for;
end for;
end for;

//print count,2*p^2-(5*p-1)/2;
gtotal:=count;

/*
Descendants of 6.163
second type
<a,b,c|ca-baa,cb,pa-baa-ubab,pb+xbaa+(u*x)bab,pc> u*x ne 1
*/

//First get possible u,x (i.e. m,n)
count:=0;
mats:=[];

for m in [1..p-1] do
for n in [1..p-1] do

if (m*n) mod p eq 1 then continue; end if;

new:=1;
index:=p*m+n;

for d in [1..p-1] do

d1:=(F!d)^-1; d1:=Z!d1;

m1:=(m*d1^2) mod p;
n1:=(n*d^2) mod p;

if p*m1+n1 lt index then new:=0; break; end if;

m1:=(n*d1^2) mod p;
n1:=F!(m*d^2)*(F!(m*n))^-2; n1:=Z!n1;

if p*m1+n1 lt index then new:=0; break; end if;

end for;

if new eq 1 then
  count:=count+1;
  Append(~mats,[m,n]);
  //print m,n;
end if;

end for;
end for;

//print count,p-3+Gcd(p-1,4)/2;

count:=0;

for A in mats do
u:=A[1]; x:=A[2];
ux:=(u*x) mod p;

r:=(F!(u-1))*(F!(2*u))^-1; r:=Z!r;
s:=(F!(u+1))*(F!(2*u))^-1; s:=Z!s;
s2:=(F!(-u*x-x))*(F!(2*u))^-1; s2:=Z!s2;

for t in [0..p-1] do
for y in [0..p-1] do
for z in [0..p-1] do

new:=1;
index:=p*y+z;

for a in [1,-1] do
for e in [0..p-1] do

y1:=F!(2*e+a*y+u*e*t); y1:=Z!y1;
z1:=F!(-2*x*e+a*z+e*t); z1:=Z!z1;
if p*y1+z1 lt index then new:=0; break; end if;

end for;
if new eq 0 then break; end if;
end for;

if new eq 1 and (u*x+1) mod p eq 0 and p mod 4 eq 1 then

  for a in [2..p-2] do
  if (a^2+1) mod p ne 0 then continue; end if;
  for e in [0..p-1] do

  y1:=-F!(2*e+z*a*u+u*e*t); y1:=Z!y1;
  z1:=F!(x*(2*e+a*y+u*e*t)); z1:=Z!z1;
  if p*y1+z1 lt index then new:=0; break; end if;

  end for;
  if new eq 0 then break; end if;
  end for;

end if;

if new eq 1 then
    count:=count+1;
    GR:=Group<a,b,c,d,e,f | d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=d*f^-r, (c,b), 
                         a^p=d*e^u*f^(y-s), b^p=d^-x*e^-(ux)*f^(z-s2), c^p=f^t>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    //print u,x,y,z,t;
end if;

end for;
end for;
end for;
end for;

//print count,(p^3-5*p+p*Gcd(p-1,4))/2;
gtotal:=gtotal+count;

vprint Orderp7, 1: "Groups 6.163 have",gtotal,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (p^3 + 4p^2 - 10p + 1 + pgcd(p-1,4))/2 =",
(p^3+4*p^2-10*p+1+p*Gcd(p-1,4))/2;

if Process then return Nmr; else return L; end if;

end function;
