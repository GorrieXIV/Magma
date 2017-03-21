freeze;

import "misc.m": ProcessPresentation; 

Group6_36 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.36 valid only for p>3"; return false; end if;

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

T4:={};
FO:={};
for x in [0..p-1] do
  y:=x^4 mod p;
  if y notin FO then
    Include(~T4,x);
    Include(~FO,y);
  end if;
end for;
w2:=w^2 mod p;
w3:=w^3 mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^w,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e*f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e*f^w,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^-1,b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^(w-1),b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p=e,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^w,b^p=e,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e*f,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e*f^w,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e,c^p=f,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
end for;
//print count,5*p+9;
count1:=count;

if p mod 4 eq 3 then
for x in [0..p-1] do
for y in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^x,b^p=e,c^p=f^y,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^x,b^p=e,c^p=f^y,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end for;
end if;
if p mod 4 eq 1 then
for x in [0..p-1] do
for y in [0..((p-1) div 2)] do
if x lt (p-x) mod p then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^x,b^p=e,c^p=f^y,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
if x lt (p-x+2*(1+(p-1)*w)) mod p then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^x,b^p=e,c^p=f^y,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
if x lt (p-x+2*(1+(p-1)*w2)) mod p then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^x,b^p=e,c^p=f^y,d^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
if x lt (p-x+2*(1+(p-1)*w3)) mod p then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^x,b^p=e,c^p=f^y,d^p=f^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
end for;
end for;
for y in T4 do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e,b^p=e,c^p=f^y,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^(1-w),b^p=e,c^p=f^y,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^(1-w2),b^p=e,c^p=f^y,d^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^(1-w3),b^p=e,c^p=f^y,d^p=f^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
end if;
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
a^p=e*f,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
a^p=e*f,b^p=e*f,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f,b^p=e*f,c^p=f^w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f,b^p=e*f,c^p=f^w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
//print count;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f,b^p=e*f^2,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f,b^p=e*f^(w+1),c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
for x in [0..p-1] do
for y in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^2,b^p=e*f^x,c^p=f^y,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e*f,(d,c),
   a^p=e*f^(w+1),b^p=e*f^x,c^p=f^y,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end for;
//print count-count1,2*p^2+3*p+Gcd(p-1,3)+Gcd(p-1,4);
count1:=count;

for x in [0..p-1] do
for y in [0..p-1] do
for z in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e*f^y,c^p=f^z,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
end for;
end for;
for x in [0..p-1] do
for y in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e*f^y,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e*f^y,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end for;
//print count-count1,p^2*(p+5)/2;
count1:=count;

for x in [0..p-1] do
for y in [0..p-1] do
for z in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f^w,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e*f^y,c^p=f^z,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
end for;
end for;
for x in [0..p-1] do
for y in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f^w,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e*f^y,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f^w,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e*f^y,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end for;
//print count-count1,p^2*(p+5)/2;
count1:=count;

GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=e*f,b^p=e*f^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^-1,b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e*f,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e*f,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e,c^p=f,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e,c^p=f^w,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count+8-count1,p+10;
count1:=count+8;

GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+10;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
    a^p=e*f,b^p=e*f^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
for x in [1..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p=e,b^p=e,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p=e,b^p=e*f,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p=e*f^x,b^p=e,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
for x in [1..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p=e,b^p=e,c^p=f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
//print count-count1,5*p-1;
count1:=count;

GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p=e,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e*f,b^p=e*f^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
for x in [1..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e,b^p=e,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e,b^p=e*f,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
for x in [1..((p-1) div 2)] do
for y in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e*f^y,b^p=e*f^x,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
end for;
for y in [-1..((p-3) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e*f^y,b^p=e,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
for x in [1..p-1] do
for y in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e,b^p=e*f^y,c^p=f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
end for;
//print count-count1,p^2+3*p;
count1:=count;

GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
a^p=e,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
   a^p=e*f,b^p=e*f^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
for x in [1..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
   a^p=e,b^p=e,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
   a^p=e,b^p=e*f,c^p=f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
for x in [1..((p-1) div 2)] do
for y in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
   a^p=e*f^y,b^p=e*f^x,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
end for;
for y in [-1..((p-3) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
   a^p=e*f^y,b^p=e,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
for x in [1..p-1] do
for y in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
   a^p=e,b^p=e*f^y,c^p=f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+1;
end for;
end for;
//print count-count1,p^2+3*p;

vprint Orderp7, 1: "Group 6.36 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is p^3+9p^2+20p+18+gcd(p-1,3)+gcd(p-1,4) =",
p^3+9*p^2+20*p+18+Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
