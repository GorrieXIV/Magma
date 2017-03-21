freeze;

import "misc.m": ProcessPresentation; 

Group6_51 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.51 valid only for p>3"; return false; end if;

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

w2:=w^2 mod p;
w3:=w^3 mod p;
w4:=w^4 mod p;
CU:={};
T3:={};
for x in [1..p-1] do
  y:=x^3 mod p;
  if y notin CU then
    Include(~CU,y);
    Include(~T3,x);
  end if;
end for;
T3p:=T3;
Include(~T3p,0);

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=e,b^p,c^p,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=e,b^p,c^p=f,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=e,b^p,c^p,d^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=e,b^p,c^p=f,d^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=7;
end if;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^w,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
//print count,7+2*Gcd(p-1,3);
count1:=count;
for x in T3p do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e,b^p,c^p=f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 3 eq 1 then
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
     a^p=e,b^p,c^p=f^x,d^p=f^w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
     a^p=e,b^p,c^p=f^x,d^p=f^w2>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end if;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 5 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e,b^p,c^p=f^w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e,b^p,c^p=f^w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e,b^p,c^p=f^w3,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e,b^p,c^p=f^w4,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
if p mod 4 eq 1 then
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=f^w,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=f^w2,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=f^w3,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
end if;
if p mod 4 eq 3 then
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=e*f^x,b^p=f^w,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end if;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e*f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e*f^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
//print count-count1,3*p+Gcd(p-1,3)+Gcd(p-1,4)+Gcd(p-1,5);
count1:=count;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e,b^p,c^p,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e,b^p,c^p=f,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p=e,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for y in T3 do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e*f^y,b^p,c^p,d^p=f^-1>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e*f^y,b^p,c^p=f,d^p=f^-1>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
if p mod 3 eq 1 then
  for x in [0..p-1] do
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
     a^p=e,b^p,c^p,d^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
     a^p=e,b^p,c^p=f,d^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
   a^p=e,b^p=f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  for y in T3 do
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
     a^p=e*f^y,b^p,c^p,d^p=f^-w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
     a^p=e*f^y,b^p,c^p=f,d^p=f^-w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
  for x in [0..p-1] do
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,
     (d,c)=f^w2,a^p=e,b^p,c^p,d^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,
     (d,c)=f^w2,a^p=e,b^p,c^p=f,d^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,
   (d,c)=f^w2,a^p=e,b^p=f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  for y in T3 do
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,
     (d,c)=f^w2,a^p=e*f^y,b^p,c^p,d^p=f^-w2>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f^w2,
     a^p=e*f^y,b^p,c^p=f,d^p=f^-w2>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
end if;
//print count-count1,2*p-2+(2*p+1)*Gcd(p-1,3);
count1:=count;

GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
//print count-count1,6;
count1:=count;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p=e,b^p,c^p,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p=e,b^p=f^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p=f^-1,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f^w,(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f^w,(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f^w,(d,a),(d,b)=e,(d,c),
   a^p=e,b^p,c^p,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f^w,(d,a),(d,b)=e,(d,c),
   a^p=e,b^p=f^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f^w,(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p=f^-w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,2*p+4+Gcd(p-1,4);
count1:=count;
count:=count+1;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e,b^p,c^p=f^w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e,b^p,c^p=f^w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e,b^p,c^p,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e,b^p=f,c^p,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=e,b^p=f^w,c^p,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
  if p mod 4 eq 1 then
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
     a^p=e,b^p=f^w2,c^p,d^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
     a^p=e,b^p=f^w3,c^p,d^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
//print count-count1,p+Gcd(p-1,3)+p*Gcd(p-1,4);

vprint Orderp7, 1: "Group 6.51 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 8p+15+(2p+5)gcd(p-1,3)+(p+2)gcd(p-1,4)+gcd(p-1,5) =",
8*p+15+(2*p+5)*Gcd(p-1,3)+(p+2)*Gcd(p-1,4)+Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;
