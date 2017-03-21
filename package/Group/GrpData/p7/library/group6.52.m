freeze;

import "misc.m": ProcessPresentation; 

Group6_52 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.52 valid only for p>3"; return false; end if;

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
CU:={};
T3:={};
for x in [1..p-1] do
  y:=x^3 mod p;
  if y notin CU then
    Include(~CU,y);
    Include(~T3,x);
  end if;
end for;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),a^p,b^p,
c^p=e,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=f,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),a^p,
b^p=f,c^p=e*f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),a^p,b^p,
c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=f,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=f^w,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),a^p,b^p,
c^p=e*f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=f,b^p,c^p=e*f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=f^w,b^p,c^p=e*f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print 9,9;
count1:=9;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p,b^p,c^p=e,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=10;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p,b^p,c^p=e,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p,b^p,c^p=e,d^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=12;
end if;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p=f,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p=f^w,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=f^w2,b^p,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=f^w3,b^p,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p,b^p=f,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a),(d,b)=e,(d,c)=f,
a^p,b^p=f^w,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
//print count-count1,3+Gcd(p-1,3)+Gcd(p-1,4);
count1:=count;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p,b^p,c^p=e,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p+1;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p,b^p,c^p=e*f,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
   a^p=f^x,b^p=f,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=f,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=f^w,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
//print count-count1,2*p+3;
count1:=count;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f,a^p,b^p,c^p=e,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
for x in T3 do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f,a^p,b^p,c^p=e*f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f,a^p=f^x,b^p,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f,a^p,b^p=f^x,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
end for;
if p mod 3 eq 1 then
for x in [0..p-1] do
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
(d,c)=f^w,a^p,b^p,c^p=e,d^p=f^x>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
for x in T3 do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f^w,a^p,b^p,c^p=e*f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f^w,a^p=f^x,b^p,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f^w,a^p,b^p=f^x,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f^w2,a^p,b^p,c^p=e,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
for x in T3 do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f^w2,a^p,b^p,c^p=e*f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f^w2,a^p=f^x,b^p,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,b),(b,a,a),(c,b),(d,a)=f,(d,b)=e,
   (d,c)=f^w2,a^p,b^p=f^x,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
end for;
end if;
//print count-count1,3*p-3+p*Gcd(p-1,3);
count1:=count;

GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),a^p,b^p,
c^p=e,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),a^p,b^p,
c^p=e*f,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),a^p,
   b^p=f^x,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),a^p,
   b^p=f^x,c^p=e*f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=f,b^p=f^x,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c),
   a^p=f,b^p=f^x,c^p=e*f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
//print count-count1,4*p+2;
count1:=count;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p,b^p,c^p=e*f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p,b^p,c^p=e*f^x,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
for x in [0..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p=f^x,b^p=f^y,c^p=e*f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p,b^p=f^x,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b)=f,(d,a),(d,b)=e,(d,c),
   a^p=f,b^p=f^x,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
//print count-count1,p^2+3*p+1;
count1:=count;
for x in [0..((p-1) div 2)] do
for y in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p,b^p=f^y,c^p=e*f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p,b^p=f^y,c^p=e*f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f,
   a^p=f,b^p=f^y,c^p=e*f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
   a^p,b^p=f^y,c^p=e*f^x,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
   a^p,b^p=f^y,c^p=e*f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(c,b),(d,a),(d,b)=e,(d,c)=f^w,
   a^p=f,b^p=f^y,c^p=e*f^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+6;
end for;
end for;
//print count-count1,3*p*(p+1);

vprint Orderp7, 1: "Group 6.52 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 4p^2+15p+15+(p+1)gcd(p-1,3)+gcd(p-1,4) =",
4*p^2+15*p+15+(p+1)*Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
