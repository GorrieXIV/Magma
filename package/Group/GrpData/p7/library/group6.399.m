freeze;

import "misc.m": ProcessPresentation; 

Group6_399 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.399 is valid only for p>5"; return false; end if;

class:=5;

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
w5:=w^5 mod p;

r:=(p+3) div 2;
s:=(p+5) div 2;

SQ:={};
for i in [0..((p-1) div 2)] do
  Include(~SQ,(F!i)^2);
end for;
for i in [0..p-1] do
  if F!(i^2-4) notin SQ then m:=i; break; end if;
end for;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b),
             (b,a,b,b)=c^-1*d^r,a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b),
            (b,a,b,b)=c^-1*d^r,a^p=d,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b),
               (b,a,b,b)=c^-1*d^r,a^p=d^w,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
if p mod 8 eq 1 then
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b),
        (b,a,b,b)=c^-1*d^r,a^p=d^w2,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b),
        (b,a,b,b)=c^-1*d^r,a^p=d^w3,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b),
   (b,a,b,b)=c^-1*d^r,a^p=d^x,b^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b),
   (b,a,b,b)=c^-1*d^r,a^p=d^x,b^p=d^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
  if p mod 4 eq 1 then
    GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b),
     (b,a,b,b)=c^-1*d^r,a^p=d^x,b^p=d^w2>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b),
     (b,a,b,b)=c^-1*d^r,a^p=d^x,b^p=d^w3>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
for x in [0..((p-1) div 2)] do
for y in [0..p-1] do
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b)=d,
   (b,a,b,b)=c^-1*d^r,a^p=d^x,b^p=d^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b),
   (b,a,b,b)=c^-1*d^s,a^p=d^x,b^p=d^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end for;
for x in [1..((p-1) div 2)] do
for y in [0..p-1] do
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b),(b,a,a,b)=d^x,
   (b,a,b,b)=c^-1*d^s,a^p=d^y,b^p=d^z>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
end for;
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d,
                 (b,a,b,b)=c^-1,a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d,
                 (b,a,b,b)=c^-1,a^p,b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d,
                 (b,a,b,b)=c^-1,a^p,b^p=d^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d,
                    (b,a,b,b)=c^-1,a^p,b^p=d^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d,
                    (b,a,b,b)=c^-1,a^p,b^p=d^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d,
                 (b,a,b,b)=c^-1,a^p=d,b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d,
                 (b,a,b,b)=c^-1,a^p=d^w,b^p=d^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d,
                 (b,a,b,b)=c^-1,a^p=d,b^p=d^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
for y in [x..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d,
   (b,a,b,b)=c^-1*d,a^p=d^x,b^p=d^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
                  (b,a,b,b)=c^-1*d^2,a^p,b^p=d^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
        (b,a,b,b)=c^-1*d^2,a^p=d,b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
        (b,a,b,b)=c^-1*d^2,a^p=d^w,b^p=d^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
        (b,a,b,b)=c^-1*d^2,a^p=d,b^p=d^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
      (b,a,b,b)=c^-1*d^2,a^p=d^w,b^p=d^-w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
      (b,a,b,b)=c^-1*d^2,a^p=d^w2,b^p=d^-w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
                 (b,a,b,b)=c^-1*d^-2,a^p,b^p=d^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
    (b,a,b,b)=c^-1*d^-2,a^p=d,b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
    (b,a,b,b)=c^-1*d^-2,a^p=d^w,b^p=d^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  for x in [w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
     (b,a,b,b)=c^-1*d^-2,a^p=d^x,b^p=d^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
count:=count+1;
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
    (b,a,b,b)=c^-1*d^-2,a^p=d,b^p=d^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 5 eq 1 then
  for x in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
     (b,a,b,b)=c^-1*d^-2,a^p=d^x,b^p=d^-x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
for x in [0..p-1] do
for y in [x..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b)=d,(b,a,a,b)=d^2,
   (b,a,b,b)=c^-1*d^m,a^p=d^x,b^p=d^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;

vprint Orderp7, 1: "Group 6.399 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is (p^3+3p^2+8p+14+6gcd(p-1,3)+(p+3)gcd(p-1,4)+2gcd(p-1,5)+gcd(p-1,8))/2 =",
(p^3+3*p^2+8*p+14+6*Gcd(p-1,3)+(p+3)*Gcd(p-1,4)+2*Gcd(p-1,5)+Gcd(p-1,8))/2;

if Process then return Nmr; else return L; end if;

end function;
