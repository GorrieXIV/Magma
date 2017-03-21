freeze;

import "misc.m": ProcessPresentation; 

Group6_60 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.60 valid only for p>3"; return false; end if;

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
r:=((p-1) div 2)*w;
r:=r mod p;
SQ:={};
for x in [0..((p-1) div 2)] do
  y:=F!(x^2);
  Include(~SQ,y);
end for;
for y in [0..p-1] do
if F!(y^2-w) notin SQ then
  x:=y;
  break;
end if;
end for;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e,f,g|e=(b,a)^w,f=(c,a),g=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),
(d,b)=f*g^r,(d,c)=e*g^r,a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a)^w,f=(c,a),g=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),
(d,b)=f*g^r,(d,c)=e*g^r,a^p,b^p,c^p=g,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a)^w,f=(c,a),g=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),
(d,b)=f*g^r,(d,c)=e*g^r,a^p,b^p=g,c^p=g^x,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a)^w,f=(c,a),g=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),
(d,b)=f*g^r,(d,c)=e*g^r,a^p,b^p,c^p,d^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a)^w,f=(c,a),g=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=g,(d,a),
(d,b)=f*g^r,(d,c)=e*g^r,a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a)^w,f=(c,a),g=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=g,(d,a),
(d,b)=f*g^r,(d,c)=e*g^r,a^p,b^p,c^p=g,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a)^w,f=(c,a),g=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=g,(d,a),
(d,b)=f*g^r,(d,c)=e*g^r,a^p,b^p=g,c^p=g^x,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a)^w,f=(c,a),g=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=g,(d,a),
(d,b)=f*g^r,(d,c)=e*g^r,a^p,b^p,c^p,d^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=8;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f,g|e=(b,a)^w,f=(c,a),g=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=g,(d,a),
   (d,b)=f*g^r,(d,c)=e*g^r,a^p,b^p,c^p,d^p=g^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f,g|e=(b,a)^w,f=(c,a),g=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=g,(d,a),
   (d,b)=f*g^r,(d,c)=e*g^r,a^p,b^p,c^p,d^p=g^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=10;
end if;

vprint Orderp7, 1: "Group 6.60 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 7+gcd(p-1,3) =",7+Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
