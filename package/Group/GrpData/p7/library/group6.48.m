freeze;

import "misc.m": ProcessPresentation; 

Group6_48 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.48 valid only for p>3"; return false; end if;

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
r:=(p+1) div 2;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c),a^p,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c),a^p,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c),a^p=f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c),a^p,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c),a^p,b^p=f^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=f,(d,a),
(d,b)=e,(d,c),a^p,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=f,(d,a),
(d,b)=e,(d,c),a^p,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=f,(d,a),
(d,b)=e,(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=f,(d,a),
(d,b)=e,(d,c),a^p=f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=f,(d,a),
(d,b)=e,(d,c),a^p,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b)=f,(d,a),
(d,b)=e,(d,c),a^p,b^p=f^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c)=f,a^p,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=13;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
   (d,c)=f,a^p,b^p,c^p=f^w,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
   (d,c)=f,a^p,b^p,c^p=f^w2,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=15;
end if;
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c)=f,a^p=f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c)=f,a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c)=f,a^p,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c)=f,a^p,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c)=f,a^p,b^p=f,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c)=f,a^p,b^p=f^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
(d,c)=f,a^p,b^p=f^w,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+7;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
   (d,c)=f,a^p,b^p=f^w2,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
   (d,c)=f,a^p,b^p=f^w2,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
   (d,c)=f,a^p,b^p=f^w3,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,a),(b,a,b),(b,a,c),(b,a,d),(c,b),(d,a),(d,b)=e,
   (d,c)=f,a^p,b^p=f^w3,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;

GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b),(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b),(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b),(d,a),
(d,b)=e*f^r,(d,c),a^p=f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b),(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b),(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b),(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b),(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p=f,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
(d,b)=e*f^r,(d,c),a^p=f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
(d,b)=e*f^r,(d,c),a^p,b^p=f,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+14;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
   (d,b)=e*f^r,(d,c),a^p,b^p,c^p,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
   (d,b)=e*f^r,(d,c),a^p,b^p=f,c^p,d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
   (d,b)=e*f^r,(d,c),a^p,b^p,c^p,d^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(c,a),f=(b,a,d),(b,a,a),(b,a,b),(b,a,c),(c,b)=f,(d,a),
   (d,b)=e*f^r,(d,c),a^p,b^p=f,c^p,d^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
end if;

vprint Orderp7, 1: "Group 6.48 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 27+3gcd(p-1,3)+2gcd(p-1,4) =",
27+3*Gcd(p-1,3)+2*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
