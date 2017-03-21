freeze;

import "misc.m": ProcessPresentation; 

Group6_34 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.34 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^w,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^w,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p=f,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f^w,b^p=f,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e*f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e*f^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e*f^-1,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e*f^(w-1),b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e*f,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
a^p=e*f^w,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=21;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p,c^p=f,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
if p mod 4 eq 3 then
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f^w,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f^w,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
end if;
if p mod 4 eq 1 then
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f^w,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f^w,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f^w2,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f^w2,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f^w3,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,c),(c,a,a),(c,b),(d,a)=f,(d,b)=e,(d,c),
    a^p=e*f^x,b^p=f^w3,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+8;
end for;
end if;

GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b),(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e*f,b^p=f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p=f,c^p=f^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e*f^-1,b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e*f^(w-1),b^p,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|e=(b,a),f=(c,a,a),(c,a,c),(c,b)=f,(d,a),(d,b)=e,(d,c),
a^p=e,b^p,c^p=f^w,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+21;

vprint Orderp7, 1: "Group 6.34 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 5p + 38 + 2gcd(p-1,4) =",
5*p+38+2*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
