freeze;

import "misc.m": ProcessPresentation; 

Group6_411 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.411 is valid only for p>5"; return false; end if;

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

r:=(F!-6)^-1; r:=Integers()!r;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,b),(b,a,a,a,a), a^p=c*d^r, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,b),(b,a,a,a,a),a^p=c*d^r,b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,b),(b,a,a,a,a),a^p=c*d^r,b^p=d^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,b),(b,a,a,a,a),a^p=c*d^r,b^p=d^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=4;
end if;

GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,a),(b,a,a,a,b), a^p=c, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,a),(b,a,a,a,b), a^p=c*d, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,a),(b,a,a,a,b), a^p=c*d^w, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,a),(b,a,a,a,b), a^p=c*d^w2, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,a),(b,a,a,a,b),a^p=c,b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,a),(b,a,a,a,b),a^p=c,b^p=d^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,a),(b,a,a,a,b),a^p=c,b^p=d^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | c=(b,a,b),d=(b,a,a,a,a),(b,a,a,a,b),a^p=c,b^p=d^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.411 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 2 + 2gcd(p-1,3) + gcd(p-1,4) =",
2+2*Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
