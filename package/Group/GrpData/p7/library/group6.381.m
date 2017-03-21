freeze;

import "misc.m": ProcessPresentation; 

Group6_381 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.381 is valid only for p>3"; return false; end if;

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

w2:=w^2 mod p;
w3:=w^3 mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b | (b,a,a,a), (b,a,b), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=a^p,d=c^p,(b,a,a,a), (b,a,b)=d^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | c=a^p,d=c^p,e=d^p,(b,a,a,a), (b,a,b)=e^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p, (b,a,b), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p, (b,a,b)=(b,a,a,a), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p, (b,a,b), b^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p, (b,a,b)=(b,a,a,a), b^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=7;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p, (b,a,b), b^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p, (b,a,b)=(b,a,a,a), b^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p, (b,a,b), b^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p, (b,a,b)=(b,a,a,a), b^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=11;
end if;
GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p=(b,a,a,a), (b,a,b), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p=(b,a,a,a), (b,a,b)=(b,a,a,a), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p=(b,a,a,a), (b,a,b)=(b,a,a,a)^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p=(b,a,a,a), (b,a,b)=(b,a,a,a)^w2, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | c=a^p,d=c^p,d^p=(b,a,a,a), (b,a,b)=(b,a,a,a)^w3, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.381 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 6 + 2gcd(p-1,3) + gcd(p-1,4) =",
6+2*Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
