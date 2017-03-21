freeze;

import "misc.m": ProcessPresentation; 

Group6_368 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.368 is valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;

GR:=Group<a,b,c|c=a^p,(b,a,a,a),(b,a,a,b),c^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a),(b,a,a,b),c^p,b^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a),(b,a,a,b),c^p=(b,a,b,b),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c|c=a^p,(b,a,a,a),(b,a,a,b),c^p=(b,a,b,b)^w,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,a),(b,a,a,b),c^p=(b,a,b,b)^w2,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=5;
end if;
GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a),c^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a),c^p,b^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a),c^p,b^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a),c^p,b^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a),c^p=(b,a,a,a),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a),c^p=(b,a,a,a)^w,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a),c^p=(b,a,a,a)^w2,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a)^w,c^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a)^w,c^p,b^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a)^w,c^p,b^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a)^w,c^p,b^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a)^w,c^p=(b,a,a,a),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a)^w,c^p=(b,a,a,a)^w,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b)=(b,a,a,a)^w,c^p=(b,a,a,a)^w2,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c|c=a^p,(b,a,a,a),(b,a,b,b),c^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a),(b,a,b,b),c^p,b^p=(b,a,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a),(b,a,b,b),c^p=(b,a,a,b),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b),c^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b),c^p,b^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+5;
if p mod 3 eq 1 then
  GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b),c^p,b^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b),c^p,b^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c|c=a^p,(b,a,a,b),(b,a,b,b),c^p=(b,a,a,a),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.368 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 9 + 6gcd(p-1,3) =",
9+6*Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
