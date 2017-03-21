freeze;

import "misc.m": ProcessPresentation; 

Group6_118 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.118 valid only for p>3"; return false; end if;


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
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,a),(b,a,a,b),a^p,b^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,a),(b,a,a,b),a^p,b^p=(b,a,b,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,a),(b,a,a,b),a^p=(b,a,b,b),b^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,a),(b,a,a,b),a^p=(b,a,b,b)^w,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,a),(b,a,a,b),a^p=(b,a,b,b)^w2,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=5;
end if;
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,a),(b,a,a,b),a^p,b^p,c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|(c,a)=(b,a,b,b),(c,b),(b,a,a,a),(b,a,a,b),a^p,b^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|(c,a)=(b,a,b,b),(c,b),(b,a,a,a),(b,a,a,b),a^p,b^p=(b,a,b,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|(c,a)=(b,a,b,b),(c,b),(b,a,a,a),(b,a,a,b),a^p=(b,a,b,b),b^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c|(c,a)=(b,a,b,b),(c,b),(b,a,a,a),(b,a,a,b),a^p=(b,a,b,b)^w,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|(c,a)=(b,a,b,b),(c,b),(b,a,a,a),(b,a,a,b),a^p=(b,a,b,b)^w2,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c|(c,a)=(b,a,b,b),(c,b),(b,a,a,a),(b,a,a,b),a^p,b^p,c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-1,a^p,b^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-1,a^p,b^p=(b,a,a,a),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-1,a^p,b^p=(b,a,a,a)^w,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-1,a^p,b^p=(b,a,a,a)^w2,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-1,a^p=(b,a,a,a),b^p=(b,a,a,a),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-1,a^p,b^p,c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-w,a^p,b^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-w,a^p,b^p=(b,a,a,a),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-w,a^p,b^p=(b,a,a,a)^w,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-w,a^p,b^p=(b,a,a,a)^w2,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c|(c,a),(c,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a)^-w,a^p,b^p,c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.118 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 11+4gcd(p-1,3) =",
11+4*Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
