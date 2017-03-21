freeze;

import "misc.m": ProcessPresentation; 

Group6_435 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.435 is valid only for p>5"; return false; end if;

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

r:=(F!6)^-1; r:=Integers()!r;

L:=[]; Nmr := 0;
GR:=Group<a,b,c|c=a^p,(b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, c^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
             c^p=(b,a,a,a,b), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
             c^p=(b,a,a,a,b)^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, c^p, 
             b^p=(b,a,a,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b), c^p=(b,a,a,a,a), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,b),(b,a,b)=(b,a,a,a,a),c^p=(b,a,a,a,a),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,b),(b,a,b)=(b,a,a,a,a)^w,c^p=(b,a,a,a,a),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=7;
if p mod 3 eq 1 then
  GR:=Group<a,b,c|c=a^p,(b,a,a,a,b),(b,a,b)=(b,a,a,a,a)^w2,c^p=(b,a,a,a,a),b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,a,b),(b,a,b)=(b,a,a,a,a)^w3,c^p=(b,a,a,a,a),b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,a,b),(b,a,b)=(b,a,a,a,a)^w4,c^p=(b,a,a,a,a),b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,a,b),(b,a,b)=(b,a,a,a,a)^w5,c^p=(b,a,a,a,a),b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b), c^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b)=(b,a,a,a,a), c^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b), c^p, b^p=(b,a,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b)=(b,a,a,a,a), c^p, 
                   b^p=(b,a,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b), c^p, b^p=(b,a,a,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b)=(b,a,a,a,a), c^p, 
                   b^p=(b,a,a,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
if p mod 4 eq 1 then
  GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b), c^p, b^p=(b,a,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b)=(b,a,a,a,a), c^p, 
                     b^p=(b,a,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b), c^p, b^p=(b,a,a,a,a)^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c|c=a^p,(b,a,a,a,b), (b,a,b)=(b,a,a,a,a), c^p, 
                     b^p=(b,a,a,a,a)^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;

vprint Orderp7, 1: "Group 6.435 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 7 + 2gcd(p-1,3) + 2gcd(p-1,4) =",
7+2*Gcd(p-1,3)+2*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
