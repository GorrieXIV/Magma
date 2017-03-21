freeze;

import "misc.m": ProcessPresentation; 

Group6_388 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.388 is valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b), (b,a)^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a), (b,a)^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b), (b,a)^p=(b,a,a,a), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a), (b,a)^p=(b,a,a,a), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b), (b,a)^p=(b,a,a,a)^w, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a), (b,a)^p=(b,a,a,a)^w, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b), (b,a)^p, c^p=(b,a,a,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a), (b,a)^p, c^p=(b,a,a,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a)^w, (b,a)^p, c^p=(b,a,a,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=9;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a)^w2, (b,a)^p, c^p=(b,a,a,a), d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a)^w3, (b,a)^p, c^p=(b,a,a,a), d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=11;
end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a)^x, (b,a)^p=(b,a,a,a), 
                     c^p=(b,a,a,a), d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a)^x, (b,a)^p=(b,a,a,a)^w, 
                     c^p=(b,a,a,a), d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [1,w,w2] do
    GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b), (b,a)^p, c^p, d^p=(b,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a), (b,a)^p, c^p, d^p=(b,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
    for y in [1..p-1] do
     y1:=(CU*y) mod p; y2:=(CU*y1) mod p;
     if y le y1 and y le y2 then
      GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b), (b,a)^p=(b,a,a,a)^y, c^p, d^p=(b,a,a,a)^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a), (b,a)^p=(b,a,a,a)^y, c^p, 
                         d^p=(b,a,a,a)^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+2;
     end if;
    end for;
  end for;
else;
  GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b), (b,a)^p, c^p, d^p=(b,a,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a), (b,a)^p, c^p, d^p=(b,a,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
  for y in [1..p-1] do
    GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b), (b,a)^p=(b,a,a,a)^y, c^p, d^p=(b,a,a,a)>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d|c=a^p,d=b^p,(b,a,b)=(b,a,a,a), (b,a)^p=(b,a,a,a)^y, c^p, 
                       d^p=(b,a,a,a)>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
end if;

vprint Orderp7, 1: "Group 6.388 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 4p + 5 + 2gcd(p-1,3) + gcd(p-1,4) =",
4*p+5+2*Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
