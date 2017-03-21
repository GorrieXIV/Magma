freeze;

import "misc.m": ProcessPresentation; 

Group6_375 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.375 is valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c | c=a^p, c^p=(b,a,b)^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | c=a^p, c^p=(b,a,b)^w, b^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | c=a^p, c^p=(b,a,b)^w, b^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | c=a^p, c^p=(b,a,b)^w, b^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=4;
end if;
if p mod 4 eq 1 then
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for x in [0..((p-1) div 2)] do
    x1:=(QU*x) mod p; x2:=p-x1;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b)^w,e=(b,a,a,a),c^p=d*e, b^p=e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b)^w,e=(b,a,a,a),c^p=d*e^w, b^p=e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+2;
    end if;
  end for;
else;
  for x in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b)^w,e=(b,a,a,a),c^p=d*e, b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;

vprint Orderp7, 1: "Group 6.375 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (p+1)/2 + gcd(p-1,3) + gcd(p-1,4)/2 =",
(p+1)/2+Gcd(p-1,3)+Gcd(p-1,4)/2;

if Process then return Nmr; else return L; end if;

end function;
