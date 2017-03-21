freeze;

import "misc.m": ProcessPresentation; 

Group6_418 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.418 is valid only for p>5"; return false; end if;

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

r:=-(F!w)*(F!6)^-1+1; r:=Integers()!r;
s:=F!(5*w)*(F!6)^-1; s:=Integers()!s;
t:=-(F!2)*(F!w)^-1; t:=Integers()!t;
u:=(2*w) mod p; u:=p-u;

L:=[]; Nmr := 0;
count:=0;
QU:=0;

if p mod 4 eq 1 then
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for x in [0..((p-1) div 2)] do
    x1:=(QU*x) mod p; x2:=p-x1;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d,e|c=(b,a,b)^w,d=(b,a,a,a),e=(d,b),(b,a,a,a,a), a^p=c*d*e^r, 
                         b^p=e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=(b,a,b)^w,d=(b,a,a,a),e=(d,b),(b,a,a,a,a), a^p=c*d^w*e^s, 
                          b^p=e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+2;
    end if;
  end for;
else;
  for x in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|c=(b,a,b)^w,d=(b,a,a,a),e=(d,b),(b,a,a,a,a), a^p=c*d*e^r, 
                     b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;

for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|c=(b,a,b)^w,d=(b,a,a,a),e=(d,a),(b,a,a,a,b), a^p=c*d*e^-1, 
                   b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 4 eq 1 then
    count:=count+1;
    GR:=Group<a,b,c,d,e|c=(b,a,b)^w,d=(b,a,a,a),e=(d,a),(b,a,a,a,b), a^p=c*d^w*e^-w, 
                     b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end if;
end for;

if p mod 4 eq 1 then
  for x in [1..((p-1) div 2)] do
    x1:=(QU*x) mod p; x2:=p-x1;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d,e|c=(b,a,b)^w,d=(b,a,a,a),e=(d,a),(b,a,a,a,b), a^p=c*d*e^(x-1), 
                         b^p=e^t>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=(b,a,b)^w,d=(b,a,a,a),e=(d,a),(b,a,a,a,b), a^p=c*d^w*e^(x-w), 
                         b^p=e^u>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+2;
    end if;
  end for;
else;
  for x in [1..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|c=(b,a,b)^w,d=(b,a,a,a),e=(d,a),(b,a,a,a,b), a^p=c*d*e^(x-1), 
                     b^p=e^t>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;

vprint Orderp7, 1: "Groups 6.418 and 6.419 have",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is p - 1 + (p+1)gcd(p-1,4)/2 =",
p-1+(p+1)*Gcd(p-1,4)/2;

if Process then return Nmr; else return L; end if;

end function;
