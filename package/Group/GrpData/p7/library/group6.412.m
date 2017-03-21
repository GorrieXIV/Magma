freeze;

import "misc.m": ProcessPresentation; 

Group6_412 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.412 is valid only for p>5"; return false; end if;

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

r:=-(F!6)^-1; r:=Integers()!r;
s:=(2*w^2) mod p; s:=p-s;

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
      GR:=Group<a,b,c,d,e | c=(b,a,b),d=(b,a,a,a),e=(d,b),(d,a), a^p=c*d*e^(r+1), 
                         b^p=e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e | c=(b,a,b),d=(b,a,a,a),e=(d,b),(d,a), a^p=c*d^w*e^(r+w), 
                          b^p=e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+2;
    end if;
  end for;
else;
  for x in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e | c=(b,a,b),d=(b,a,a,a),e=(d,b),(d,a), a^p=c*d*e^(r+1), 
                     b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;

for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | c=(b,a,b),d=(b,a,a,a),e=(d,a),(d,b), a^p=c*d*e^-1, 
                   b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 4 eq 1 then
    count:=count+1;
    GR:=Group<a,b,c,d,e | c=(b,a,b),d=(b,a,a,a),e=(d,a),(d,b), a^p=c*d^w*e^-w, 
                     b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end if;
end for;

if p mod 4 eq 1 then
  for x in [1..((p-1) div 2)] do
    x1:=(QU*x) mod p; x2:=p-x1;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d,e | c=(b,a,b),d=(b,a,a,a),e=(d,a),(d,b), a^p=c*d*e^(x-1), 
                         b^p=e^-2>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e | c=(b,a,b),d=(b,a,a,a),e=(d,a),(d,b), a^p=c*d^w*e^(x-w), 
                         b^p=e^s>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+2;
    end if;
  end for;
else;
  for x in [1..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e | c=(b,a,b),d=(b,a,a,a),e=(d,a),(d,b), a^p=c*d*e^(x-1), 
                     b^p=e^-2>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;

vprint Orderp7, 1: "Groups 6.412 and 6.413 have",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is p - 1 + (p+1)gcd(p-1,4)/2 =",
p-1+(p+1)*Gcd(p-1,4)/2;

if Process then return Nmr; else return L; end if;

end function;
