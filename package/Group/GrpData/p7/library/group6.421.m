freeze;

import "misc.m": ProcessPresentation; 

Group6_421 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.420 is valid only for p>5"; return false; end if;

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

r:=(F!5)*(F!6)^-1; r:=Integers()!r;
w2:=w^2 mod p;

L:=[]; Nmr := 0;
count:=0;

if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [1..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
     for y in [0..p-1] do
      GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,b),(b,a,b,b,a), a^p=c*d*e^(x-1), 
                         b^p=e^y>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,b),(b,a,b,b,a), a^p=c*d^w*e^(x-w), 
                         b^p=e^y>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,b),(b,a,b,b,a), a^p=c*d^w2*e^(x-w2),
                         b^p=e^y>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+3;
     end for;
    end if;
  end for;
  for x in [0..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,b),(b,a,b,b,a), a^p=c*d*e^-1, 
                         b^p=e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,b),(b,a,b,b,a), a^p=c*d^w*e^-w, 
                         b^p=e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,b),(b,a,b,b,a), a^p=c*d^w2*e^-w2, 
                         b^p=e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+3;
    end if;
  end for;

  for x in [0..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
     for y in [0..p-1] do
      GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,a),(b,a,b,b,b)=e^x, 
        a^p=c*d*e^(r-x), b^p=e^y>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      s:=F!(w*x-w)+(F!6)^-1; s:=Integers()!(-s);
      GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,a),(b,a,b,b,b)=e^x, 
        a^p=c*d^w*e^s, b^p=e^y>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      s:=F!(w2*x-w2)+(F!6)^-1; s:=Integers()!(-s);
      GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,a),(b,a,b,b,b)=e^x, 
        a^p=c*d^w2*e^s,b^p=e^y>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+3;
     end for;
    end if;
  end for;

else;
for x in [1..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,b),(b,a,b,b,a), a^p=c*d*e^(x-1), 
                   b^p=e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,b),(b,a,b,b,a), a^p=c*d*e^-1, 
                   b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

for x in [0..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|c=(b,a,a),d=(b,a,b,b),e=(d,a),(b,a,b,b,b)=e^x, 
          a^p=c*d*e^(r-x), b^p=e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
end if;

vprint Orderp7, 1: "Groups 6.421 - 6.423 have",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 2p^2 - p - 1 + (p+1)gcd (p-1,3) =",
2*p^2-p-1+(p+1)*Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
