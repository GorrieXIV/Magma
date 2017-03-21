freeze;

import "misc.m": ProcessPresentation; 

Group6_408 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.408 is valid only for p>5"; return false; end if;

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

r:=(p+3) div 2;
s:=((p+3)*w) div 2; s:=s mod p;
t:=((p+3)*w^2) div 2; t:=t mod p;

L:=[]; Nmr := 0;
count:=0;

if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for y in [0..p-1] do
    y1:=(CU*y) mod p; y2:=(CU*y1) mod p;
    if y le y1 and y le y2 then
      for x in [0..((p-1) div 2)] do
        GR:=Group<a,b,c,d,e|c=(b,a,b),d=(b,a,a,a),e=(d,a),a^p=c*e^(x+1), 
                           b^p=d*e^(y-r)>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        GR:=Group<a,b,c,d,e|c=(b,a,b),d=(b,a,a,a),e=(d,a),a^p=c*e^(w+x), 
                           b^p=d^w*e^(y-s)>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        GR:=Group<a,b,c,d,e|c=(b,a,b),d=(b,a,a,a),e=(d,a),a^p=c*e^(w2+x), 
                           b^p=d^w2*e^(y-t)>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        count:=count+3;
      end for;
    end if;
  end for;
else;
  for x in [0..((p-1) div 2)] do
  for y in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|c=(b,a,b),d=(b,a,a,a),e=(d,a),a^p=c*e^(x+1),b^p=d*e^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  end for;
end if;

vprint Orderp7, 1: "Groups 6.408 - 6.410 have",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is (p + 1)(p - 1 + gcd(p-1,3))/2 =",
(p+1)*(p-1+Gcd(p-1,3))/2;

if Process then return Nmr; else return L; end if;

end function;
