freeze;

import "misc.m": ProcessPresentation; 

Group6_507 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.507 is valid only for p>5"; return false; end if;

class:=6;

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

r:=(F!7)*(F!6)^-1; r:=Integers()!r;
s:=(F!4)^-1; s:=Integers()!s;
t:=(F!29)*(F!12)^-1; t:=Integers()!t;
u:=(F!w)+(F!17)*(F!12)^-1; u:=Integers()!u;

L:=[]; Nmr := 0;
count:=0;
for x in [0..p-1] do
  v:=(r*x+s) mod p;
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(d,a),(b,a,b)=c*d^-1*e^v, 
                           (c,b)=e^x, a^p, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(d,a),(b,a,b)=c*d^-1*e^v, 
                     (c,b)=e^x, a^p=e, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(d,a),(b,a,b)=c*d^-1*e^v, 
                     (c,b)=e^x, a^p=e^w, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
  if p mod 3 eq 1 then
    for y in [w2,w3,w4,w5] do
      count:=count+1;
      GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(d,a),(b,a,b)=c*d^-1*e^v, 
                       (c,b)=e^x, a^p=e^y, b^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end for;
  end if;
  if p mod 5 ne 1 then
    for y in [0..p-1] do
      count:=count+1;
      GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(d,a),(b,a,b)=c*d^-1*e^v, 
       (c,b)=e^x, a^p=e^y, b^p=e>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end for;
  else;
    for i in [2..p-1] do
      if i^5 mod p eq 1 then FI:=i; break; end if;
    end for;
    for y in [0..p-1] do
      y1:=(FI*y) mod p; y2:=(FI*y1) mod p; y3:=(FI*y2) mod p; y4:=(FI*y3) mod p;
      if y le y1 and y le y2 and y le y3 and y le y4 then
        for z in [1,w,w2,w3,w4] do
          count:=count+1;
          GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(d,a),(b,a,b)=c*d^-1*e^v, 
           (c,b)=e^x, a^p=e^y, b^p=e^z>;
          ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        end for;
      end if;
    end for;
  end if;
end for;

for x in [0..p-1] do
for y in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(d,a),(b,a,b)=c*d^-1*e^t, 
     (c,b)=e, a^p=e^x, b^p=e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=(b,a,a,a),d=(c,a),e=(d,a),(b,a,b)=c*d^-1*e^u, 
     (c,b)=e, a^p=e^x, b^p=e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end for;

vprint Orderp7, 1: "Group 6.507 has",count,"descendants of order p^7 and p-class 6";

vprint Orderp7, 2: "Total number of groups is 2p^2 + p + 2pgcd(p-1,3) + pgcd(p-1,5) =",
2*p^2+p+2*p*Gcd(p-1,3)+p*Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;
