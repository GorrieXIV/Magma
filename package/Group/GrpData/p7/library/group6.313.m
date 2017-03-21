freeze;

import "misc.m": ProcessPresentation; 

Group6_313 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.313 valid only for p>3"; return false; end if;
 
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
w4:=w^4 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), a^p, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), a^p, b^p=(c,a), 
                      c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), a^p, b^p=(c,a), 
                      c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), a^p, b^p=(c,a), 
                        c^p=e^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), a^p, b^p=(c,a), 
                        c^p=e^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=5;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), a^p=e, 
                          b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
FI:=1;
if p mod 5 eq 1 then
  for i in [2..p-1] do
    if i^5 mod p eq 1 then FI:=i; break; end if;
  end for;
  for y in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), a^p=e^y, 
                              b^p=(c,a), c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  for x in [1..p-1] do
    x1:=(FI*x) mod p; x2:=(FI*x1) mod p; x3:=(FI*x2) mod p; x4:=(FI*x3) mod p;
    if x le x1 and x le x2 and x le x3 and x le x4 then
      for y in [1,w,w2,w3,w4] do
        count:=count+1;
        GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), a^p=e^y, 
                                  b^p=(c,a), c^p=e^x>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
else;
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), a^p=e, 
                              b^p=(c,a), c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;

vprint Orderp7, 1: "Group 6.313 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p + gcd(p-1,4) + gcd(p-1,5) =",
p+Gcd(p-1,4)+Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;
