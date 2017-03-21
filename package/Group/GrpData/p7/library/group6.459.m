freeze;

import "misc.m": ProcessPresentation; 

Group6_459 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.459 is valid only for p>5"; return false; end if;

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
s:=(7*r) mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,b),(d,a), (b,a,a)=d*e^-1, c^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,b),(d,a), (b,a,a)=d*e^-1, 
                    c^p=e, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,b),(d,a), (b,a,a)=d*e^-1, 
                    c^p=e^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,b),(d,a), (b,a,a)=d*e^-1, 
                      c^p=e^w2, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,b),(d,a), (b,a,a)=d*e^-1, 
                      c^p=e^w3, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=5;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,b),(d,a), (b,a,a)=d*e^-1, c^p, 
                        b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 5 eq 1 then
  for x in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,b),(d,a), (b,a,a)=d*e^-1, c^p, 
                            b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,b),(d,a), (b,a,a)=d, 
                          c^p=e^x, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,b),(d,a), (b,a,a)=d, c^p, 
                          b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(d,b), (b,a,a)=d*e^s, 
                          c^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(d,b), (b,a,a)=d*e^s, 
                          c^p=e, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 5 eq 1 then
  for x in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(d,b), (b,a,a)=d*e^s, 
                            c^p=e^x, b^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(d,b), (b,a,a)=d*e^s, c^p, 
                          b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(d,b), (b,a,a)=d*e^s, c^p, 
                          b^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  for x in [w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(d,b), (b,a,a)=d*e^s, c^p, 
                            b^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(d,b)=e, 
        (b,a,a)=d*e^r, c^p=e^x, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(d,b)=e, 
      (b,a,a)=d*e^r, c^p, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.459 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 4p +2 gcd(p-1,3) + gcd(p-1,4) + 2gcd(p-1,5) =",
4*p+2*Gcd(p-1,3)+Gcd(p-1,4)+2*Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;
