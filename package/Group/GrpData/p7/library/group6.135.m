freeze;

import "misc.m": ProcessPresentation; 

Group6_135 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.135 valid only for p>3"; return false; end if;

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

r:=(p-1) div 2;
s:=(p+1) div 2;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d | d=(b,a,b),(c,a)=d, (c,b), a^p, b^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b), a^p, b^p=d*e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b), a^p, b^p=d*e^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b), a^p, b^p=d*e^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b), a^p=e,
                            b^p=d*e^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
FI:=1;
if p mod 5 ne 1 then
  for x in [0..p-1] do
  for y in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e, a^p=e^x,
                              b^p=d*e^y, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  end for;
else;
  for i in [2..p-1] do
    if i^5 mod p eq 1 then FI:=i; break; end if;
  end for;
  for z in [1,w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e^z, a^p, b^p=d, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    for x in [1..p-1] do
      x1:=(FI*x) mod p; x2:=(FI*x1) mod p; x3:=(FI*x2) mod p; x4:=(FI*x3) mod p;
      if x le x1 and x le x2 and x le x3 and x le x4 then
        count:=count+1;
        GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e^z, a^p, 
                                  b^p=d*e^x, c^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        for y in [0..p-1] do
          count:=count+1;
          GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e^z, a^p=e^x, 
                                    b^p=d*e^y, c^p>;
          ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        end for;
      end if;
    end for;
  end for;
end if;
QU:=1;
if p mod 4 eq 3 then
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b), a^p, b^p=d, 
                              c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b), a^p, b^p=d, 
                              c^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
  for x in [1..((p-1) div 2)] do
    GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e^x, a^p, b^p=d, 
                                c^p=e>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e^x, a^p, b^p=d, 
                                c^p=e^w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
else;
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for z in [1,w,w2,w3] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b), a^p, b^p=d, 
                              c^p=e^z>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    for x in [1..((p-1) div 2)] do
      x1:=(QU*x) mod p; x2:=p-x1;
      if x le x1 and x le x2 then
        count:=count+1;
        GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e^x, a^p, b^p=d, 
                                  c^p=e^z>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end if;
    end for;
  end for;
end if;

GR:=Group<a,b,c,d,e,f | d=(b,a,b),e=(b,a,a)^-1,f=(b,a,a,b),(c,a)=d, (c,b), a^p=e*f^s, 
                            b^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a,b),e=(b,a,a)^-1,f=(b,a,a,b),(c,a)=d, (c,b), a^p=e*f^s, 
                            b^p=d*f^s, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a,b),e=(b,a,a)^-1,f=(b,a,a,b),(c,a)=d, (c,b), a^p=e*f^s, 
                            b^p=d*f^r, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a,b),e=(b,a,a)^-1,f=(b,a,a,b),(c,a)=d, (c,b), a^p=e*f^s, 
                            b^p=d*f^r, c^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;

vprint Orderp7, 1: "Group 6.135 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p^2 + 2p + 3 + gcd(p-1,3) + gcd(p-1,4) + gcd(p-1,5) =",
p^2+2*p+3+Gcd(p-1,3)+Gcd(p-1,4)+Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;
