freeze;

import "misc.m": ProcessPresentation; 

Group6_104 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.104 valid only for p>3"; return false; end if;

class:=3;

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
r:=F!(4)^-1; r:=Integers()!r;

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (b,a,b), (b,a,c), (c,a,a), (c,a,b), (c,a,c), (c,b,b), 
                     (c,b,c), a^p=(b,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d | d=(b,a,c),(b,a,a), (b,a,b), (c,a,a), (c,a,b)=d^-1, (c,a,c), 
                     (c,b,b), (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d^-1, 
                     (c,b,b), (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d^-w, 
                     (c,b,b), (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b), (c,a,c), (c,b,b), 
                     (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b), (c,a,c), (c,b,b), 
                     (c,b,c), a^p=d^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a)=d, (c,a,b), (c,a,c), 
                     (c,b,b), (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a)=d, (c,a,b), (c,a,c), 
                     (c,b,b), (c,b,c), a^p=d^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=8;
for x in [-1..p-3] do
  count:=count+1;
  GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b)=d, 
                  (c,a,c)=d^x, (c,b,b), (c,b,c), a^p=d, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b)=d, 
                  (c,a,c)=d^r, (c,b,b), (c,b,c), a^p=d^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b)=d, 
                  (c,a,c)=d^-2, (c,b,b), (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a)=d, (c,a,b)=d, 
                  (c,a,c)=d^-2, (c,b,b), (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d | d=(c,b,b),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,b), (c,a,c), 
                  (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,b), (c,a,c), 
                  (c,b,b)=d, (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d | d=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,b), (c,a,c), 
                  (c,b,b)=d, (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,b), (c,a,c), 
                  (c,b,b)=d^w, (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+7;

for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d | d=(b,a,c),(b,a,a), (b,a,b), (c,a,a)=d^x, (c,a,b), (c,a,c), 
                  (c,b,b)=d, (c,b,c), a^p=d, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b), (b,a,c)=d, (c,a,a)=d^-2, (c,a,b), 
                  (c,a,c), (c,b,b)=d, (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b), (b,a,c)=d, (c,a,a)=d^-2, (c,a,b), 
                  (c,a,c), (c,b,b)=d, (c,b,c), a^p=d^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d | d=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,b), 
                  (c,b,b)=d, (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,b), 
                  (c,b,b)=d, (c,b,c), a^p=d^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d^-1, 
                  (c,b,b)=d^-1, (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d^-1, 
                  (c,b,b)=d^-1, (c,b,c), a^p=d^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d^-w, 
                  (c,b,b)=d^-w, (c,b,c), a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d^-w, 
                  (c,b,b)=d^-w, (c,b,c), a^p=d^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+8;

CU:=1;
if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [0..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b)=d^x, (b,a,c), (c,a,a), (c,a,b), 
        (c,a,c)=d, (c,b,b)=d, (c,b,c), a^p=d, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b)=d^x, (b,a,c), (c,a,a), (c,a,b), 
        (c,a,c)=d^w, (c,b,b)=d^w, (c,b,c), a^p=d, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b)=d^x, (b,a,c), (c,a,a), (c,a,b), 
        (c,a,c)=d^w2, (c,b,b)=d^w2, (c,b,c), a^p=d, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b)=d^x, (b,a,c), (c,a,a), (c,a,b), 
        (c,a,c)=d, (c,b,b)=d, (c,b,c), a^p=d^w, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b)=d^x, (b,a,c), (c,a,a), (c,a,b), 
        (c,a,c)=d^w, (c,b,b)=d^w, (c,b,c), a^p=d^w, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b)=d^x, (b,a,c), (c,a,a), (c,a,b), 
        (c,a,c)=d^w2, (c,b,b)=d^w2, (c,b,c), a^p=d^w, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+6;
    end if;
  end for;
else;
  for x in [0..p-1] do
    GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b)=d^x, (b,a,c), (c,a,a), (c,a,b), 
      (c,a,c)=d, (c,b,b)=d, (c,b,c), a^p=d, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b)=d^x, (b,a,c), (c,a,a), (c,a,b), 
      (c,a,c)=d, (c,b,b)=d, (c,b,c), a^p=d^w, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
end if;

GR:=Group<a,b,c | (b,a,b), (b,a,c), (c,a,a), (c,a,b), (c,a,c), (c,b,b), 
                           (c,b,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d, 
                           (c,b,b), (c,b,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d^w, 
                           (c,b,b), (c,b,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a)=d, (c,a,b), (c,a,c), 
                           (c,b,b), (c,b,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;

if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [0..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d, 
                                 (c,b,b)=d, (c,b,c)=d^x, a^p, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d, 
                                 (c,b,b)=d^w, (c,b,c)=d^x, a^p, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d, 
                                 (c,b,b)=d^w2, (c,b,c)=d^x, a^p, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+3;
    end if;
  end for;
else;
  for x in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,b), (c,a,c)=d, 
                             (c,b,b)=d, (c,b,c)=d^x, a^p, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
count:=count+1;
GR:=Group<a,b,c,d | d=(b,a,a),(b,a,b)=d, (b,a,c), (c,a,a)=d, (c,a,b), 
                (c,a,c)=d^-1, (c,b,b)=d^-1, (c,b,c)=d, a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.104 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 5p + 24 + 3gcd(p-1,3) =",
5*p+24+3*Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
