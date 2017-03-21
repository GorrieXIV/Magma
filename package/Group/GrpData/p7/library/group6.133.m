freeze;

import "misc.m": ProcessPresentation; 

Group6_133 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.133 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b), a^p=(b,a,b)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b), a^p=d^w*e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b), a^p=d^w*e^w, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=3;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b), a^p=(b,a,b)^w, b^p=(b,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b), a^p=(b,a,b)^w, b^p=(b,a,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b), a^p=(b,a,b)^w, b^p=(b,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b), a^p=(b,a,b)^w, b^p, c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b), a^p=(b,a,b)^w, b^p, c^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b), a^p=(b,a,b)^w, b^p, c^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b)=(b,a,a,a), a^p=(b,a,b)^w, b^p, c^p=(b,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b)=(b,a,a,a), a^p=(b,a,b)^w, 
                            b^p=(b,a,a,a)^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
if p mod 3 eq 2 then
  for x in [1..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e, 
                              a^p=d^w*e^x, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
CU:=1;
if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [1..((p-1) div 2)] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p; x3:=p-x1; x4:=p-x2;
    if x le x1 and x le x2 and x le x3 and x le x4 then
      count:=count+1;
      GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e, 
                                a^p=d^w*e^x, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end if;
  end for;
  for x in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b)=(b,a,a,a)^w, a^p=(b,a,b)^w, b^p, 
                              c^p=(b,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b)=(b,a,a,a)^w, a^p=(b,a,b)^w, 
                              b^p=(b,a,a,a)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  for x in [1..((p-1) div 2)] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p; x3:=p-x1; x4:=p-x2;
    if x le x1 and x le x2 and x le x3 and x le x4 then
      count:=count+1;
      GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e^w, 
                                a^p=d^w*e^x, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end if;
  end for;
  for x in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b)=(b,a,a,a)^w2, a^p=(b,a,b)^w, b^p, 
                              c^p=(b,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c | (c,a)=(b,a,b), (c,b)=(b,a,a,a)^w2, a^p=(b,a,b)^w, 
                              b^p=(b,a,a,a)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  for x in [1..((p-1) div 2)] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p; x3:=p-x1; x4:=p-x2;
    if x le x1 and x le x2 and x le x3 and x le x4 then
      count:=count+1;
      GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(c,a)=d, (c,b)=e^w2, 
                                a^p=d^w*e^x, b^p, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end if;
  end for;
end if;

vprint Orderp7, 1: "Group 6.133 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (p + 1 + 3(p+1)gcd(p-1,3) + gcd(p-1,4))/2 =",
(p+1+3*(p+1)*Gcd(p-1,3)+Gcd(p-1,4))/2;

if Process then return Nmr; else return L; end if;

end function;
