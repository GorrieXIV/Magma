freeze;

import "misc.m": ProcessPresentation; 

Group6_274 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.274 valid only for p>3"; return false; end if;
 
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

GR:=Group<a,b,c | (c,b), (c,a,c), a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (c,a,c), a^p=(b,a), b^p, c^p=(c,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (c,a,c), a^p=(b,a), b^p, c^p=(c,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (c,a,c), a^p=(b,a), b^p, c^p=(c,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=4;
end if;
GR:=Group<a,b,c | (c,b), (c,a,c)=(c,a,a,a), a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (c,a,c)=(c,a,a,a), a^p=(b,a), b^p, 
                            c^p=(c,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (c,a,c)=(c,a,a,a), a^p=(b,a), b^p, 
                              c^p=(c,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (c,a,c)=(c,a,a,a), a^p=(b,a), b^p, 
                              c^p=(c,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c | (c,b)=(c,a,a,a), (c,a,c), a^p=(b,a), b^p, 
                            c^p=(c,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 3 eq 1 then
    GR:=Group<a,b,c | (c,b)=(c,a,a,a)^w, (c,a,c), a^p=(b,a), b^p, 
                                c^p=(c,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c | (c,b)=(c,a,a,a)^w2, (c,a,c), a^p=(b,a), b^p, 
                                c^p=(c,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
  count:=count+1;
  GR:=Group<a,b,c | (c,b)=(c,a,a,a), (c,a,c)=(c,a,a,a), a^p=(b,a), 
                            b^p, c^p=(c,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 3 eq 1 then
    GR:=Group<a,b,c | (c,b)=(c,a,a,a)^w, (c,a,c)=(c,a,a,a), a^p=(b,a), 
                                b^p, c^p=(c,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c | (c,b)=(c,a,a,a)^w2, (c,a,c)=(c,a,a,a), a^p=(b,a), 
                                b^p, c^p=(c,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
GR:=Group<a,b,c | (c,b), (c,a,c), a^p=(b,a), b^p=(c,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(c,a,a,a), (c,a,c), a^p=(b,a), 
                            b^p=(c,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b)=(c,a,a,a)^w, (c,a,c), a^p=(b,a), 
                              b^p=(c,a,a,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b)=(c,a,a,a)^w2, (c,a,c), a^p=(b,a), 
                              b^p=(c,a,a,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (c,a,c)=(c,a,a,a), a^p=(b,a), 
                          b^p=(c,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 5 eq 1 then
  for x in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c | (c,b), (c,a,c)=(c,a,a,a), a^p=(b,a), 
                              b^p=(c,a,a,a)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
CU:=1;
if p mod 3 eq 2 then
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c | (c,b)=(c,a,a,a), (c,a,c)=(c,a,a,a), a^p=(b,a), 
                              b^p=(c,a,a,a)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
else;
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [1..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c | (c,b)=(c,a,a,a), (c,a,c)=(c,a,a,a), a^p=(b,a), 
                                  b^p=(c,a,a,a)^x, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c | (c,b)=(c,a,a,a)^w, (c,a,c)=(c,a,a,a), a^p=(b,a), 
                                  b^p=(c,a,a,a)^x, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c | (c,b)=(c,a,a,a)^w2, (c,a,c)=(c,a,a,a), a^p=(b,a), 
                                  b^p=(c,a,a,a)^x, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+3;
    end if;
  end for;
end if;

vprint Orderp7, 1: "Group 6.274 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p + 2 + (2p+3)gcd(p-1,3) + gcd(p-1,5) =",
p+2+(2*p+3)*Gcd(p-1,3)+Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;
