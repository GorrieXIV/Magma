freeze;

import "misc.m": ProcessPresentation; 

Group6_312 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.312 valid only for p>3"; return false; end if;
 
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
w5:=w^5 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (c,b), (b,a,b), a^p, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b), a^p=(b,a,a,a), b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), a^p, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), a^p=(b,a,a,a), 
                      b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), a^p=(b,a,a,a)^w, 
                      b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=5;
if p mod 3 eq 1 then
  for x in [w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), a^p=(b,a,a,a)^x, 
                              b^p=(c,a), c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), a^p, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), a^p=(b,a,a,a), 
                            b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), a^p=(b,a,a,a)^w, 
                            b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), a^p=(b,a,a,a)^w2, 
                              b^p=(c,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), a^p=(b,a,a,a)^w3, 
                              b^p=(c,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), a^p=(b,a,a,a)^x,
                              b^p=(c,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b)=(b,a,a,a)^w, (b,a,b)=(b,a,a,a), a^p=(b,a,a,a)^x,
                              b^p=(c,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c | (c,b), (b,a,b), a^p, b^p=(c,a), c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b), a^p, b^p=(c,a), c^p=(b,a,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b), a^p, b^p=(c,a), c^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b), a^p, b^p=(c,a), c^p=(b,a,a,a)^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), a^p, b^p=(c,a), 
                            c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), a^p, b^p=(c,a), 
                            c^p=(b,a,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), a^p, b^p=(c,a), 
                              c^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), a^p, b^p=(c,a), 
                              c^p=(b,a,a,a)^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), a^p, b^p=(c,a), 
                            c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), a^p, b^p=(c,a), 
                            c^p=(b,a,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), a^p, b^p=(c,a), 
                              c^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), a^p, b^p=(c,a), 
                              c^p=(b,a,a,a)^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [1..p-1] do
  GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), a^p, 
                              b^p=(c,a), c^p=(b,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b)=(b,a,a,a)^w, (b,a,b)=(b,a,a,a), a^p, 
                              b^p=(c,a), c^p=(b,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;

vprint Orderp7, 1: "Group 6.312 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 4p + 2 + 2gcd(p-1,3) + 4gcd(p-1,4) =",
4*p+2+2*Gcd(p-1,3)+4*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
