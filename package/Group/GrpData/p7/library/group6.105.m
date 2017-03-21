freeze;

import "misc.m": ProcessPresentation; 

Group6_105 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.105 valid only for p>3"; return false; end if;

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
w3:=w^3 mod p;
w4:=w^4 mod p;
w5:=w^5 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,c), a^p=(c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(c,b),e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), 
                      a^p=d*e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,c), a^p=(c,b), b^p, 
                      c^p=(c,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,c), a^p=(c,b), b^p, 
                      c^p=(c,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,c), a^p=(c,b), 
                      b^p=(c,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,a), a^p=(c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,a), a^p=(c,b), b^p, 
                      c^p=(c,a,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,a), a^p=(c,b), 
                      b^p=(c,a,c), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=8;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,a), a^p=(c,b), 
                              b^p=(c,a,c)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,a), a^p=(c,b), 
                              b^p=(c,a,c)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

GR:=Group<a,b,c | (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a), 
                            a^p=(c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a), 
                            a^p=(c,b), b^p, c^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 5 eq 1 then
  for x in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c | (b,a,b), (b,a,c), (c,a,a), (c,a,c)*(b,a,a)^-1, 
                              a^p=(c,b), b^p, c^p=(b,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b,c | (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a), 
                            a^p=(c,b), b^p=(b,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a), 
                            a^p=(c,b), b^p=(b,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  for x in [w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c | (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a), 
                              a^p=(c,b), b^p=(b,a,a)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;

GR:=Group<a,b,c | (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b)^-1, a^p=(c,b), 
                            b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b)^-1, a^p=(c,b), 
                            b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b)^-1, a^p=(c,b), 
                              b^p, c^p=(b,a,b)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b)^-1, a^p=(c,b), 
                              b^p, c^p=(b,a,b)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d | d=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=d^-1, a^p=(c,b), 
                            b^p=d, c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b)^-w, a^p=(c,b),
                            b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b)^-w, a^p=(c,b),
                            b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b)^-w, a^p=(c,b),
                              b^p, c^p=(b,a,b)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b)^-w, a^p=(c,b),
                              b^p, c^p=(b,a,b)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.105 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 11 + 5gcd(p-1,3) + gcd(p-1,5) =",
11+5*Gcd(p-1,3)+Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;
