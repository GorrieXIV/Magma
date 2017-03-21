freeze;

import "misc.m": ProcessPresentation; 

Group6_197 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.197 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d | d=a^p,(b,a,a), (c,a), (c,b), d^p=(b,a,b,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=1;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d | d=a^p,(b,a,a), (c,a), (c,b), d^p=(b,a,b,b)^w, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=a^p,(b,a,a), (c,a), (c,b), d^p=(b,a,b,b)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=3;
end if;
count:=count+1;
GR:=Group<a,b,c,d|d=a^p,(b,a,a), (c,a)=(b,a,b,b), (c,b), d^p=(b,a,b,b), 
                          b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d|d=a^p,(b,a,a), (c,a)=(b,a,b,b), (c,b), d^p=(b,a,b,b)^w, 
                              b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|d=a^p,(b,a,a), (c,a)=(b,a,b,b), (c,b), d^p=(b,a,b,b)^w2, 
                              b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a), (c,b), d^p=(b,a,b,b), 
                          b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a), (c,b), d^p=(b,a,b,b)^w, 
                              b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a), (c,b), d^p=(b,a,b,b)^w2, 
                              b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a)=(b,a,b,b), (c,b), 
                          d^p=(b,a,b,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a)=(b,a,b,b), (c,b), 
                              d^p=(b,a,b,b)^w, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a)=(b,a,b,b), (c,b), 
                              d^p=(b,a,b,b)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d|d=a^p,(b,a,a), (c,a), (c,b), d^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a), (c,a), (c,b), d^p, b^p, c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a), (c,a), (c,b), d^p, b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a), (c,a)=(b,a,b,b), (c,b), d^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a), (c,a)=(b,a,b,b), (c,b), d^p, b^p, 
                            c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a), (c,a)=(b,a,b,b), (c,b), d^p, 
                            b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a), (c,b), d^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a), (c,b), d^p, b^p, 
                            c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a), (c,b), d^p, 
                            b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a), (c,b), d^p, 
                             b^p=(b,a,b,b)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+10;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a), (c,b), d^p, 
                              b^p=(b,a,b,b)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a), (c,b), d^p, 
                              b^p=(b,a,b,b)^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a)=(b,a,b,b), (c,b), d^p, 
                            b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a)=(b,a,b,b), (c,b), d^p, 
                            b^p, c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a)=(b,a,b,b), (c,b), d^p, 
                            b^p, c^p=(b,a,b,b)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a)=(b,a,b,b), (c,b), d^p, 
                            b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a)=(b,a,b,b), (c,b), d^p, 
                            b^p=(b,a,b,b)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+5;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a)=(b,a,b,b), (c,b), d^p, 
                              b^p=(b,a,b,b)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|d=a^p,(b,a,a)=(b,a,b,b), (c,a)=(b,a,b,b), (c,b), d^p, 
                              b^p=(b,a,b,b)^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.197 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 11 + 4gcd(p-1,3) + 2gcd(p-1,4) =",
11+4*Gcd(p-1,3)+2*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
