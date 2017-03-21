freeze;

import "misc.m": ProcessPresentation; 

Group6_218 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.218 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b), a^p, b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b), a^p, b^p, d^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b), a^p, b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b), a^p, b^p, 
                      d^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b)=(b,a,a,a), a^p, b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b)=(b,a,a,a), a^p, b^p, 
                      d^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b)=(b,a,a,a), a^p, b^p, 
                      d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b)=(b,a,a,a), a^p, b^p, 
                      d^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b)=(b,a,a,a)^w, a^p, b^p, 
                      d^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b), a^p, b^p=(b,a,a,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b), a^p, b^p=(b,a,a,a), 
                       d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b)=(b,a,a,a), a^p, b^p=(b,a,a,a), 
                       d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b)=(b,a,a,a), a^p, 
                       b^p=(b,a,a,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=13;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b), a^p, b^p=(b,a,a,a)^w, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b), a^p, b^p=(b,a,a,a)^w, 
                         d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b)=(b,a,a,a), a^p, b^p=(b,a,a,a)^w, 
                         d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b)=(b,a,a,a), a^p, 
                         b^p=(b,a,a,a)^w, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b), a^p, b^p=(b,a,a,a)^w2, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b), a^p, 
                         b^p=(b,a,a,a)^w2, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b)=(b,a,a,a), a^p, 
                         b^p=(b,a,a,a)^w2, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b)=(b,a,a,a), a^p, 
                         b^p=(b,a,a,a)^w2, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=21;
end if;
GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b), a^p=(b,a,a,a), b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b), (c,a), (c,b)=(b,a,a,a), a^p=(b,a,a,a), b^p, 
                            d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b), a^p=(b,a,a,a), b^p, 
                            d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b)=(b,a,a,a), 
                            a^p=(b,a,a,a), b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b), a^p=(b,a,a,a)^w, b^p, 
                            d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b)=(b,a,a,a), 
                            a^p=(b,a,a,a)^w, b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b), a^p=(b,a,a,a)^w2, 
                              b^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b)=(b,a,a,a), 
                              a^p=(b,a,a,a)^w2, b^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b), a^p=(b,a,a,a)^w3, 
                              b^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=c^p, (b,a,b)=(b,a,a,a), (c,a), (c,b)=(b,a,a,a), 
                              a^p=(b,a,a,a)^w3, b^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;

vprint Orderp7, 1: "Group 6.218 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 11 + 4gcd(p-1,3) + 2gcd(p-1,4) =",
11+4*Gcd(p-1,3)+2*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
