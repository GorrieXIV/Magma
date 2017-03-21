freeze;

import "misc.m": ProcessPresentation; 

Group6_325 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.325 is valid only for p>5"; return false; end if;

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

Z:=Integers();
r:=(F!6)^-1; r:=Z!r;

w2:=w^2 mod p;
w3:=w^3 mod p;
w4:=w^4 mod p;
w5:=w^5 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, (c,a), (c,b), a^p,
                      b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, (c,a), (c,b), 
                      a^p=(b,a,a,a,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, (c,a), (c,b), 
                      a^p=(b,a,a,a,b)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, (c,a), (c,b), a^p,
                      b^p=(b,a,a,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, (c,a), (c,b), 
                      a^p=(b,a,a,a,b), b^p=(b,a,a,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, (c,a), (c,b), 
                      a^p=(b,a,a,a,b)^w, b^p=(b,a,a,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=6;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, (c,a), (c,b), 
                        a^p=(b,a,a,a,b)^w2, b^p=(b,a,a,a,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, (c,a), (c,b), 
                        a^p=(b,a,a,a,b)^w3, b^p=(b,a,a,a,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=8;
end if;
count:=count+1;
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, (c,a), (c,b), a^p,
                          b^p, c^p=(b,a,a,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count,5+Gcd(p-1,4);
count1:=count;
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
                           (c,a)=(b,a,a,a,b), (c,b), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
                           (c,a)=(b,a,a,a,b), (c,b), a^p=(b,a,a,a,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
                           (c,a)=(b,a,a,a,b), (c,b), a^p=(b,a,a,a,b)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
                           (c,a)=(b,a,a,a,b), (c,b), a^p, b^p=(b,a,a,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
                  (c,a)=(b,a,a,a,b), (c,b), a^p=(b,a,a,a,b), b^p=(b,a,a,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
                  (c,a)=(b,a,a,a,b), (c,b), a^p=(b,a,a,a,b)^w, b^p=(b,a,a,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
               (c,a)=(b,a,a,a,b), (c,b), a^p=(b,a,a,a,b)^w2, b^p=(b,a,a,a,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
               (c,a)=(b,a,a,a,b), (c,b), a^p=(b,a,a,a,b)^w3, b^p=(b,a,a,a,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (b,a,a,a,a), (b,a,b)=(b,a,a,a,b)^r, 
                         (c,a)=(b,a,a,a,b), (c,b), a^p, b^p, c^p=(b,a,a,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,5+Gcd(p-1,4);
count1:=count;
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b), a^p=(b,a,a,a,a), 
                            b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b), a^p, 
                            b^p=(b,a,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b), a^p, 
                            b^p=(b,a,a,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b), a^p, 
                              b^p=(b,a,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b), a^p, 
                              b^p=(b,a,a,a,a)^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b), a^p, b^p, 
                          c^p=(b,a,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,3+Gcd(p-1,4);
count1:=count;
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b)=(b,a,a,a,a), a^p, 
                            b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b)=(b,a,a,a,a), 
                            a^p=(b,a,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b)=(b,a,a,a,a), a^p, 
                            b^p=(b,a,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b)=(b,a,a,a,a), a^p, 
                            b^p=(b,a,a,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b)=(b,a,a,a,a), a^p, 
                              b^p=(b,a,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b)=(b,a,a,a,a), a^p, 
                              b^p=(b,a,a,a,a)^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b), (c,a), (c,b)=(b,a,a,a,a), a^p, 
                          b^p, c^p=(b,a,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,3+Gcd(p-1,4);
count1:=count;
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), (c,b), a^p, 
                            b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), (c,b), 
                            a^p=(b,a,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), (c,b), 
                            a^p=(b,a,a,a,a)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  for x in [w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), (c,b), 
                              a^p=(b,a,a,a,a)^x, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), (c,b), a^p, 
                            b^p=(b,a,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), (c,b), a^p, 
                            b^p=(b,a,a,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), (c,b), a^p, 
                              b^p=(b,a,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), (c,b), a^p, 
                              b^p=(b,a,a,a,a)^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), (c,b), a^p, 
                          b^p, c^p=(b,a,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,2+2*Gcd(p-1,3)+Gcd(p-1,4);
count1:=count;
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                           (c,b)=(b,a,a,a,a), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                           (c,b)=(b,a,a,a,a), a^p=(b,a,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                           (c,b)=(b,a,a,a,a), a^p=(b,a,a,a,a)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  for x in [w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                             (c,b)=(b,a,a,a,a), a^p=(b,a,a,a,a)^x, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                           (c,b)=(b,a,a,a,a), a^p, b^p=(b,a,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                           (c,b)=(b,a,a,a,a), a^p, b^p=(b,a,a,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                             (c,b)=(b,a,a,a,a), a^p, b^p=(b,a,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                             (c,b)=(b,a,a,a,a), a^p, b^p=(b,a,a,a,a)^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                         (c,b)=(b,a,a,a,a), a^p, b^p, c^p=(b,a,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                             (c,b)=(b,a,a,a,a), a^p, b^p, c^p=(b,a,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a,a,b), (b,a,b)=(b,a,a,a,a), (c,a), 
                             (c,b)=(b,a,a,a,a), a^p, b^p, c^p=(b,a,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
//print count-count1,1+3*Gcd(p-1,3)+Gcd(p-1,4);

vprint Orderp7, 1: "Group 6.325 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 19 + 5gcd(p-1,3) + 6gcd(p-1,4) =",
19+5*Gcd(p-1,3)+6*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
