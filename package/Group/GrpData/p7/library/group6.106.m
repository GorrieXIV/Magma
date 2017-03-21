freeze;

import "misc.m": ProcessPresentation; 

Group6_106 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.106 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;
count:=0;

for x in [0..p-1] do
  GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,a,c), (c,b,c), a^p=(b,a), b^p, 
                              c^p=(c,b,b)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,a,c), (c,b,c), a^p=(b,a), 
                              b^p=(c,b,b), c^p=(c,b,b)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,b,b)=(c,a,c), (c,b,c), 
                              a^p=(b,a), b^p, c^p=(c,a,c)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,b,b)=(c,a,c), (c,b,c), 
                              a^p=(b,a), b^p=(c,a,c), c^p=(c,a,c)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b)=(c,a,a), (c,b,c), 
                              a^p=(b,a), b^p, c^p=(c,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b)=(c,a,a), (c,b,c), 
                              a^p=(b,a), b^p=(c,a,a), c^p=(c,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b)=(c,a,a)^w, (c,b,c), 
                              a^p=(b,a), b^p, c^p=(c,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b)=(c,a,a)^w, (c,b,c), 
                              a^p=(b,a), b^p=(c,a,a), c^p=(c,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+8;
end for;
for x in [0..p-1] do
for y in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d | d=(c,a,a),(c,a,b), (c,a,c)=d, (c,b,b)=d, (c,b,c), 
                              a^p=(b,a), b^p=d^y, c^p=d^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d | d=(c,a,a),(c,a,b), (c,a,c)=d, (c,b,b)=d^w, (c,b,c), 
                              a^p=(b,a), b^p=d^y, c^p=d^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end for;
GR:=Group<a,b,c | (c,a,a), (c,a,c), (c,b,b), (c,b,c), a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,c), (c,b,b), (c,b,c), a^p=(b,a), b^p, 
                            c^p=(c,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,c), (c,b,b), (c,b,c), a^p=(b,a), 
                            b^p=(c,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,c), (c,b,b), (c,b,c), a^p=(b,a), 
                            b^p=(c,a,b), c^p=(c,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,c), (c,b,b), (c,b,c)=(c,a,b), 
                            a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,c), (c,b,b), (c,b,c)=(c,a,b), 
                            a^p=(b,a), b^p=(c,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,c), (c,b,b), (c,b,c)=(c,a,b), 
                            a^p=(b,a), b^p=(c,a,b)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+7;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d | d=(c,a,b),(c,a,a), (c,a,c), (c,b,b), (c,b,c)=d, 
                            a^p=(b,a), b^p=d^x, c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,a,c), (c,b,b), a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,a,c), (c,b,b), a^p=(b,a), b^p, 
                            c^p=(c,b,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,a,c), (c,b,b), a^p=(b,a), 
                            b^p=(c,b,c), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,a,c), (c,b,b), a^p=(b,a), 
                            b^p=(c,b,c)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,b,c),(c,a,a), (c,a,b), (c,a,c), (c,b,b), 
                            a^p=d*e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,b,c),(c,a,a), (c,a,b), (c,a,c), (c,b,b), 
                            a^p=d*e, b^p, c^p=(c,b,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,b,c),(c,a,a), (c,a,b), (c,a,c), (c,b,b), 
                            a^p=d*e, b^p=(c,b,c), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,b,c),(c,a,a), (c,a,b), (c,a,c), (c,b,b), 
                            a^p=d*e, b^p=(c,b,c)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c)=(c,a,a), 
                            a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c)=(c,a,a), 
                             a^p=(b,a), b^p, c^p=(c,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c)=(c,a,a), 
                             a^p=(b,a), b^p, c^p=(c,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c)=(c,a,a), 
                             a^p=(b,a), b^p=(c,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c)=(c,a,a), 
                             a^p=(b,a), b^p=(c,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+13;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c)=(c,a,a), 
                              a^p=(b,a), b^p=(c,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c)=(c,a,a), 
                              a^p=(b,a), b^p=(c,a,a)^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,b,b), (c,b,c), a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c),(c,a,a), (c,a,b), (c,b,b), (c,b,c), 
                            a^p=d*e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c),(c,a,a), (c,a,b), (c,b,b), (c,b,c), 
                            a^p=d*e^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,b,b), (c,b,c), a^p=(b,a), b^p, 
                            c^p=(c,a,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c),(c,a,a), (c,a,b), (c,b,b), (c,b,c), 
                            a^p=d*e, b^p, c^p=(c,a,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c),(c,a,a), (c,a,b), (c,b,b), (c,b,c), 
                            a^p=d*e^w, b^p, c^p=(c,a,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,a), (c,a,b), (c,b,b), (c,b,c), a^p=(b,a), 
                            b^p=(c,a,c), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c), a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c), a^p=(b,a), b^p, 
                            c^p=(c,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c), a^p=(b,a), b^p, 
                             c^p=(c,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c), (c,b,b), (c,b,c), a^p=(b,a), 
                             b^p=(c,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c)=(c,a,a), (c,b,b), (c,b,c), 
                             a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c)=(c,a,a), (c,b,b), (c,b,c), 
                             a^p=(b,a), b^p, c^p=(c,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c)=(c,a,a), (c,b,b), (c,b,c), 
                             a^p=(b,a), b^p, c^p=(c,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,a,b), (c,a,c)=(c,a,a), (c,b,b), (c,b,c), 
                             a^p=(b,a), b^p=(c,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+15;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,a,b), (c,a,c)=(c,a,a), (c,b,b), (c,b,c), 
                              a^p=(b,a), b^p=(c,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,a,b), (c,a,c)=(c,a,a), (c,b,b), (c,b,c), 
                              a^p=(b,a), b^p=(c,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.106 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is p^2 + 10p + 32 + gcd(p-1,3) + gcd(p-1,4) =",
p^2+10*p+32+Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
