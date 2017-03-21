freeze;

import "misc.m": ProcessPresentation; 

Group6_475 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.475 is valid only for p>5"; return false; end if;

class:=6;

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
w6:=w^6 mod p;

r:=(p-3) div 2;
s:=(F!4)*(F!3)^-1; s:=Integers()!s; s:=p-s;
t:=(p-1) div 2;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|c=(b,a,a,a,a),d=(c,a),(b,a,b)=c*d^r, (b,a,a,a,b), a^p,
                    b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a,a),d=(c,a),(b,a,b)=c*d^r, (b,a,a,a,b), a^p,
                    b^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 5 eq 1 then
  for x in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c,d|c=(b,a,a,a,a),d=(c,a),(b,a,b)=c*d^r, (b,a,a,a,b), a^p,
                            b^p=d^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
count:=count+1;
GR:=Group<a,b,c,d|c=(b,a,a,a,a),d=(c,a),(b,a,b)=c*d^r, (b,a,a,a,b), 
                        a^p=d, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 7 eq 1 then
  for x in [w,w2,w3,w4,w5,w6] do
    count:=count+1;
    GR:=Group<a,b,c,d|c=(b,a,a,a,a),d=(c,a),(b,a,b)=c*d^r, (b,a,a,a,b), 
                            a^p=d^x, b^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a,a),d=(c,a),(b,a,b)=c*d^s, 
           (b,a,a,a,b)=d, a^p, b^p=d^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a,a),d=(c,a),(b,a,b)=c*d^s, 
            (b,a,a,a,b)=d, a^p=d^x, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a,a),d=(c,a),(b,a,b)=c*d^t, (b,a,a,a,b),
                          a^p, b^p=d^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a,a),d=(c,a),(b,a,b)=c*d^t, (b,a,a,a,b), 
                          a^p=d^x, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.475 has",count,"descendants of order p^7 and p-class 6";

vprint Orderp7, 2: "Total number of groups is 4p - 1 + gcd(p-1,5) + gcd(p-1,7) =",
4*p-1+Gcd(p-1,5)+Gcd(p-1,7);

if Process then return Nmr; else return L; end if;

end function;
