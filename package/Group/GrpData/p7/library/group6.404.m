freeze;

import "misc.m": ProcessPresentation; 

Group6_404 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.404 is valid only for p>5"; return false; end if;

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

w2:=w^2 mod p;
w3:=w^3 mod p;

r:=((p+3)*w) div 2; r:=r mod p;
s:=(r+1) mod p;


L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b), 
                   (b,a,b,b)=c^-w*d^r, a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b), 
     (b,a,b,b)=c^-w*d^r, a^p=d, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b), 
       (b,a,b,b)=c^-w*d^r, a^p=d^w, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
if p mod 8 eq 1 then
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b), 
      (b,a,b,b)=c^-w*d^r, a^p=d^w2, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b), 
      (b,a,b,b)=c^-w*d^r, a^p=d^w3, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b), 
   (b,a,b,b)=c^-w*d^r,a^p=d^x,b^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b), 
   (b,a,b,b)=c^-w*d^r,a^p=d^x,b^p=d^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
  if p mod 4 eq 1 then
    GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b), 
     (b,a,b,b)=c^-w*d^r,a^p=d^x,b^p=d^w2>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b), 
     (b,a,b,b)=c^-w*d^r,a^p=d^x,b^p=d^w3>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
for x in [0..((p-1) div 2)] do
for y in [0..p-1] do
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b)=d, 
   (b,a,b,b)=c^-w*d^r,a^p=d^x,b^p=d^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b), 
   (b,a,b,b)=c^-w*d^s,a^p=d^x,b^p=d^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
end for;
for x in [1..((p-1) div 2)] do
for y in [0..p-1] do
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(c,a),(b,a,a,a,b), (b,a,a,b)=d^x, 
   (b,a,b,b)=c^-w*d^s,a^p=d^y,b^p=d^z>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
end for;

vprint Orderp7, 1: "Group 6.404 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is (p^3 + p^2 + 2p + 2 + (p+1)gcd(p-1,4) + gcd(p-1,8))/2 =",
(p^3+p^2+2*p+2+(p+1)*Gcd(p-1,4)+Gcd(p-1,8))/2;

if Process then return Nmr; else return L; end if;

end function;
