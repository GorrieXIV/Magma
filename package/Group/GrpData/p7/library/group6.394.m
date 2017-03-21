freeze;

import "misc.m": ProcessPresentation; 

Group6_394 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.394 is valid only for p>5"; return false; end if;

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
w4:=w^4 mod p;
w5:=w^5 mod p;
w6:=w^6 mod p;
w7:=w^7 mod p;
w8:=w^8 mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),(b,a,b,b),a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),(b,a,b,b),
             a^p=(b,a,a,a,b),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),(b,a,b,b),
             a^p=(b,a,a,a,b)^w,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),(b,a,b,b),a^p,
             b^p=(b,a,a,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),(b,a,b,b),
             a^p=(b,a,a,a,b),b^p=(b,a,a,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),(b,a,b,b),
             a^p=(b,a,a,a,b)^w,b^p=(b,a,a,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=6;
if p mod 4 eq 1 then
  GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),(b,a,b,b),
               a^p=(b,a,a,a,b)^w2,b^p=(b,a,a,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),(b,a,b,b),
               a^p=(b,a,a,a,b)^w3,b^p=(b,a,a,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=8;
end if;
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),
                   (b,a,b,b)=(b,a,a,a,b),a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),
                   (b,a,b,b)=(b,a,a,a,b),a^p,b^p=(b,a,a,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 5 eq 1 then
for x in [w,w2,w3,w4] do
  count:=count+1;
  GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),
                  (b,a,b,b)=(b,a,a,a,b),a^p,b^p=(b,a,a,a,b)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end if;
if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [0..((p-1) div 2)] do
    x1:=(CU*x) mod p; x2:=p-x1; x3:=(CU*x1) mod p; x4:=(CU*x2) mod p;
    if x le x1 and x le x2 and x le x3 and x le x4 then
      for y in [1,w,w2,w3,w4,w5] do
        count:=count+1;
        GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),
          (b,a,b,b)=(b,a,a,a,b),a^p=(b,a,a,a,b)^y,b^p=(b,a,a,a,b)^x>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
else;
  for x in [0..((p-1) div 2)] do
  for y in [1,w] do
    count:=count+1;
    GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b),
      (b,a,b,b)=(b,a,a,a,b),a^p=(b,a,a,a,b)^y,b^p=(b,a,a,a,b)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  end for;
end if;
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b)^2,(b,a,b,b),a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b)^2,(b,a,b,b),
                   a^p=(b,a,a,a,b),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b)^2,(b,a,b,b),
                   a^p=(b,a,a,a,b)^w,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b)^2,(b,a,b,b),
                   a^p=(b,a,a,a,b)^x,b^p=(b,a,a,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b|(b,a,a,a,a),(b,a,a,b)=(b,a,a,a,b)^2,
    (b,a,b,b)=(b,a,a,a,b),a^p=(b,a,a,a,b)^x,b^p=(b,a,a,a,b)^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b),a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b),a^p,b^p=(b,a,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b),a^p,b^p=(b,a,a,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b),a^p,
                     b^p=(b,a,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b),a^p,
                     b^p=(b,a,a,a,a)^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b),a^p=(b,a,a,a,a),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b)=(b,a,a,a,a),(b,a,b,b),a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b)=(b,a,a,a,a),(b,a,b,b),
                   a^p=(b,a,a,a,a),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 5 eq 1 then
  for x in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b)=(b,a,a,a,a),(b,a,b,b),
                     a^p=(b,a,a,a,a)^x,b^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b)=(b,a,a,a,a),(b,a,b,b),a^p,
                   b^p=(b,a,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b)=(b,a,a,a,a),(b,a,b,b),a^p,
                   b^p=(b,a,a,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b)=(b,a,a,a,a),(b,a,b,b),a^p,
                     b^p=(b,a,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b)=(b,a,a,a,a),(b,a,b,b),a^p,
                     b^p=(b,a,a,a,a)^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a,a),a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a,a),
                   a^p=(b,a,a,a,a),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
for y in [w,w2] do
  count:=count+1;
  GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a,a),
                   a^p=(b,a,a,a,a)^y,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end if;
if p mod 9 eq 1 then
for y in [w3,w4,w5,w6,w7,w8] do
  count:=count+1;
  GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a,a),
                   a^p=(b,a,a,a,a)^y,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end if;
if p mod 4 eq 3 then
  for x in [0..((p-1) div 2)] do
  for y in [1,w] do
    count:=count+1;
    GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a,a),
                     a^p=(b,a,a,a,a)^x,b^p=(b,a,a,a,a)^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  end for;
end if;
if p mod 8 eq 5 then
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for x in [0..((p-1) div 2)] do
    x1:=(QU*x) mod p; x2:=p-x1;
    if x le x1 and x le x2 then
      for y in [1,w,w2,w3] do
        count:=count+1;
        GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a,a),
                        a^p=(b,a,a,a,a)^x,b^p=(b,a,a,a,a)^y>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
end if;
if p mod 8 eq 1 then
  for i in [2..p-2] do
    if i^8 mod p eq 1 and i^4 mod p ne 1 then OC:=i; break; end if;
  end for;
  for x in [0..((p-1) div 2)] do
    x1:=(OC*x) mod p; x2:=(OC*x1) mod p; x3:=(OC*x2) mod p;
    x1:=Minimum(x1,p-x1); x2:=Minimum(x2,p-x2); x3:=Minimum(x3,p-x3);
    if x le x1 and x le x2 and x le x3 then
      for y in [1,w,w2,w3,w4,w5,w6,w7] do
        count:=count+1;
        GR:=Group<a,b|(b,a,a,a,b),(b,a,a,b),(b,a,b,b)=(b,a,a,a,a),
                        a^p=(b,a,a,a,a)^x,b^p=(b,a,a,a,a)^y>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
end if;

vprint Orderp7, 1: "Group 6.394 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is p^2+3p+10+2gcd(p-1,3)+3gcd(p-1,4)+2gcd(p-1,5)+gcd(p-1,8)+gcd(p-1,9) =",
p^2+3*p+10+2*Gcd(p-1,3)+3*Gcd(p-1,4)+2*Gcd(p-1,5)+Gcd(p-1,8)+Gcd(p-1,9);

if Process then return Nmr; else return L; end if;

end function;
