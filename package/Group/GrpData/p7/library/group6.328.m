freeze;

import "misc.m": ProcessPresentation; 

Group6_328 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.328 is valid only for p>5"; return false; end if;

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
r:=(F!7)*(F!6)^-1; r:=Z!r;
s:=-(F!3)*(F!2)^-1; s:=Z!s;
t:=(p+1) div 2;

w2:=w^2 mod p;
w3:=w^3 mod p;
w4:=w^4 mod p;
w5:=w^5 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                     (c,a), (c,b)=d*e^t, a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                     (c,a), (c,b)=d*e^t, a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                     (c,a), (c,b)=d*e^t, a^p=e^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 3 eq 1 then
  for x in [w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                    (c,a), (c,b)=d*e^t, a^p=e^x, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                (c,a), (c,b)=d*e^t, a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 5 eq 1 then
  for x in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                    (c,a), (c,b)=d*e^t, a^p, b^p=e^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
FI:=1;
if p mod 5 eq 1 then
  for i in [2..p-1] do
    if i^5 mod p eq 1 then FI:=i; break; end if;
  end for;
  for x in [1..p-1] do
    x1:=(FI*x) mod p; x2:=(FI*x1) mod p; x3:=(FI*x2) mod p; x4:=(FI*x3) mod p;
    if x le x1 and x le x2 and x le x3 and x le x4 then
      for y in [1,w,w2,w3,w4] do
        count:=count+1; 
        GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                        (c,a), (c,b)=d*e^t, a^p=e^x, 
                         b^p=e^y, c^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
else;
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                    (c,a), (c,b)=d*e^t, a^p=e^x, 
                     b^p=e, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                  (c,a), (c,b)=d*e^t, a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                  (c,a), (c,b)=d*e^t, a^p, b^p, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                 (c,a), (c,b)=d*e^t, a^p, b^p, c^p=e^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                 (c,a), (c,b)=d*e^t, a^p, b^p, c^p=e^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
//print count,p+2*Gcd(p-1,3)+Gcd(p-1,4)+Gcd(p-1,5);
//count1:=count;
CU:=1;
if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for z in [1,w,w2] do
  for x in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                    (c,a)=e^z, (c,b)=d*e^t, 
                     a^p=e^x, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    for y in [1..p-1] do
      y1:=(CU*y) mod p; y2:=(CU*y1) mod p;
      if y le y1 and y le y2 then
        count:=count+1;
        GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                        (c,a)=e^z, (c,b)=d*e^t, 
                         a^p=e^x, b^p=e^y, c^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end if;
    end for;
  end for;
  for y in [1..p-1] do
    y1:=(CU*y) mod p; y2:=(CU*y1) mod p;
    if y le y1 and y le y2 then
      count:=count+1;
      GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                  (c,a)=e^z, (c,b)=d*e^t, a^p, b^p, 
                   c^p=e^y>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end if;
  end for;
  end for;
else;
  for x in [0..p-1] do
  for y in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                    (c,a)=e, (c,b)=d*e^t, 
                     a^p=e^x, b^p=e^y, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  end for;
  for y in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=d*e^r, 
                    (c,a)=e, (c,b)=d*e^t, a^p, b^p, 
                     c^p=e^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
//print count-count1,p^2-1+p*Gcd(p-1,3);
//count1:=count;

GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                  (c,b)=d*e^s, a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                  (c,b)=d*e^s, a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                  (c,b)=d*e^s, a^p, b^p=e^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                (c,b)=d*e^s, a^p, b^p=e^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                (c,b)=d*e^s, a^p, b^p=e^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                (c,b)=d*e^s, a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 5 eq 1 then
  for y in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                    (c,b)=d*e^s, a^p=e^y, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
if p mod 5 eq 1 then
  for x in [1..p-1] do
    x1:=(FI*x) mod p; x2:=(FI*x1) mod p; x3:=(FI*x2) mod p; x4:=(FI*x3) mod p;
    if x le x1 and x le x2 and x le x3 and x le x4 then
      for y in [1,w,w2,w3,w4] do
        count:=count+1;
        GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
              (c,b)=d*e^s, a^p=e^y, b^p=e^x, 
               c^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
else;
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
           (c,b)=d*e^s, a^p=e, b^p=e^x, 
            c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                (c,b)=d*e^s, a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                (c,b)=d*e^s, a^p, b^p, c^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                (c,b)=d*e^s, a^p, b^p, c^p=e^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
if p mod 3 eq 1 then
  for x in [1..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      for y in [1,w,w2] do
        count:=count+1;
        GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                        (c,b)=d*e^s, a^p, b^p=e^x, 
                         c^p=e^y>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
else;
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b)=d*e^-1, (c,a), 
                    (c,b)=d*e^s, a^p, b^p=e^x, 
                     c^p=e>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
//print count-count1,2*p-1+Gcd(p-1,3)+Gcd(p-1,4)+Gcd(p-1,5);

vprint Orderp7, 1: "Group 6.328 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is p^2 + 3p - 2 + (p+3)gcd(p-1,3) + 2gcd(p-1,4) + 2gcd(p-1,5) =",
p^2+3*p-2+(p+3)*Gcd(p-1,3)+2*Gcd(p-1,4)+2*Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;
