freeze;

import "misc.m": ProcessPresentation; 

Group6_327 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.327 is valid only for p>5"; return false; end if;

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
s:=-(F!3)*(F!2)^-1; s:=Z!s;
t:=(p+1) div 2;
t1:=(p-1) div 2;

w2:=w^2 mod p;
w3:=w^3 mod p;
w4:=w^4 mod p;
w5:=w^5 mod p;
w6:=w^6 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, (c,a), 
                     (c,b)=d*e^t, a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, (c,a), 
                     (c,b)=d*e^t, a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, (c,a), 
                     (c,b)=d*e^t, a^p=e^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, (c,a), 
                     (c,b)=d*e^t, a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, (c,a), 
       (c,b)=d*e^t, a^p=e, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, (c,a), 
       (c,b)=d*e^t, a^p=e^w, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=6;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, (c,a), 
        (c,b)=d*e^t, a^p=e^w2, b^p=e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, (c,a), 
        (c,b)=d*e^t, a^p=e^w3, b^p=e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=8;
end if;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, (c,a), 
                  (c,b)=d*e^t, a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, (c,a), 
                  (c,b)=d*e^t, a^p, b^p, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
//print count,6+Gcd(p-1,4);
//count1:=count;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, 
             (c,a)=e, (c,b)=d*e^t, a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, 
  (c,a)=e, (c,b)=d*e^t, a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, 
  (c,a)=e, (c,b)=d*e^t, a^p=e^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  for x in [w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, 
      (c,a)=e, (c,b)=d*e^t, a^p=e^x, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, 
     (c,a)=e, (c,b)=d*e^t, a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 7 eq 1 then
  for x in [w,w2,w3,w4,w5,w6] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, 
      (c,a)=e, (c,b)=d*e^t, a^p, b^p=e^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
SE:=1;
if p mod 7 eq 1 then
  for i in [2..p-1] do
    if i^7 mod p eq 1 then SE:=i; break; end if;
  end for;
  for x in [1..p-1] do
    x1:=(SE*x) mod p; x2:=(SE*x1) mod p; x3:=(SE*x2) mod p; x4:=(SE*x3) mod p;
    x5:=(SE*x4) mod p; x6:=(SE*x5) mod p;
    if x le x1 and x le x2 and x le x3 and x le x4 and x le x5 and x le x6 then
      for y in [1,w,w2,w3,w4,w5,w6] do 
        count:=count+1;
        GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, 
                                 (c,a)=e, (c,b)=d*e^t, 
                                  a^p=e^x, b^p=e^y, c^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
else;
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, 
                             (c,a)=e, (c,b)=d*e^t, 
                              a^p=e^x, b^p=e, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, 
  (c,a)=e, (c,b)=d*e^t, a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,b),(b,a,a,a,a), (b,a,b)=e^r, 
  (c,a)=e, (c,b)=d*e^t, a^p, b^p, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
//print count-count1,p+2+2*Gcd(p-1,3)+Gcd(p-1,7);
//count1:=count;

GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
                           (c,b)=d*e^s, a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
                           (c,b)=d*e^s, a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
                           (c,b)=d*e^s, a^p, b^p=e^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
                          (c,b)=d*e^s, a^p, b^p=e^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
                          (c,b)=d*e^s, a^p, b^p=e^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
                           (c,b)=d*e^s, a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
             (c,b)=d*e^s, a^p, b^p=e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
             (c,b)=d*e^s, a^p, b^p=e^w, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
            (c,b)=d*e^s, a^p, b^p=e^w2, c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
            (c,b)=d*e^s, a^p, b^p=e^w3, c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
                         (c,b)=d*e^s, a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,3+2*Gcd(p-1,4);
//count1:=count;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
                        (c,b)=d*e^t1, a^p, b^p=e^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
            (c,b)=d*e^t1, a^p, b^p=e^x, c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a,a),e=(d,a),(b,a,a,a,b), (b,a,b), (c,a), 
                         (c,b)=d*e^t1, a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,2*p+1;

vprint Orderp7, 1: "Group 6.327 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 3p + 12 + 2gcd(p-1,3) + 3gcd (p-1,4) + gcd(p-1,7) =",
3*p+12+2*Gcd(p-1,3)+3*Gcd(p-1,4)+Gcd(p-1,7);

if Process then return Nmr; else return L; end if;

end function;
