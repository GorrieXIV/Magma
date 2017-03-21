freeze;

import "misc.m": ProcessPresentation; 

Group6_362 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.362 is valid only for p>5"; return false; end if;

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
r:=(F!5)*(F!12)^-1; r:=Z!r;
s:=(F!17)*(F!12)^-1; s:=Z!s;
t:=(r+w) mod p;

w2:=w^2 mod p;
w3:=w^3 mod p;
w4:=w^4 mod p;
w5:=w^5 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                      a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                      a^p, b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                      a^p, b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                        a^p, b^p=f^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                        a^p, b^p=f^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=5;
end if;
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                            a^p, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                            a^p, b^p=f, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                            a^p, b^p=f^w, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                              a^p, b^p=f^w2, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                              a^p, b^p=f^w3, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                            a^p=f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^r, 
                            a^p=f, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
//print count,4+2*Gcd(p-1,4);
count1:=count;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^s, 
                              a^p, b^p=f^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^s, 
                              a^p, b^p=f^x, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^s, 
                          a^p=f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^s, 
                            a^p=f^x, b^p, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^t, 
                              a^p, b^p=f^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^t, 
                              a^p, b^p=f^x, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^t, 
                          a^p=f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b), (c,a), (c,b)=d*e^-1*f^t, 
                            a^p=f^x, b^p, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
//print count-count1,5*p+1;
count1:=count;
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                  (c,b)=d*e^-1*f^r, a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                  (c,b)=d*e^-1*f^r, a^p, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 5 eq 1 then
  for x in [w,w2,w3,w4] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                    (c,b)=d*e^-1*f^r, a^p, b^p, c^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
             (c,b)=d*e^-1*f^r, a^p, b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
             (c,b)=d*e^-1*f^r, a^p, b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
               (c,b)=d*e^-1*f^r, a^p, b^p=f^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
               (c,b)=d*e^-1*f^r, a^p, b^p=f^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
QU:=1;
if p mod 4 eq 1 then
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for x in [1..((p-1) div 2)] do
    x1:=(QU*x) mod p; x2:=p-x1;
    if x le x1 and x le x2 then
      for y in [1,w,w2,w3] do
        count:=count+1;
        GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                                 (c,b)=d*e^-1*f^r, a^p, b^p=f^y, c^p=f^x>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
else;
  for x in [1..((p-1) div 2)] do
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                               (c,b)=d*e^-1*f^r, a^p, b^p=f, c^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                               (c,b)=d*e^-1*f^r, a^p, b^p=f^w, c^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
end if;
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                           (c,b)=d*e^-1*f^r, a^p=f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                           (c,b)=d*e^-1*f^r, a^p=f^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  for y in [w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                             (c,b)=d*e^-1*f^r, a^p=f^y, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
CU:=1;
if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [1..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      for y in [1,w,w2,w3,w4,w5] do
        count:=count+1;
        GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                                 (c,b)=d*e^-1*f^r, a^p=f^y, b^p=f^x, c^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
  for x in [1..((p-1) div 2)] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p; x3:=p-x1; x4:=p-x2;
    if x le x1 and x le x2 and x le x3 and x le x4 then
      for y in [1,w,w2,w3,w4,w5] do
      for z in [0..p-1] do
        count:=count+1;
        GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                                 (c,b)=d*e^-1*f^r, a^p=f^y, b^p=f^z, c^p=f^x>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
      end for;
    end if;
  end for;
else;
  for x in [1..p-1] do
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                               (c,b)=d*e^-1*f^r, a^p=f, b^p=f^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                               (c,b)=d*e^-1*f^r, a^p=f^w, b^p=f^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
  for x in [1..((p-1) div 2)] do
  for y in [0..p-1] do
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                               (c,b)=d*e^-1*f^r, a^p=f, b^p=f^y, c^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(d,a),f=(e,a),(b,a,b)=f, (c,a), 
                               (c,b)=d*e^-1*f^r, a^p=f^w, b^p=f^y, c^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
  end for;
end if;
//print count-count1,p^2+2*p-2+2*Gcd(p-1,3)+Gcd(p-1,4)+Gcd(p-1,5);

vprint Orderp7, 1: "Group 6.362 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is p^2 + 7p + 3 + 2gcd(p-1,3) + 3gcd(p-1,4) + gcd(p-1,5) =",
p^2+7*p+3+2*Gcd(p-1,3)+3*Gcd(p-1,4)+Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;
