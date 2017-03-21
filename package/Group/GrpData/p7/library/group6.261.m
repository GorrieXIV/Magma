freeze;

import "misc.m": ProcessPresentation; 

Group6_261 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.261 valid only for p>3"; return false; end if;
 
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
r:=(p-1) div 2;

L:=[]; Nmr := 0;
count:=0;

for x in [0..p-2] do
  if x eq r then continue; end if;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^x, 
                             (c,a,a), (c,a,c), a^p, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^x, 
                             (c,a,a), (c,a,c), a^p=e, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^x, 
                             (c,a,a), (c,a,c), a^p, b^p, c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^x, 
                             (c,a,a), (c,a,c), a^p, b^p=e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
  if p mod 3 eq 1 then
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^x, 
                               (c,a,a), (c,a,c), a^p, b^p=e^w, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^x, 
                               (c,a,a), (c,a,c), a^p, b^p=e^w2, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^x, 
                           (c,a,a), (c,a,c), a^p, b^p=e, c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 3 eq 1 then
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^x, 
                               (c,a,a), (c,a,c), a^p, b^p=e^w, c^p=e>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^x, 
                               (c,a,a), (c,a,c), a^p, b^p=e^w2, c^p=e>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
//print count,(p-2)*(3+2*Gcd(p-1,3));
//count1:=count;
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^-1, 
                           (c,a,a), (c,a,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^-1, 
                           (c,a,a), (c,a,c), a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^-1, 
                           (c,a,a), (c,a,c), a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^-1, 
                           (c,a,a), (c,a,c), a^p=e, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^-1, 
                           (c,a,a), (c,a,c), a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+5;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^-1, 
                             (c,a,a), (c,a,c), a^p, b^p=e^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^-1, 
                             (c,a,a), (c,a,c), a^p, b^p=e^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^-1, 
                         (c,a,a), (c,a,c), a^p, b^p=e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^-1, 
                    (c,a,a), (c,a,c), a^p, b^p=e^w, c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^-1, 
                    (c,a,a), (c,a,c), a^p, b^p=e^w2, c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
//print count-count1,4+2*Gcd(p-1,3);
//count1:=count;
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^r, 
                           (c,a,a), (c,a,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^r, 
                           (c,a,a), (c,a,c), a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^r, 
                           (c,a,a), (c,a,c), a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^r, 
                             (c,a,a), (c,a,c), a^p, b^p=e^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^r, 
                             (c,a,a), (c,a,c), a^p, b^p=e^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b), (b,a,c)=e^r, 
                         (c,a,a), (c,a,c), a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,3+Gcd(p-1,3);
//count1:=count;
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                  (b,a,c)=e^r, (c,a,a), (c,a,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                  (b,a,c)=e^r, (c,a,a), (c,a,c), a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                  (b,a,c)=e^r, (c,a,a), (c,a,c), a^p=e^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                    (b,a,c)=e^r, (c,a,a), (c,a,c), a^p=e^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                    (b,a,c)=e^r, (c,a,a), (c,a,c), a^p=e^w3, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                (b,a,c)=e^r, (c,a,a), (c,a,c), a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                    (b,a,c)=e^r, (c,a,a), (c,a,c), a^p, b^p=e^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                    (b,a,c)=e^r, (c,a,a), (c,a,c), a^p, b^p=e^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                (b,a,c)=e^r, (c,a,a), (c,a,c), a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                    (b,a,c)=e^r, (c,a,a), (c,a,c), a^p, b^p, c^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e, 
                    (b,a,c)=e^r, (c,a,a), (c,a,c), a^p, b^p, c^p=e^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
//print count-count1,1+2*Gcd(p-1,3)+Gcd(p-1,4);
//count1:=count;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                             (c,a,a), (c,a,c)=e, a^p, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                             (c,a,a), (c,a,c)=e, a^p=e, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                             (c,a,a), (c,a,c)=e, a^p=e^w, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
  if p mod 4 eq 1 then
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                               (c,a,a), (c,a,c)=e, a^p=e^w2, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                               (c,a,a), (c,a,c)=e, a^p=e^w3, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                           (c,a,a), (c,a,c)=e, a^p, b^p=e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 3 eq 1 then
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                               (c,a,a), (c,a,c)=e, a^p, b^p=e^w, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                               (c,a,a), (c,a,c)=e, a^p, b^p=e^w2, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
  for y in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                (c,a,a), (c,a,c)=e, a^p, b^p=e^y, c^p=e>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if p mod 3 eq 1 then
      GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                (c,a,a), (c,a,c)=e, a^p, b^p=e^y, c^p=e^w>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|d=(b,a,a),e=(d,a),(c,b)=d*e^-1, (b,a,b)=e^x, (b,a,c), 
                (c,a,a), (c,a,c)=e, a^p, b^p=e^y, c^p=e^w2>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+2;
    end if;
  end for;
end for;
//print count-count1,p*(1+(p+1)*Gcd(p-1,3)+Gcd(p-1,4));

vprint Orderp7, 1: "Group 6.261 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 4p + 2 + (p^2+3p+1)gcd(p-1,3) + (p+1)gcd(p-1,4) =",
4*p+2+(p^2+3*p+1)*Gcd(p-1,3)+(p+1)*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
