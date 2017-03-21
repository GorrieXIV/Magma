freeze;

import "misc.m": ProcessPresentation; 

Group6_131 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.131 valid only for p>3"; return false; end if;

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
w4:=w^4 mod p;
w5:=w^5 mod p;
w6:=w^6 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e^-1, (c,b), 
                      a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e^-1, (c,b), 
                      a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e^-1, (c,b), 
                      a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e^-1, (c,b), 
                      a^p, b^p=e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e^-1, (c,b), 
                      a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=5;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e^-1, (c,b), 
                              a^p=e^w, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e^-1, (c,b), 
                              a^p=e^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e^-1, (c,b), 
                          a^p=e, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e^-1, (c,b), 
                              a^p=e^w, b^p=e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e^-1, (c,b), 
                              a^p=e^w2, b^p=e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b), 
                            a^p=(b,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b), a^p, 
                            b^p=(b,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b), a^p, 
                              b^p=(b,a,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b), a^p, 
                              b^p=(b,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b), a^p, b^p, 
                            c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b)=(b,a,a,a),
                            a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b)=(b,a,a,a),
                            a^p=(b,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 7 eq 1 then
  for x in [w,w2,w3,w4,w5,w6] do
    count:=count+1;
    GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b)=(b,a,a,a),
                              a^p=(b,a,a,a)^x, b^p, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b)=(b,a,a,a),
                            a^p, b^p=(b,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b)=(b,a,a,a),
                            a^p, b^p=(b,a,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  for x in [w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b)=(b,a,a,a),
                              a^p, b^p=(b,a,a,a)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
count:=count+1;
GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b)=(b,a,a,a),
                          a^p, b^p, c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b)=(b,a,a,a),
                              a^p, b^p, c^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a,b), (b,a,b,b), (c,a)=(b,a,b), (c,b)=(b,a,a,a),
                              a^p, b^p, c^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e, 
                           (c,a)=d*e^-1, (c,b), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e, 
                           (c,a)=d*e^-1, (c,b), a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e, 
                             (c,a)=d*e^-1, (c,b), a^p, b^p=e^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e, 
                             (c,a)=d*e^-1, (c,b), a^p, b^p=e^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e, 
              (c,a)=d*e^-1, (c,b), a^p=e, b^p=e^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 3 eq 1 then
    GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e, 
                 (c,a)=d*e^-1, (c,b), a^p=e^w, b^p=e^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e, 
                 (c,a)=d*e^-1, (c,b), a^p=e^w2, b^p=e^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e, 
                   (c,a)=d*e^-1, (c,b), a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e, 
                   (c,a)=d*e^-1, (c,b), a^p, b^p, c^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e^w, 
                           (c,a)=d*e^-w, (c,b), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e^w, 
                           (c,a)=d*e^-w, (c,b), a^p, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e^w, 
                       (c,a)=d*e^-w, (c,b), a^p, b^p=e^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e^w, 
                       (c,a)=d*e^-w, (c,b), a^p, b^p=e^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e^w, 
               (c,a)=d*e^-w, (c,b), a^p=e, b^p=e^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 3 eq 1 then
    GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e^w, 
                  (c,a)=d*e^-w, (c,b), a^p=e^w, b^p=e^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e^w, 
                  (c,a)=d*e^-w, (c,b), a^p=e^w2,b^p=e^x,c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e^w, 
                         (c,a)=d*e^-w, (c,b), a^p, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,b),e=(b,a,a,a),(b,a,a,b), (b,a,b,b)=e^w, 
                           (c,a)=d*e^-w, (c,b), a^p, b^p, c^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
GR:=Group<a,b,c | (b,a,a,a), (b,a,b,b), (c,a)=(b,a,b), (c,b), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a), (b,a,b,b), (c,a)=(b,a,b), (c,b), a^p, 
                            b^p=(b,a,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a), (b,a,b,b), (c,a)=(b,a,b), (c,b), 
                            a^p=(b,a,a,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a), (b,a,b,b), (c,a)=(b,a,b), (c,b), 
                            a^p=(b,a,a,b), b^p=(b,a,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (b,a,a,a), (b,a,b,b), (c,a)=(b,a,b), (c,b), 
                              a^p=(b,a,a,b), b^p=(b,a,a,b)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a,a), (b,a,b,b), (c,a)=(b,a,b), (c,b), 
                              a^p=(b,a,a,b), b^p=(b,a,a,b)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (b,a,a,a), (b,a,b,b), (c,a)=(b,a,b), (c,b), a^p, b^p, 
                            c^p=(b,a,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a,a), (b,a,b,b), (c,a)=(b,a,b), (c,b), a^p, b^p, 
                            c^p=(b,a,a,b)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;

vprint Orderp7, 1: "Group 6.131 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 15 + (p+10)gcd(p-1,3) + gcd(p-1,4) + gcd(p-1,7) =",
15+(p+10)*Gcd(p-1,3)+Gcd(p-1,4)+Gcd(p-1,7);

if Process then return Nmr; else return L; end if;

end function;
