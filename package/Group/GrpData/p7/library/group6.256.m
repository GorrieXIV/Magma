freeze;

import "misc.m": ProcessPresentation; 

Group6_256 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.256 valid only for p>3"; return false; end if;
 
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

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c), 
                      a^p=(b,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c), a^p, 
                      b^p=(b,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c), a^p, 
                        b^p=(b,a,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c), a^p, 
                        b^p=(b,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=5;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c), a^p, b^p, 
                          c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count,3+Gcd(p-1,3);
//count1:=count;
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,c), 
                            a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,c), 
                            a^p=(b,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,c), 
                            a^p, b^p=(b,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,c), 
                              a^p, b^p=(b,a,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,c), 
                              a^p, b^p=(b,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,c), 
                          a^p, b^p, c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,3+Gcd(p-1,3);
//count1:=count;
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), (c,a,c), 
                            a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), (c,a,c), 
                            a^p=(b,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), (c,a,c), 
                            a^p=(b,a,a,a)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), (c,a,c), 
                              a^p=(b,a,a,a)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), (c,a,c), 
                              a^p=(b,a,a,a)^w3, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), (c,a,c), 
                          a^p, b^p=(b,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), (c,a,c), 
                              a^p, b^p=(b,a,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), (c,a,c), 
                              a^p, b^p=(b,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), (c,a,c), 
                          a^p, b^p, c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,2+Gcd(p-1,3)+Gcd(p-1,4);
//count1:=count;
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a),
                           (c,a,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a),
                           (c,a,c), a^p=(b,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a),
                           (c,a,c), a^p=(b,a,a,a)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a),
                             (c,a,c), a^p=(b,a,a,a)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a),
                             (c,a,c), a^p=(b,a,a,a)^w3, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a),
                         (c,a,c), a^p, b^p=(b,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a),
                             (c,a,c), a^p, b^p=(b,a,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a),
                             (c,a,c), a^p, b^p=(b,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a),
                           (c,a,c), a^p, b^p, c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(b,a,a,a), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a),
                           (c,a,c), a^p, b^p, c^p=(b,a,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
//print count-count1,3+Gcd(p-1,3)+Gcd(p-1,4);
//count1:=count;
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c)=(b,a,a,a), (c,a,a), (c,a,c), 
                            a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c)=(b,a,a,a), (c,a,a), (c,a,c), 
                            a^p=(b,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c)=(b,a,a,a), (c,a,a), (c,a,c), 
                            a^p, b^p=(b,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c)=(b,a,a,a), (c,a,a), (c,a,c), 
                              a^p, b^p=(b,a,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c)=(b,a,a,a), (c,a,a), (c,a,c), 
                              a^p, b^p=(b,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c)=(b,a,a,a), (c,a,a), (c,a,c), 
                          a^p, b^p=(b,a,a,a), c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c)=(b,a,a,a), (c,a,a), (c,a,c), 
                              a^p, b^p=(b,a,a,a)^w, c^p=(b,a,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c)=(b,a,a,a), (c,a,a), (c,a,c), 
                              a^p, b^p=(b,a,a,a)^w2, c^p=(b,a,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c)=(b,a,a,a), (c,a,a), (c,a,c), 
                          a^p, b^p, c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
//print count-count1,3+2*Gcd(p-1,3);
//count1:=count;
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a,a), 
                            a^p=(b,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a,a), 
                            a^p=(b,a,a,a)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a,a), 
                            a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a,a), 
                            a^p, b^p=(b,a,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a,a), 
                              a^p, b^p=(b,a,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a,a), 
                              a^p, b^p=(b,a,a,a)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a,a), 
                            a^p, b^p, c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a,a), 
                            a^p, b^p=(b,a,a,a), c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a,a), 
                              a^p, b^p=(b,a,a,a)^w, c^p=(b,a,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b), (b,a,c), (c,a,a), (c,a,c)=(b,a,a,a), 
                              a^p, b^p=(b,a,a,a)^w2, c^p=(b,a,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
//print count-count1,4+2*Gcd(p-1,3);
//count1:=count;
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                           (c,a,c)=(b,a,a,a), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                           (c,a,c)=(b,a,a,a), a^p=(b,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                           (c,a,c)=(b,a,a,a), a^p=(b,a,a,a)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,a,a), a^p=(b,a,a,a)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,a,a), a^p=(b,a,a,a)^w3, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                         (c,a,c)=(b,a,a,a), a^p, b^p, c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,a,a), a^p, b^p, c^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,a,a), a^p, b^p, c^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                  (c,a,c)=(b,a,a,a), a^p, b^p=(b,a,a,a), c^p=(b,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
if p mod 3 eq 1 then
  for x in [0..((p-1) div 2)] do
    GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                  (c,a,c)=(b,a,a,a), a^p, b^p=(b,a,a,a)^w, c^p=(b,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a), (b,a,c), (c,a,a), 
                  (c,a,c)=(b,a,a,a), a^p, b^p=(b,a,a,a)^w2, c^p=(b,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
end if;
//print count-count1,1+(p+3)*Gcd(p-1,3)/2+Gcd(p-1,4);
//count1:=count;
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                           (c,a,c)=(b,a,a,a), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                           (c,a,c)=(b,a,a,a), a^p=(b,a,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                           (c,a,c)=(b,a,a,a), a^p=(b,a,a,a)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                     (c,a,c)=(b,a,a,a), a^p=(b,a,a,a)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                    (c,a,c)=(b,a,a,a), a^p=(b,a,a,a)^w3, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                (c,a,c)=(b,a,a,a), a^p, b^p, c^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,a,a), a^p, b^p, c^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,a,a), a^p, b^p, c^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                  (c,a,c)=(b,a,a,a), a^p, b^p=(b,a,a,a), c^p=(b,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 3 eq 1 then
    GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                      (c,a,c)=(b,a,a,a), a^p, b^p=(b,a,a,a)^w, c^p=(b,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a,a)^w, (b,a,c), (c,a,a), 
                      (c,a,c)=(b,a,a,a), a^p, b^p=(b,a,a,a)^w2, c^p=(b,a,a,a)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
//print count-count1,1+(p+3)*Gcd(p-1,3)/2+Gcd(p-1,4);

vprint Orderp7, 1: "Group 6.256 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 20 + (p+11)gcd(p-1,3) + 4gcd(p-1,4) =",
20+(p+11)*Gcd(p-1,3)+4*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
