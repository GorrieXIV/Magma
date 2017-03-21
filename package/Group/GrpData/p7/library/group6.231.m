freeze;

import "misc.m": ProcessPresentation; 

Group6_231 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.231 valid only for p>3"; return false; end if;
 
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
w7:=w^7 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c), 
                      a^p=(b,a,b,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c), 
                     a^p=(b,a,b,b)^w, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c), 
                     a^p=(b,a,b,b)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c), a^p, 
                            b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c), 
                            a^p=(b,a,b,b), b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c), 
                     a^p=(b,a,b,b)^w, b^p=(b,a,b,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c), 
                     a^p=(b,a,b,b)^w2, b^p=(b,a,b,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c), a^p, b^p, 
                 c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                   a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                   a^p=(b,a,b,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                              a^p=(b,a,b,b)^w, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                              a^p=(b,a,b,b)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                            a^p, b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                            a^p=(b,a,b,b), b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                              a^p=(b,a,b,b)^w, b^p=(b,a,b,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                              a^p=(b,a,b,b)^w2, b^p=(b,a,b,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                            a^p, b^p, c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                            a^p, b^p=(b,a,b,b), c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                            a^p, b^p=(b,a,b,b)^w, c^p=(b,a,b,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                            a^p, b^p, c^p=(b,a,b,b)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                            a^p, b^p=(b,a,b,b), c^p=(b,a,b,b)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a)=(b,a,b,b), (c,a,c), 
                            a^p, b^p=(b,a,b,b)^w, c^p=(b,a,b,b)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;

GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                            a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                            a^p=(b,a,b,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                              a^p=(b,a,b,b)^w, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                              a^p=(b,a,b,b)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                            a^p, b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                            a^p=(b,a,b,b), b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                              a^p=(b,a,b,b)^w, b^p=(b,a,b,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                              a^p=(b,a,b,b)^w2, b^p=(b,a,b,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                            a^p, b^p, c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                            a^p=(b,a,b,b), b^p, c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                              a^p=(b,a,b,b)^w, b^p, c^p=(b,a,b,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a), (c,a,c), 
                              a^p=(b,a,b,b)^w2, b^p, c^p=(b,a,b,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a)=(b,a,b,b),
                         (c,a,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a)=(b,a,b,b),
                           (c,a,c), a^p=(b,a,b,b), b^p=(b,a,b,b)^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 3 eq 1 then
    GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a)=(b,a,b,b),
                               (c,a,c), a^p=(b,a,b,b)^w, b^p=(b,a,b,b)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a)=(b,a,b,b),
                               (c,a,c), a^p=(b,a,b,b)^w2, b^p=(b,a,b,b)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a)=(b,a,b,b),
                         (c,a,c), a^p, b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a)=(b,a,b,b),
                             (c,a,c), a^p, b^p=(b,a,b,b)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a)=(b,a,b,b),
                             (c,a,c), a^p, b^p=(b,a,b,b)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a)=(b,a,b,b),
                             (c,a,c), a^p, b^p=(b,a,b,b)^x, c^p=(b,a,b,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c)=(b,a,b,b), (c,a,a)=(b,a,b,b),
                             (c,a,c), a^p, b^p=(b,a,b,b)^x, c^p=(b,a,b,b)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;

GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                            a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                            a^p, b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                            a^p, b^p=(b,a,b,b)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                              a^p, b^p=(b,a,b,b)^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                              a^p, b^p=(b,a,b,b)^w3, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                          a^p=(b,a,b,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                              a^p=(b,a,b,b)^w, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                              a^p=(b,a,b,b)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
CU:=1;
if p mod 3 eq 2 then
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                              a^p=(b,a,b,b), b^p=(b,a,b,b)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
else;
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [1..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                                  a^p=(b,a,b,b), b^p=(b,a,b,b)^x, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                                  a^p=(b,a,b,b)^w, b^p=(b,a,b,b)^x, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                                  a^p=(b,a,b,b)^w2, b^p=(b,a,b,b)^x, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+3;
    end if;
  end for;
end if;
count:=count+1;
GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), (c,a,c), 
                          a^p, b^p, c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                            a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b),
                            a^p, b^p, c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                            a^p, b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                            a^p, b^p=(b,a,b,b), c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                            a^p=(b,a,b,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                            a^p=(b,a,b,b)^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w3, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w4, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w5, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                            a^p=(b,a,b,b), b^p, c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                            a^p=(b,a,b,b)^w, b^p, c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w2, b^p, c^p=(b,a,b,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w3, b^p, c^p=(b,a,b,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w4, b^p, c^p=(b,a,b,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w5, b^p, c^p=(b,a,b,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                            a^p=(b,a,b,b), b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                            a^p=(b,a,b,b)^w, b^p=(b,a,b,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w2, b^p=(b,a,b,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w3, b^p=(b,a,b,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w4, b^p=(b,a,b,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                              a^p=(b,a,b,b)^w5, b^p=(b,a,b,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
if p mod 3 eq 2 then
  for x in [1..((p-1) div 2)] do
    GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                       a^p=(b,a,b,b), b^p=(b,a,b,b), c^p=(b,a,b,b)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                       a^p=(b,a,b,b)^w, b^p=(b,a,b,b), c^p=(b,a,b,b)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
else;
  for x in [1..((p-1) div 2)] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p; x3:=p-x1; x4:=p-x2;
    if x le x1 and x le x2 and x le x3 and x le x4 then
      GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                         a^p=(b,a,b,b), b^p=(b,a,b,b), c^p=(b,a,b,b)^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                         a^p=(b,a,b,b)^w, b^p=(b,a,b,b), c^p=(b,a,b,b)^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                         a^p=(b,a,b,b)^w2, b^p=(b,a,b,b), c^p=(b,a,b,b)^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                         a^p=(b,a,b,b)^w3, b^p=(b,a,b,b), c^p=(b,a,b,b)^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                         a^p=(b,a,b,b)^w4, b^p=(b,a,b,b), c^p=(b,a,b,b)^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c | (c,b), (b,a,a), (b,a,c), (c,a,a), (c,a,c)=(b,a,b,b), 
                         a^p=(b,a,b,b)^w5, b^p=(b,a,b,b), c^p=(b,a,b,b)^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+6;
    end if;
  end for;
end if;

GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                           (c,a,c)=(b,a,b,b), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                           (c,a,c)=(b,a,b,b), a^p, b^p, c^p=(b,a,b,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 7 eq 1 then
  for x in [w,w2,w3,w4,w5,w6] do
    count:=count+1;
    GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,b,b), a^p, b^p, c^p=(b,a,b,b)^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
QU:=1; OC:=1;
if p mod 4 eq 3 then
  for x in [1,w] do
    count:=count+1;
    GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,b,b), a^p, b^p=(b,a,b,b)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    for y in [1..((p-1) div 2)] do
      count:=count+1;
      GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                      (c,a,c)=(b,a,b,b), a^p, b^p=(b,a,b,b)^x, c^p=(b,a,b,b)^y>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end for;
  end for;
end if;
if p mod 8 eq 5 then
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for x in [1,w,w2,w3] do
    count:=count+1;
    GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,b,b), a^p, b^p=(b,a,b,b)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    for y in [1..((p-1) div 2)] do
      y1:=(QU*y) mod p; y2:=p-y1;
      if y le y1 and y le y2 then
        count:=count+1;
        GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                        (c,a,c)=(b,a,b,b), a^p, b^p=(b,a,b,b)^x, c^p=(b,a,b,b)^y>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end if;
    end for;
  end for;
end if;
if p mod 8 eq 1 then
  for i in [2..p-2] do
    if i^8 mod p eq 1 and i^4 mod p ne 1 then OC:=i; break; end if;
  end for;
  for x in [1,w,w2,w3,w4,w5,w6,w7] do
    count:=count+1;
    GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,b,b), a^p, b^p=(b,a,b,b)^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    for y in [1..((p-1) div 2)] do
      y1:=(OC*y) mod p; y2:=(OC*y1) mod p; y3:=(OC*y2) mod p;
      y4:=p-y1; y5:=p-y2; y6:=p-y3;
      if y le y1 and y le y2 and y le y3 and y le y4 and y le y5 and y le y6 then
        count:=count+1;
        GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                        (c,a,c)=(b,a,b,b), a^p, b^p=(b,a,b,b)^x, c^p=(b,a,b,b)^y>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end if;
    end for;
  end for;
end if;
if p mod 3 eq 2 then
  for x in [1,w] do
  for y in [0..p-1] do
  for z in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                             (c,a,c)=(b,a,b,b), 
                     a^p=(b,a,b,b)^x, b^p=(b,a,b,b)^y, c^p=(b,a,b,b)^z>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  end for;
  end for;
else;
  for x in [1,w,w2,w3,w4,w5] do
    for z in [0..p-1] do
      z1:=(CU*z) mod p; z2:=(CU*z1) mod p;
      if z le z1 and z le z2 then
        count:=count+1;
        GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                                 (c,a,c)=(b,a,b,b), 
                                  a^p=(b,a,b,b)^x, b^p=(b,a,b,b)^z, c^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end if;
    end for;
    for y in [1..((p-1) div 2)] do
      y1:=(CU*y) mod p; y2:=(CU*y1) mod p; y3:=p-y1; y4:=p-y2;
      if y le y1 and y le y2 and y le y3 and y le y4 then
        for z in [0..p-1] do
          count:=count+1;
          GR:=Group<a,b,c | (c,b), (b,a,a)=(b,a,b,b), (b,a,c), (c,a,a), 
                                   (c,a,c)=(b,a,b,b), 
                           a^p=(b,a,b,b)^x, b^p=(b,a,b,b)^z, c^p=(b,a,b,b)^y>;
          ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        end for;
      end if;
    end for;
  end for;
end if;

vprint Orderp7, 1: "Group 6.231 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p^2+5p+14+(p+17)gcd(p-1,3)+2gcd(p-1,4)+gcd(p-1,7)+gcd(p-1,8) =",
p^2+5*p+14+(p+17)*Gcd(p-1,3)+2*Gcd(p-1,4)+Gcd(p-1,7)+Gcd(p-1,8);

if Process then return Nmr; else return L; end if;

end function;
