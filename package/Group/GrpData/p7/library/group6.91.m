freeze;

import "misc.m": ProcessPresentation; 

Group6_91 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.91 valid only for p>3"; return false; end if;

class:=3;

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

L:=[]; Nmr := 0;



GR:=Group<a,b,c | (b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b), a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=b^p,(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b)=d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d | d=b^p,(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), d^p, 
                      a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), d^p, 
                      a^p=e^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), d^p, a^p, 
                      c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), d^p, 
                      a^p=e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), d^p, 
                      a^p=e^w, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,c),(b,a,a), (b,a,b), (b,a,c), (c,a,a), (c,b), 
                      d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), d^p, 
                       a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), d^p, 
                       a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), d^p, 
                       a^p=e^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), d^p, 
                       a^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), d^p, 
                       a^p=e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), d^p, 
                       a^p=e^w, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-1, (c,b), 
                       d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-w, (c,b), d^p,
                       a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-w, (c,b), d^p,
                       a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-w, (c,b), d^p,
                       a^p=e^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-w, (c,b), d^p,
                       a^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-w, (c,b), d^p,
                       a^p=e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-w, (c,b), d^p,
                       a^p=e^w, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c)=e^-w, (c,b), 
                       d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p, a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p, a^p=e^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p, a^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p, a^p=e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p, a^p=e^w, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c)=e, (c,b), 
                       d^p=e^w, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-1, 
                      (c,b), d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-1, 
                      (c,b), d^p, a^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=33;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-1, 
                        (c,b), d^p, a^p, c^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=34;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-1, 
                             (c,b), d^p, a^p=e, c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-1, 
                             (c,b), d^p, a^p=e^w, c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-1, 
                           (c,b), d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-1, 
                           (c,b), d^p=e^w, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-w, 
                           (c,b), d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-w, 
                           (c,b), d^p, a^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-w, 
                           (c,b), d^p, a^p, c^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-w, 
                             (c,b), d^p, a^p=e, c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-w, 
                             (c,b), d^p, a^p=e^w, c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-w, 
                           (c,b), d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c)=e^-w, 
                           (c,b), d^p=e^w, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a), (c,a,c), (c,b), d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a), (c,a,c), (c,b), d^p, a^p, 
                            c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a), (c,a,c), (c,b), d^p, 
                            a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a), (c,a,c), (c,b), d^p, 
                            a^p=e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a), (c,a,c), (c,b), 
                            d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a)=e, (c,a,c), (c,b), 
                            d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a)=e, (c,a,c), (c,b), 
                           d^p, a^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p, a^p, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p, a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p, a^p=e, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p, a^p=e, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,c),(b,a,a), (b,a,b), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), (c,b), d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), (c,b), d^p, a^p, 
                             c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), (c,b), d^p, a^p, 
                             c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), (c,b)=e, 
                             d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), (c,b)=e, 
                             d^p, a^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), (c,b)=e, 
                             d^p, a^p, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), (c,b), d^p, 
                             a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), (c,b)=e, 
                             d^p, a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), (c,b), 
                             d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(c,a,a),(b,a,a), (b,a,b), (b,a,c), (c,a,c), (c,b)=e, 
                             d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p, a^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p, a^p, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p, a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p, a^p=e^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a)=e, (c,a,c), (c,b), 
                             d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c), (c,b), d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c), (c,b), d^p, a^p, 
                             c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c), (c,b), d^p, 
                             a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c), (c,b), d^p, 
                             a^p=e^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,b),(b,a,a), (b,a,c), (c,a,a), (c,a,c), (c,b), 
                             d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b), d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b), d^p, a^p, 
                             c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b), d^p, 
                             a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b), 
                             d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b), 
                             d^p=e^w, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b)=e, 
                             d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b)=e, 
                             d^p, a^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b)=e, 
                             d^p, a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b)=e, 
                             d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b), (b,a,c), (c,a,a), (c,a,c), (c,b)=e, 
                             d^p=e^w, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c), (c,b), 
                             d^p, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c), (c,b), 
                             d^p, a^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c), (c,b), 
                             d^p, a^p=e^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c), (c,b), 
                             d^p, a^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c), (c,b), 
                             d^p=e, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=b^p,e=(b,a,a),(b,a,b)=e, (b,a,c), (c,a,a), (c,a,c), (c,b), 
                             d^p=e^w, a^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+51;

vprint Orderp7, 1: "Group 6.91 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 2p + 88 + gcd(p-1,4) =",
2*p+88+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
