freeze;

import "misc.m": ProcessPresentation; 

Group5_16 := function (p: Process:=true, Select:=func<x|true>, Limit := 0)

if p lt 5 then "5.16 valid only for p>3"; return false; end if;

class:=3;
limited := not Process and Limit ge 1;

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

GR:=Group<a,b,c | (c,b),a^p,b^p=(b,a),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p,b^p=d*e,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p,b^p=d*f,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;

GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e,b^p=d,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e,b^p=d*f,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e,b^p=d*e*f^x,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
count:=p+5;

GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f,b^p=d,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f,b^p=d*e,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f,b^p=d*f,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f^w,b^p=d,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f^w,b^p=d*e,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f^w,b^p=d*f,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+6;
for x in [1..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p,b^p=d,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p,b^p=d*f,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p,b^p=d*e,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p,b^p=d*e*f,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f,b^p=d,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f,b^p=d*e,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+6;
  for y in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f,b^p=d*e^y*f,c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f^w,b^p=d,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f^w,b^p=d*e,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
  for y in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=f^w,b^p=d*e^y*f,c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
  for z in [0..p-1] do
    GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e*f^z,b^p=d,c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e*f^z,b^p=d*f,c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    count:=count+2;
    for y in [0..p-1] do
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e*f^z,b^p=d*e*f^y,c^p=e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    end for;
  end for;
end for;
for x in [0..p-1] do
  if x ne 1 then
    GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e^x,b^p=d,c^p=f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e^x,b^p=d*f,c^p=f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    count:=count+2;
    for y in [0..p-1] do
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e^x,b^p=d*e*f^y,c^p=f>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    end for;
  end if;
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e*f^x,b^p=d,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e*f^x,b^p=d*f,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=e*f^x,b^p=d*e,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+3;
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p,b^p=d,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=f,b^p=d,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=f^w,b^p=d,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+3;
  for y in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=f^y,b^p=d,c^p=e^x*f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    for z in [0..p-1] do
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=e*f^y,b^p=d,c^p=e^x*f^z>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    end for;
  end for;
end for;
for y in [0..p-1] do
for z in [0..p-1] do
for t in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=f^y,b^p=d*f,c^p=e^z*f^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
for x in [1..((p-1) div 2)] do
for y in [0..p-1] do
for z in [0..p-1] do
for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=e^x*f^y,b^p=d*f,c^p=e^z*f^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
end for;
for y in [0..p-1] do
for z in [0..p-1] do
for t in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=f^y,b^p=d*f^w,c^p=e^z*f^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
for x in [1..((p-1) div 2)] do
for y in [0..p-1] do
for z in [0..p-1] do
for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=e^x*f^y,b^p=d*f^w,c^p=e^z*f^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
end for;

vprint Orderp7, 1: "Group 5.16 has",count,"descendants of order p^7 and class 3";

vprint Orderp7, 2: "Total number of groups is p^4 + 2p^3 + 5p^2 + 14p =",
p^4+2*p^3+5*p^2+14*p;

if Process then return Nmr; else return L; end if;

end function;

Children33 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_16 (p: Process:=Process, Select:=Select);
end function;

