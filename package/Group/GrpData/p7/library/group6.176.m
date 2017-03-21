freeze;

import "misc.m": ProcessPresentation; 

Group6_176 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.176 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;

count:=0;

for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                            a^p=d, b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
QU:=1;
if p mod 4 eq 3 then
  for y in [1..((p-1) div 2)] do
    for x in [0..p-1] do
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                                a^p=d, b^p=f^y, c^p=f^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end for;
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                              a^p=d*f^y, b^p, c^p=f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    for z in [1..p-1] do
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                  a^p=d*f^z, b^p=f^y, c^p=f>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end for;
  end for;
else;
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for y in [1..((p-1) div 2)] do
    y1:=(QU*y) mod p; y2:=p-y1;
    if y le y1 and y le y2 then
      for x in [0..p-1] do
        count:=count+1;
        GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                                  a^p=d, b^p=f^y, c^p=f^x>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                                a^p=d*f^y, b^p, c^p=f>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      for z in [1..p-1] do
        count:=count+1;
        GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                    a^p=d*f^z, b^p=f^y, c^p=f>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
end if;

if p mod 4 eq 1 then
  for x in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                              a^p=d^w, b^p, c^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  for y in [1..((p-1) div 2)] do
    y1:=(QU*y) mod p; y2:=p-y1;
    if y le y1 and y le y2 then
      for x in [0..p-1] do
        count:=count+1;
        GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                                  a^p=d^w, b^p=f^y, c^p=f^x>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                                a^p=d^w*f^y, b^p, c^p=f^w>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      for z in [1..p-1] do
        count:=count+1;
        GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b)=d^w, 
                    a^p=d^w*f^z, b^p=f^y, c^p=f^w>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
end if;

vprint Orderp7, 1: "Groups 6.176 and 6.177 have",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p(p-1) + pgcd(p-1,4)/2 =",
p*(p-1)+p*Gcd(p-1,4)/2;

if Process then return Nmr; else return L; end if;

end function;
