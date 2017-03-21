freeze;

import "misc.m": ProcessPresentation; 

Group6_427 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.427 is valid only for p>5"; return false; end if;

//The following computes a set of reps for the equivalence
//classes of pairs [x,y], where [x,y]~[x',y'] if
//y^2-wx^2 = y'^2-wx'^2

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

L:=[]; Nmr := 0;
count:=0;
temp:=[0:j in [1..p]];
for x in [0..p-1] do
for y in [0..p-1] do
z:=y^2-w*x^2;
t:=F!z;
z:=1+Integers()!t;
if temp[z] eq 0 then
  temp[z]:=1;
  if x+y ne 0 then
    count:=count+1;
    GR:=Group<a,b,c,d,e,f |c=(b,a,a)^-w,d=(b,a,b)^-1,e=(b,a,a,a),f=(e,b),
                                  a^p=d*e^(x-w),b^p=c*e^(y+w)>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end if;
end if;
end for;
end for;

count:=count+1;
GR:=Group<a,b,c,d,e |c=(b,a,a)^-w,d=(b,a,b)^-1,e=(b,a,a,a),
                    (e,b),a^p=d*e^-w,b^p=c*e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
found:=0;
for y in [0..p-1] do
for x in [1..p-1] do
if (y^2) mod p eq (w*(x^2+1)) mod p then
  found:=1; x1:=x; y1:=y; break;
end if;
end for;
if found eq 1 then break; end if;
end for;

wx:=w*x1 mod p;
count:=count+1;
GR:=Group<a,b,c,d,e,f |c=(b,a,a)^-w,d=(b,a,b)^-1,e=(b,a,a,a),f=(e,b),
                             (b,a,a,a,a)^wx=f^-y1,a^p=d*e^-w, b^p=c*e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.427 has",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is p + 1 =",p+1;

if Process then return Nmr; else return L; end if;

end function;
