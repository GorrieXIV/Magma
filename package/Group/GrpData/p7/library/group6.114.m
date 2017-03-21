freeze;

import "misc.m": ProcessPresentation; 

Group6_114 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.114 valid only for p>3"; return false; end if;

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

Z:=Integers();
V1:=VectorSpace(F,1);
V2:=VectorSpace(F,2);
H21:=Hom(V2,V1);
H22:=Hom(V2,V2);

mats:=[];

count:=0;

for x in [0..p-2] do
if x eq 3 then continue; end if;

C:=H22![x-1,1,-1,0];
D:=H22![x^2-2*x,x-1,1-x,-1];

for z in [0..p-1] do
A:=H21![1,z];
new:=1;

G:=C*A;
y:=G[1][1];
if y ne 0 then
  G:=y^-1*G;
  z1:=Z!(G[2][1]);
  if z1 lt z then new:=0; end if;
end if;

G:=D*A;
y:=G[1][1];
if y ne 0 then
  G:=y^-1*G;
  z1:=Z!(G[2][1]);
  if z1 lt z then new:=0; end if;
end if;

for c in [0..p-2] do
if F!(c*x+c^2-c+1) eq 0 then continue; end if;
E:=H22![(1+c*x)*(c*x-2*c+1),c*(c*x+2-c),-c*(c*x+2-c),-(-1+c)*(c+1)];
G:=E*A;
y:=G[1][1];
if y ne 0 then
  G:=y^-1*G;
  z1:=Z!(G[2][1]);
  if z1 lt z then new:=0; break; end if;
end if;
end for;

if new eq 1 then
  count:=count+1;
  mats[count]:=[x,z];
end if;

end for;

end for;

r:=(p+1) div 2;
s:=(p-1) div 2;
t:=(p+3) div 2;
u:=(p+7) div 2; u:=u mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=(c,b),g=(b,a,b),(b,a,c), a^p=d*g^s, b^p=f*g^-1, 
                      c^p=d^-1*e*g^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=(c,b),g=(b,a,b),(b,a,c)=g, a^p=d*g^s, 
                          b^p=f*g^s, c^p=d^-1*e*g^(x-s)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=(c,b),g=(b,a,b),(b,a,c), a^p=d*g^s, 
                        b^p=f*g, c^p=d^3*e*g^-t>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=(c,b),g=(b,a,b),(b,a,c)=g^-1, a^p=d*g^s, 
                        b^p=f*g^r, c^p=d^3*e*g^-u>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=p+3;
for A in mats do
  x:=A[1]; z:=A[2];
  t:=(s*(x+z)+r) mod p;
  u:=(s*x*z+r*x+s*z) mod p;
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=(c,b),g=(b,a,b),(b,a,c)=g^z, a^p=d*g^s,  
                            b^p=f*g^-t, c^p=d^x*e*g^-u>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.114 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 4p - 4 =",4*p-4;

if Process then return Nmr; else return L; end if;

end function;
