freeze;

import "misc.m": ProcessPresentation; 

Group5_38 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "5.38 valid only for p>3"; return false; end if;

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

Z:=Integers();
V2:=VectorSpace(F,2);
H22:=Hom(V2,V2);

//Case babb=baaa
mats1:={};

for y1 in [0..(p-1) div 2] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

new :=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A:=H22![y1,y2,y3,y4];

for a in [0..p-1] do
for b in [0..p-1] do

if a ne b and a ne p-b then

B:=H22![a,b,b,a];
C:=H22![a^4-b^4,2*a*b*(a^2-b^2),2*a*b*(a^2-b^2),a^4-b^4];
D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

B:=H22![a,b,-b,-a];
C:=H22![-a^4+b^4,-2*a*b*(a^2-b^2),2*a*b*(a^2-b^2),a^4-b^4];
D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  Include(~mats1,[y1,y2,y3,y4]);
end if;

end for;
end for;
if #mats1 eq (Gcd(p-1,3)*(p^2+3*p+11)+1)/2 then break; end if;
end for;
if #mats1 eq (Gcd(p-1,3)*(p^2+3*p+11)+1)/2 then break; end if;
end for;

//Case babb=wbaaa
mats2:={};

for y1 in [0..(p-1) div 2] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

new :=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A:=H22![y1,y2,y3,y4];

for a in [0..p-1] do
for b in [0..p-1] do

if a+b ne 0 then

B:=H22![a,b,w*b,a];
C:=H22![a^4-w^2*b^4,2*a*b*(a^2-w*b^2),2*w*a*b*(a^2-w*b^2),a^4-w^2*b^4];
D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;


B:=H22![a,b,-w*b,-a];
C:=H22![-a^4+w^2*b^4,-2*a*b*(a^2-w*b^2),2*w*a*b*(a^2-w*b^2),a^4-w^2*b^4];
D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  Include(~mats2,[y1,y2,y3,y4]);
end if;

end for;
end for;
if #mats2 eq (Gcd(p-1,3)*(p^2+p+1)+5)/2 then break; end if;
end for;
if #mats2 eq (Gcd(p-1,3)*(p^2+p+1)+5)/2 then break; end if;
end for;

w2:=w^2 mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b|(b,a,b,b),a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,b,b),a^p,b^p=(b,a,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,c|c=(b,a,a,b),(b,a,b,b),a^p=(b,a,a,a),b^p=c^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b|(b,a,b,b),a^p=(b,a,a,b),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|c=(b,a,a,a),d=(b,a,a,b),(b,a,b,b),a^p=c*d,b^p=d^2>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=p+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(b,a,a,b),(b,a,b,b),a^p=c*d^w,b^p=d^2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(b,a,a,b),(b,a,b,b),a^p=c*d^w2,b^p=d^2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
end if;
GR:=Group<a,b|(b,a,b,b),a^p,b^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,b,b),a^p=(b,a,a,b),b^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b|(b,a,b,b),a^p=(b,a,a,b)^w,b^p=(b,a,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(b,a,a,b),(b,a,b,b),a^p=d^x,b^p=c*d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+p;
if p mod 3 eq 1 then
  GR:=Group<a,b|(b,a,b,b),a^p,b^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b|(b,a,b,b),a^p=(b,a,a,b),b^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b|(b,a,b,b),a^p=(b,a,a,b)^w,b^p=(b,a,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  for x in [0..p-1] do
    GR:=Group<a,b,c,d|c=(b,a,a,a),d=(b,a,a,b),(b,a,b,b),a^p=d^x,b^p=c^w*d>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  count:=count+3+p;
  GR:=Group<a,b|(b,a,b,b),a^p,b^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b|(b,a,b,b),a^p=(b,a,a,b),b^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b|(b,a,b,b),a^p=(b,a,a,b)^w,b^p=(b,a,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  for x in [0..p-1] do
    GR:=Group<a,b,c,d|c=(b,a,a,a),d=(b,a,a,b),(b,a,b,b),a^p=d^x,b^p=c^w2*d>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  count:=count+p+3;
end if;
//print count,p+3+(p+4)*Gcd(p-1,3);
count1:=count;
for A in mats1 do
  x:=A[1]; y:=A[2]; z:=A[3]; t:=A[4];
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(b,a,a,b),(b,a,b,b)=c,a^p=c^x*d^y,b^p=c^z*d^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
//print count-count1,(Gcd(p-1,3)*(p^2+3*p+11)+1)/2;
count1:=count;
for A in mats2 do
  x:=A[1]; y:=A[2]; z:=A[3]; t:=A[4];
  count:=count+1;
  GR:=Group<a,b,c,d|c=(b,a,a,a),d=(b,a,a,b),(b,a,b,b)=c^w,a^p=c^x*d^y,b^p=c^z*d^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
//print count-count1,(Gcd(p-1,3)*(p^2+p+1)+5)/2;

vprint Orderp7, 1: "Group 5.38 has",count,"descendants of order p^7 and class 4";

vprint Orderp7, 2:"Total number of groups is gcd(p-1,3)(p^2 + 3p + 10) + p + 6 =",
Gcd(p-1,3)*(p^2+3*p+10)+p+6;

if Process then return Nmr; else return L; end if;

end function;

Children6 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_38 (p: Process:=Process, Select:=Select);
end function;
