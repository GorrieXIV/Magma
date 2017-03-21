freeze;

forward Nielsen, Neumann;
intrinsic AutomorphismGroup(G :: GrpFP) -> GrpAuto
{The automorphism group of a free group G}
 /* The first two generators permute the generators of F and generate S_ng.
  * The third inverts the first generator of F.
  * The fourth maps F.1 -> F.1*F.2 and fixes the other generators of F.
  */
  local ng, genims, A;
  require #Relations(G) eq 0 : "For type GrpFP, group must be free";
  ng := Ngens(G);
  if ng eq 1 then
    genims := [[G.1^-1]];
    igenims := [[G.1^-1]];
  else
    genims := [ [G.2,G.1] cat [G.i : i in [3..ng]] ];
    igenims := [ [G.2,G.1] cat [G.i : i in [3..ng]] ];
    if ng gt 2 then
      Append( ~genims, [G.i : i in [2..ng]] cat [G.1] );
      Append( ~igenims, [G.ng] cat [G.i : i in [1..ng-1]] );
    end if;
    Append(~genims, [G.1^-1] cat [G.i : i in [2..ng]] );
    Append(~igenims, [G.1^-1] cat [G.i : i in [2..ng]] );
    Append( ~genims, [G.1*G.2] cat [G.i : i in [2..ng]] );
    Append( ~igenims, [G.1*G.2^-1] cat [G.i : i in [2..ng]] );
  end if;
  A := AutomorphismGroup( G, [G.i : i in [1..ng]], genims, igenims );
  A`Group := G;
  A`InnerGenerators := [];
  //for the presentation, we have used Neumann for ng=1,2, Nielsen for ng>=3
  A`FpGroup := 
     < F, hom<F->A | [A.i : i in [1..Ngens(A)]]> > where
       F := ng le 2 select Neumann(ng) else Nielsen(ng);
  return A;
end intrinsic;

WA1 := function(F)
// F = free group - return list of Type 1 Whitehead Automorphisms 
 n := Ngens(F);
 auts := [];
 S:=CartesianPower([-1,1],n);
 for p in Sym(n) do for s in S do
   ims := [ (F.(i^p))^s[i] : i in [1..n] ];
   Append(~auts, hom< F->F | ims >);
 end for; end for;
 return auts;
end function;

WA2 := function(F)
// F = free group - return list of Type 2 Whitehead Automorphisms 
 n := Ngens(F);
 auts := [];
 for i in [1..n] do for e in [-1,1] do
   a := F.i^e;
   allone := true;
   S := CartesianPower([1..4],n-1);
   for s in S do if not forall(x){x: x in [1..n-1] | s[x] eq 1} then
     ims := []; sct := 0;
     for j in [1..n] do
       if j eq i then
         ims[j] := F.i;
       else
         sct +:= 1;
         ims[j] := s[sct] eq 1 select F.j else s[sct] eq 2 select F.j*a
             else  s[sct] eq 3 select a^-1*F.j else a^-1*F.j*a;
       end if;
     end for;
     Append(~auts,hom< F->F | ims >);
   end if; end for;
  end for; end for;
  return auts;
end function;

intrinsic WhiteheadReduction(F :: GrpFP, l :: SeqEnum) -> BoolElt, SeqEnum, GrpAutoElt
{Perform Whitehead reduction of a sequence of elements of a free group F.
Return true/false if list was part of a free basis, the Whitehead reduction,
and corresponding automorphism of F}
  /* Whitehead reduce.
   * return true if fully reduced to part of free basis, false otherwise.
   * return also reduced list and automorphism of F mapping l to reduction.
   * If fully reduced, automorphism maps l to F.1, F.2, ...
   */
  local W, red, a, na, nb, nc, r, fr;
  require #Relations(F) eq 0 : "For type GrpFP, group must be free";
  r := Ngens(F);
  W := WA2(F);
  red := true;
  a := hom< F-> F | [F.i : i in [1..Ngens(F)]] >;
  fr := forall{ x : x in l | #x eq 1 } and
                        #{ Abs( Eltseq(e)[1] ) : e in l } eq #l;
  red := not fr;
  while red do
    red := false;
    for w in W do
      if &+[#w(x) : x in l] lt &+[#x : x in l] then
        l := [w(x) : x in l];
        a := a * w;
        fr := forall{ x : x in l | #x eq 1 } and
                        #{ Abs( Eltseq(e)[1] ) : e in l } eq #l;
        red := not fr;
        if fr then break; end if;
        //continue;
      end if;
    end for;
  end while;
  if fr then //fully reduced
    na := [ Eltseq(e)[1] : e in l ];
    nb := [ Sign(na[i]) * i : i in [1..#l] ];
    na := [ Abs(i) : i in na ];
    for i in [1..r] do if Position(na, i) eq 0 then
      Append(~na, i);
    end if; end for;
    nb cat:= [#l+1 .. r];
    nc := [ nb[ Position(na,i) ] : i in [1..r] ];
    a := a * hom< F-> F | [ F.nc[i] : i in [1..r] ] >;
    return true, [ F.i : i in [1..#l] ],
     AutomorphismGroup(F, [F.i : i in [1..r]], [[a(F.i) : i in [1..r]]]).1;
  else
    return false, l,
     AutomorphismGroup(F, [F.i : i in [1..r]], [[a(F.i) : i in [1..r]]]).1;
  end if;
end intrinsic;

WB := function(F,l)
  isit, rl := WhiteheadReduction(F,l);
  if &+[#x : x in rl] ne &+[#x : x in l] then
    error "WB: input not Whitehead reduced";
  end if;
  W1 := WA1(F);
  W2 := WA2(F);
  ball := {l};
  repeat
    ov := #ball;
    for b in ball do
      for w in W2 do
        if &+[#w(x) : x in b] eq &+[#x : x in b] then
          Include(~ball, [w(x) : x in b] );
        end if;
      end for;
    end for;
    nv := #ball;
    "Ball size:",nv;
  until nv eq ov;

  //close under W1
  for b in ball do
    for w in W1 do if &+[#w(x) : x in b] eq &+[#x : x in b] then
      Include(~ball, [w(x) : x in b] );
    end if; end for;
  end for;
  nv := #ball;
  "Final ball size:",nv;
  return ball;
end function;

intrinsic InverseAutomorphismFreeGroup(t :: GrpAutoElt) -> GrpAutoElt 
{inverse of automorphism t of free group}
  local F, H, r, invims, GA;
  F := Domain(t);
  require Type(F) eq GrpFP and #Relations(F) eq 0 :
                 "Domain of automorphism must be a free group";
  r := Ngens(F);
  H := sub< F | [t(F.i) : i in [1..r]] >;
  assert Index(F,H) eq 1; //t should be an automorphism
  invims := [ H!(F.i) : i in [1..r]];
  GA := AutomorphismGroup(F, [F.i:i in [1..r]], [[F!Eltseq(u) : u in invims]]);
  return GA.1;
end intrinsic; 

intrinsic InverseAutomorphismFreeGroup(F :: GrpFP, l :: SeqEnum) -> GrpAutoElt 
{inverse of automorphism of free group F defined by generator images l}
  local H, r, invims, GA;
  require #Relations(F) eq 0 :
                 "Domain of automorphism must be a free group";
  r := Ngens(F);
  assert #l eq r;
  H := sub< F | l >;
  ind := Index(F, H);
  assert ind eq 1; //t should be an automorphism
  invims := [ H!(F.i) : i in [1..r]];
  GA := AutomorphismGroup(F, [F.i:i in [1..r]], [[F!Eltseq(u) : u in invims]]);
  return GA.1;
end intrinsic; 

// Nielsen presentation for Aut (F_n, n>1)
Nielsen := function(n)

F<a,b,c,d> := FreeGroup(4);

// Relations for S_n:

A := quo< F | a^2, b^n, (b*a)^(n-1) >;

if n gt 4 then 
   for i in [2..(n div 2)] do
	A := quo< A | (a,b^(-i)*a*b^i)>;
   end for;
end if;

A := quo< A | c^2, (c,b*a), (c,b^(-1)*c*b) >;

if n ge 3 then
   A := quo< A |(c,b^(-1)*a*b)>;
end if;

// Rest of relations for the group:
A := quo< A | 
(d, c*d*c), //e
(d, a*b^(-1)*c*d*c*b*a), // f 
a*c*a*d*a*c*a*d, // i 
d^(-1)*a*d*a*c*d*c*a*c  //j 
>;

if n ge 3 then
A := quo< A | 
(d, b*a*b^(-1)*a*b), // b 
(d, b^(-2)*c*b^2), // c 
(d, a*b^(-1)*a*b*a*d*a*b^(-1)*a*b*a),  // g 
 a*b^(-1)*d*b*a*b^(-1)*d*b*d*b^(-1)*d^-1*b*d^-1   // h 
>;
end if;

if n ge 4 then
A := quo< A | (d,b^(-2)*d*b^2), // d
(d,b^(-2)*a*b^2) // a
>;
end if;

//Homomorphisms:

G := FreeGroup(n);

H1 := []; H2 := []; H3 := []; H4 := [];
for i :=  1 to n-1 do
H2[i] := G.(i+1);
end for;

H2[n] := G.1;
for i :=  2 to n do
H1[i] := G.i;
H3[i] := G.i;
H4[i] := G.i;
end for;

H1[1] := G.2;
H1[2] := G.1;
H3[1] := G.1^(-1);
H4[1] := G.1*G.2;

h1 := hom< G -> G | H1 >;
h2 := hom< G -> G | H2 >;
h3 := hom< G -> G | H3 >;
h4 := hom< G -> G | H4 >;

h := [];
h[1] := h1;
h[2] := h2;
h[3] := h3;
h[4] := h4;

// Output:

return A, h;
end function;

// Neumann presentation for Aut(F_n)

Neumann := function(n)

if n eq 1 then
F<x> := FreeGroup(1);
A := Group< a | a^2 >;
h1 := hom< F -> F | [x^(-1)] >;

elif n eq 2 then
F<x,y> := FreeGroup(2);
A := Group< a,b,c | a^2, b^2, (b*a)^4, (c,b*c*b), 
                    (a*b*a*c)^2, (c*a*b)^3 >;
h1 := hom< F -> F | [y,x] >;
h2 := hom< F -> F | [x^(-1),y] >;
h3 := hom< F -> F | [x*y,y] >;

elif n eq 3 then
A := Group< s,t,u | 
(s^5*t^(-1))^2, 
t^(-1)*s*t^2*s^8*t^(-1)*s*t^2*s^(-4), 
(s^4*t^(-1)*s*t^(-1))^2, 
t^4, 
(u,s^2*t^(-1)*s*t^(-1)*s^2), 
(u,s^(-2)*t^(-1)*s*t^(-1)*u*s^(-2)*t^(-1)*s*t^(-1)), 
// Neumann relations 19g corrected 
// (u,  s^2*t^(-1)*s*t*s*t^(-1)*u*t*s^(-1)*t^(-1)*s^(-1)*t*s^2), 
   (u, s^-2*t^(-1)*s*t*s*t^(-1)*u*t*s^(-1)*t^(-1)*s^(-1)*t*s^2), 
(u,t^(-1)*s*t^2*u*t^(-1)*s*t^2), 
s^(-2)*t^(-1)*s*t^2*s^2*u*s^2*t^(-1)*s*t^2*s^2*u*s^(-2)*u*s^2*u^(-1)
*s^(-2)*u^(-1), 
(s^(-2)*t^(-1)*s*t*u)^2, 
(u*t)^3 >;
F<x,y,z> := FreeGroup(3);
h1 := hom< F -> F | [y^(-1),z^(-1),x^(-1)] >;
h2 := hom< F -> F | [y,x^(-1),z] >;
h3 := hom< F -> F | [x*y,y,z] >;

elif IsEven(n) then
// Neumann for even n greater than 3:

F<q,r> := FreeGroup(2);

A := quo< F | (r^3*(q*r^3)^(n-1))^2, (q*r^3)^(2*(n-1)), q^n >;
for i in [2..(n/2)] do
	A := quo< A | (r^3*(q*r^3)^(n-1),q^(-i)*r^3*(q*r^3)^(n-1)*q^i)>;
end for;

A := quo< A | q^n, ((q*r^3)^(n-1),q^(-1)*r^3*(q*r^3)^(n-1)*q), 
		(q^(-2)*r^4*q^2*r^(-3),q*r^(-3)*q^(-1)*r^(-3)*q), 
		(r^4,(q*r^3)^(n-1)), (r^4,q^(-2)*r^4*q^2), 
		(q^(-2)*r^4*q^2*r^(-3),
(q*r^3)^(n-1)*q^(-2)*r^4*q^2*r^(-3)*(q*r^3)^(n-1)),
		(q^(-2)*r^4*q^2*r^(-3),
r^(-3)*q^(-1)*q^(-2)*r^4*q^2*r^(-3)*q*r^3), 
		(q^(-2)*r^4*q^2*r^(-3),
r^(-3)*q^(-1)*r^(-3)*(q*r^3)^n*q^(-2)*r^4*q^2*r^(-3)*(q*r^3)^(-n)*r^3*q*r^3), 
		(q*r^3)^(-n)*q^(-2)*r^4*q^2*r^(-3)*(q*r^3)^n*
q^(-3)*r^4*q^2*r^(-3)*q^(-1)*r^4*q^2*r^(-3)*q^(-1)*
r^3*q^(-2)*r^(-4)*q^3*r^3*q^(-2)*r^(-4)*q^2, 
		(r^3*(q*r^3)^(n-1)*q^(-2)*r^4*q^2)^2, r^12 >;

G := FreeGroup(n);
H1 := []; H2 := []; H3 := [];
for i :=  1 to n-1 do
	H1[i] := G.(i+1);
	H3[i] := G.i;
end for;
H1[n] := G.1;
H3[n] := G.n;

if n gt 4 then
	for i :=  3 to n-2 do
		H2[i] := G.i;
	end for;
end if;
H2[1] := G.2^(-1);
H2[2] := G.1;
H2[n-1] := G.n*G.(n-1)^(-1);
H2[n] := G.(n-1)^(-1);

h1 := hom< G -> G | H1 >;
h2 := hom< G -> G | H2 >;
h3 := hom< G -> G | H3 >;

else
// Neumann for odd n greater than 3:

F<r,s> := FreeGroup(2);
A := quo< F | (r^3*s^n*(s*r^(-3))^(n-1))^2, 
       (s^(n+1)*r^3*s^n*(s*r^(-3))^(n-1))^(n-1)*s^(-n*(n-1))>;

for i in [2..((n-1)/2)] do
   A := quo< A | (r^3*s^n*(s*r^(-3))^(n-1),
            s^(-i*(n+1))*r^3*s^n*(s*r^(-3))^(n-1)*s^(i*(n+1))) >;
end for;
		
A := quo< A | (s^n*(s*r^(-3))^(n-1))^2, 
(s^n*(s*r^(-3))^(n-1),s^(-(n+1))*r^3*s^n*(s*r^(-3))^(n-1)*s^(n+1)), 
		(s^(-2)*r^4*s^2*r^(-3),s*r^(-3)*s^(n-1)*r^(-3)*s), 
		(r^4,s^n*(s*r^(-3))^(n-1)), 
		(r^4,s^(-2)*r^4*s^2), 
(s^(-2)*r^4*s^2*r^(-3),
s^n*(s*r^(-3))^(n-1)*s^(-2)*r^4*s^2*r^(-3)*s^n*(s*r^(-3))^(n-1)),
(s^(-2)*r^4*s^2*r^(-3),
r^(-3)*s^(-(n+1))*s^(-2)*r^4*s^2*r^(-3)*s^(n+1)*r^3), 
(s^(-2)*r^4*s^2*r^(-3),
r^(-3)*s^(-1)*r^(-3)*s*r^3*s^n*(s*r^(-3))^(n-1)*
s^(-2)*r^4*s^2*r^3*(s*r^(-3))^(n-1)*s^n*r^(-3)*s^(-1)*r^3*s*r^3), 
r^3*(s*r^(-3))^(n-1)*s^(-3)*r^4*s^2*r^(-3)*
s*r^3*(s*r^(-3))^(n-1)*s^(n-3)*
r^4*s^2*r^(-3)*s^(n-1)*r^4*s^2*r^(-3)*
s^(n-1)*r^3*s^(-2)*r^(-4)*s^(n+3)*r^3*s^(-2)*r^(-4)*s^2, 
(r^3*(s*r^(-3))^(n-1)*s^(n-2)*r^4*s^2)^2 >;

G := FreeGroup(n);
H1 := []; H2 := []; H3 := [];
for i :=  1 to n-1 do
	H2[i] := G.(i+1)^(-1);
	H3[i] := G.i;
end for;
H2[n] := G.1^(-1);
H3[n] := G.n;

for i :=  3 to n-2 do
	H1[i] := G.i;
end for;
H1[1] := G.2^(-1);
H1[2] := G.1;
H1[n-1] := G.n*G.(n-1)^(-1);
H1[n] := G.(n-1)^(-1);

h1 := hom< G -> G | H1 >;
h2 := hom< G -> G | H2 >;
h3 := hom< G -> G | H3 >;

end if;
if n eq 1 then
return A, [h1];
elif n ge 4 then 
return A, [h1, h2];
else 
return A, [h1, h2, h3];
end if;
end function;

// Magnus - K - S relation to add to Nielsen presentation
// for Aut(F_n) to produce GL(n, Z)
// return (U * O)^2 eq Identity (I);
