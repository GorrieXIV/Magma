freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//                         CLASS NUMBERS                          //
//                    OF BINARY QUADRATIC FORMS                   //
//                          David Kohel                           //
//                    Last modified April 2000                    //
//                                                                //
////////////////////////////////////////////////////////////////////
//
// March 2014, SRD
// Changed the output of ReducedForms and ReducedOrbits in the case
// where narrow class group differs from non-narrow: previously,
// half the forms were not equivalent to any of the ReducedForms
// and half the reduced forms were not in any of the ReducedOrbits.

// Intrinsics: ReducedForms, ReducedOrbits (positive discriminants) 

import "class_number.m" : FundDiscCond;

forward ReducedFormsCond, KernelForms, PullbackForm; 
forward P1Class, P1Orbits; 

intrinsic ReducedForms(D::RngIntElt) -> SeqEnum 
   {Sequence containing one reduced form in each equivalence class of 
   BinaryQuadraticForms(D).}
   require D mod 4 in {0,1} : "Argument is not a discriminant";
   DK, m := FundDiscCond(D);
   if D lt 0 and m eq 1 then
      return RF(D);
   end if;
   return ReducedFormsCond(DK,m,true);
end intrinsic;

intrinsic ReducedForms(Q::QuadBin) -> SeqEnum 
   {Sequence containing one reduced form in each equivalence class of Q.}
   D := Discriminant(Q);
   DK, m := FundDiscCond(D);
   if D lt 0 and m eq 1 then
      return RF(D);
   end if;
   return ReducedFormsCond(DK,m,true);
end intrinsic;

intrinsic ReducedOrbits(Q::QuadBin) -> SeqEnum
   {The ReductionOrbit of each of the ReducedForms(Q).
   For positive discriminants only.}
   DK, m := FundDiscCond(Discriminant(Q));
   require DK gt 0 : "Discriminant must be positive";
   G := ReducedFormsCond(DK,m,true);
   return [ ReductionOrbit(g) : g in G ];
end intrinsic;

function ReducedFormsCond(DK,m, narrow)
   // The sequence of reduced binary quadratic forms of 
   // fundamental discriminant DK and conductor m. 
   if m eq 1 then
      if DK lt 0 then
         return RF(DK);
      else 
         G, f := FundamentalClassGroup(QuadraticForms(DK));  
         R := [ f(g) : g in G ]; 
      end if; 
   else
      K := KernelForms(DK,m); 
      if DK lt 0 then
         H := [ PullbackForm(q,m) : q in RF(DK) ]; 
      else
         A, f := FundamentalClassGroup(QuadraticForms(DK));
         H := [ PullbackForm(f(x),m) : x in A ]; 
      end if;
      R := [ k * h : k in K, h in H ];  
   end if;
   if narrow and DK gt 0 then
      Q := Universe(R);
      f1 := Q!1;
      f2 := Q![-e[1],e[2],-e[3]] where e is Eltseq(f1);
      if not IsEquivalent(f1, f2) then
         R := R cat [Q| [-e[1],e[2],-e[3]] where e is Eltseq(f) : f in R];
      end if;
   end if;
   return R;
end function;

function KernelForms(DK,m) 
   // The reduced binary quadratic forms in the kernel of the 
   // map to the form class group of fundamental discriminant.
   if m eq 1 then 
      return QuadraticForms(DK)!1;
   end if;
   Q := QuadraticForms(m^2*DK);
   t := DK mod 4;
   n := (t - DK) div 4;;
   if DK lt 0 then 
      S := { [ Integers() | x[1], x[2] ] : x in P1Classes(m) |
               IsUnit(x[1]^2 + t*x[1]*x[2] + n*x[2]^2) };
   else 
      R := MaximalOrder(QuadraticField(DK));
      w := Basis(R)[2];
      u := FundamentalUnit(R);
      M := MatrixAlgebra(Integers(),2)!
             &cat[Eltseq(u*x) : x in Basis(R)];
      S := { [ Integers() | x[1], x[2] ] : x in P1Orbits(M,m) |
               IsUnit(x[1]^2 + t*x[1]*x[2] + n*x[2]^2) };
   end if;
   // For discriminants D = -3 and D = -4, the units give 
   // elements to multiplicity 3 or 2, so construct kernel 
   // forms first as a set.
   K := { Q | };
   for P in S do
      X := EchelonForm( RMatrixSpace(Integers(),3,2) ! 
         &cat[ P, [ m, 0 ], [ 0, m ] ] );  
      Include(~K, Reduction( Q ! [
             X[1,1]^2 + t*X[1,1]*X[1,2] + n*X[1,2]^2,
             t*X[1,1]*X[2,2] + 2*n*X[1,2]*X[2,2], n*X[2,2]^2 ] ) );  
   end for;
   K := Sort([ f : f in K ]);
   return K;
end function;

function PullbackForm(f,m)
   a, b, c := Explode(Eltseq(f));
   if GCD(a,m) eq 1 then
      Q2 := QuadraticForms(m^2*(b^2-4*a*c));
      r,_:=Reduction(Q2![a,m*b,m^2*c]); return r;
   elif GCD(c,m) eq 1 then
      Q2 := QuadraticForms(m^2*(b^2-4*a*c));
      r,_:=Reduction(Q2![c,-m*b,m^2*a]); return r;
   end if;
   m1 := m;
   t1 := GCD(a,m);
   while t1 ne 1 do 
      m1 div:= t1;
      t1 := GCD(a,m1);
   end while;
   m2 := m div m1;
   if m1 ne 1 then
      Q2 := QuadraticForms(m1^2*(b^2-4*a*c));
      return PullbackForm(Reduction(Q2![a,m1*b,m1^2*c]),m2);
   end if;
   m1 := m;
   t1 := GCD(c,m);
   while t1 ne 1 do 
      m1 div:= t1;
      t1 := GCD(c,m1);
   end while;
   m2 := m div m1;
   if m1 ne 1 then
      Q2 := QuadraticForms(m1^2*(b^2-4*a*c));
      return PullbackForm(Reduction(Q2![c,-m1*b,m1^2*a]),m2);
   end if;
   Q2 := QuadraticForms(b^2-4*a*c);
   return PullbackForm(Q2![a+b+c,b+2*c,c],m);
end function;

function P1Orbits(M,m)
   // M is an integral matrix, and m the modulus
   R := ResidueClassRing(m);
   M := MatrixAlgebra(R,2)!M;
   X := { x : x in P1Classes(m) };
   C := [ Universe(X) | ];
   while #X ne 0 do
      x := Random(X);
      Exclude(~X,x);
      Append(~C,x);
      y := P1Class(x*M);
      while y ne x do
         Exclude(~X,y);
         y := P1Class(y*M);
      end while;
   end while;
   return C;
end function;

function P1Class(x)
   V := Parent(x);
   m := Modulus(BaseRing(V));
   x1 := Integers()!x[1];
   x2 := Integers()!x[2];
   y1, y2 := P1Normalize(x1,x2,m); 
   return V![y1,y2];
end function;

