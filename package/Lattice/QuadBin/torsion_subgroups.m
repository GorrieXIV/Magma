////////////////////////////////////////////////////////////////////
//                                                                //
//                       TORSION SUBGROUPS                        //
//                   OF BINARY QUADRATIC FORMS                    //
//                         David Kohel                            //
//                    Last modified April 2000                    //
//                                                                //
////////////////////////////////////////////////////////////////////

freeze;

// Intrinsics:
// pSubgroup, TwoTorsionSubgroup, AmbiguousForms, Random

intrinsic pSubgroup(Q::QuadBin,p::RngIntElt) -> GrpAb, Map
   {The Sylow p-subgroup of reduced forms.}

   G, m := ClassGroup(Q);
   H := SylowSubgroup(G,p);
   pgens := [ m(H.i) : i in [1..Ngens(H)] ];
   Gp := AbelianGroup([ Order(H.i) : i in [1..Ngens(H)] ]);
   mp := map< Gp -> Q | g :-> &*[ pgens[i]^c[i] 
      where c is Eltseq(g) : i in [1..Ngens(G)] ] >;
   return Gp, mp;
end intrinsic;

intrinsic AmbiguousForms(Q::QuadBin) -> SeqEnum
   {The sequence of reduced 2-torsion forms of negative 
   discriminant D.} 

   D := Discriminant(Q);
   require (D lt 0) : "Argument 1 must be negative.";
   require (D mod 4) in {0,1} : 
      "Argument 1 not congruent to 0 or 1 mod 4."; 
   G, f := TwoTorsionSubgroup(Q);
   return [ f(g) : g in G ];
end intrinsic;

intrinsic TwoTorsionSubgroup(Q::QuadBin) -> GrpAb, Map
   {The subgroup of form classes of order 2.}

   D := Discriminant(Q);
   require D lt 0 : "Argument 1 must be negative.";
   m := Conductor(Q);
   DK := D div m^2;
   prms := Factorization(D);
   S := [ Q | ];
   r1 := 0;
   r2 := 0;
   for p in prms do
      if IsEven(p[1]) then
         e := p[2];  
         case e :
            when 2 : 
               if DK mod 4 eq 0 then
     	          n := (4-D) div 8;
                  Append(~S,Q![2,2,n]);
  	          r2 +:= 1;
               end if;
            when 3 :
  	       n := -D div 8;
               Append(~S,Q![2,0,-D div 8]);
	       r2 +:= 1;
            when 4 :
  	       n := -D div 2^e;
               Append(~S,Q![2^(e-2),0,n]);
	       r2 +:= 1;
            else 
  	       n := -D div 2^e;
               Append(~S,Q![2^(e-2),0,n]);
  	       n := (2^(2*e-4)-D) div 2^e;
               Append(~S,Q![2^(e-2),2^(e-2),n]);
               r2 +:= 2;
         end case 
      else 
         r1 +:= 1;
         q := p[1]^p[2];
         if D mod 4 eq 1 then
            n := (q+(-D div q)) div 4;
            Append(~S,Q![q,q,n]);
         else    
            n := -D div (4*q);
            Append(~S,Q![q,0,n]);
         end if;
      end if;
   end for;
   S := [ Reduction(S[i]) : i in [1..r1+r2-1] ]; 
   G := AbelianGroup([ 2 : i in [1..#S] ]); 
   f := map< G -> Q | g :-> &*[ Q | S[i]^c[i] 
            where c is Eltseq(g) : i in [1..#S] ] >;
   return G, f;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    ELEMENT GROUP OPERATIONS                    //
//                                                                //
////////////////////////////////////////////////////////////////////

/*
// in kernel (as IsEquavalent)

intrinsic Equivalence(f::QuadBinElt,g::QuadBinElt) -> AlgMat
   {A matrix defining the equivalence between two forms.}
   require Discriminant(f) lt 0: "Discriminant of arguments must be negative.";
   require Parent(f) eq Parent(g) : "Arguments have different parents";
   require IsEquivalent(f,g) : "Arguments must be equivalent";
   B1 := Basis(LLL(Lattice(f)));
   B2 := Basis(LLL(Lattice(g)));
   MatZ := MatrixAlgebra(Integers(),2);
   M1 := MatZ! &cat[ Eltseq(x) : x in B1 ];
   M2 := MatZ! &cat[ Eltseq(x) : x in B2 ];
   // Make into a proper equivalence: 
   if Determinant(M1) eq -1 then
      M1[2] *:= -1;
   end if;
   if Determinant(M2) eq -1 then
      M2[2] *:= -1;
   end if;
   // Right action on forms is by transpose:
   M1 := Transpose(M1);
   M2 := Transpose(M2);
   // Adjust to a unique reduced representative in 
   // ambiguous classes:
   r1 := f*M1;
   if not IsReduced(r1) then
      if r1[1] eq -r1[2] then
         M1 := M1*(MatrixAlgebra(Integers(),2)![1,1,0,1]);
      elif r1[1] eq r1[3] then
         M1 := M1*(MatrixAlgebra(Integers(),2)![0,-1,1,0]);
      end if;
   end if;
   r2 := g*M2;
   if not IsReduced(r2) then
      if r2[2] eq -r2[1] then
         M2 := M2*(MatrixAlgebra(Integers(),2)![1,1,0,1]);
      elif r2[1] eq r2[3] then
         M2 := M2*(MatrixAlgebra(Integers(),2)![0,-1,1,0]);
      end if;
   end if;
   // assert f*M1*M2^-1 eq g;
   return M1*M2^-1;
end intrinsic;
*/

intrinsic IsOrder(f::QuadBinElt, n::RngIntElt) -> BoolElt
   {Returns true iff n is the order of the form class f.}
   fac := Factorization(n);
   id := Parent(f)!1;
   if not IsEquivalent(n*f,id) then return false; end if;
   for p in fac do
      if IsEquivalent((n div p[1])*f,id) then
         return false;
      end if;
   end for;
   return true;
end intrinsic;

intrinsic Random(Q::QuadBin : Lambda := 2) -> QuadBinElt
   {A pseudo-random reduced form in Q; increasing the 
   parameter Lambda achieves a better approximation to 
   randomness.}

   // The failure of randomness is due to the failure of 
   // forms representing small numbers to represent primes 
   // in a moderate range. 

   Lambda := Max(Lambda,1/2);
   D := Discriminant(Q);
   B := Max(Ceiling(Lambda*Log(Abs(D))/Log(2)),10);
   repeat
      p := RandomPrime(B : Proof := false);
      if KroneckerSymbol(D,p) eq 1 then
         r := Reduction(PrimeForm(Q,p)); 
         return r;
      end if;
   until false;
end intrinsic;

