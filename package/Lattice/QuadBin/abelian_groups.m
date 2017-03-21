freeze;

////////////////////////////////////////////////////////////////////
//                                                                //  
//                     Abelian Group Structure                    // 
//                           David Kohel                          // 
//                            May 2000                            //
//                                                                //  
////////////////////////////////////////////////////////////////////
//
// March 2014, SRD
// Now works for positive discriminant:
// was wrong due to using wrong equality test!
// (Yes I know, this file was intended for generic use, 
// but in fact it is only used for quadratic forms.)

forward GeneratedSylowSubgroup, SylowSubgroup;
forward Is_pDependent, pEchelonization;

// Canonical representative in the class of f 
// in ClassGroup(Parent(f))

function rep(f)
   D := Discriminant(f);
   if D lt 0 then
      return f;
   else
      g := Parent(f) ! [-e[1],e[2],-e[3]] where e is Eltseq(f);
      return Min(ReductionOrbit(f) join ReductionOrbit(g));
   end if;
end function;

////////////////////////////////////////////////////////////////////
//                     Full Group Analysis                        //
////////////////////////////////////////////////////////////////////

function GeneratedSubgroup(gens,n)
   Q := Universe(gens);
   ords := [ Order(x) : x in gens ];
   prms := PrimeDivisors(n);
   pGrps := [ ];
   pMaps := [PowerStructure(Map) | ];
   for p in prms do 
      q := p^Valuation(n,p);
      pords := [ p^Valuation(ords[i],p) : i in [1..#ords] ];
      pgens := [ gens[i]^(ords[i] div pords[i]) 
                  : i in [1..#gens] | pords[i] mod p eq 0 ]; 
      Gp, fp := GeneratedSylowSubgroup(pgens,p,q);
      Append(~pGrps,Gp);
      Append(~pMaps,fp);
   end for;
   E, incl_maps, proj_maps := DirectSum(pGrps);
   return E, hom< E -> Q | x :-> 
      &*[ Q | pMaps[i](proj_maps[i](x)) : i in [1..#pMaps] ] >;
end function;

////////////////////////////////////////////////////////////////////
//                        pGroup Analysis                         //
////////////////////////////////////////////////////////////////////

function GeneratedSylowSubgroup(gens,p,q)
   G := Universe(gens);
   egens := [ G | ];
   pgens := [ G | ];
   ords := [ Integers() | ];
   for x in gens do
      pEchelonization(x,p,q,~pgens,~egens,~ords);
   end for;
   A := AbelianGroup(ords);
   return A, hom< A -> G | x :-> 
      &*[ egens[i]^c[i] : i in [1..#egens] ] where c is Eltseq(x) >;
end function;

function SylowSubgroup(G,p)
   // G := QuadraticForms(D) and p is a prime
   n := ClassNumber(G);   
   if n mod p ne 0 then
      A := AbelianGroup([]);
      return A, hom< A -> G | x :-> Id(G) >;
   end if;
   q := p^Valuation(n,p);
   m := n div q;
   gens := [ G | ];
   pgens := [ G | ];
   ords := [ Integers() | ];
   while &*ords ne q do
      x := Random(G)^m;
      t := Order(x);
      if p lt 10 then
         for i in [1..3] do
   	    x1 := Random(G)^m;
            t1 := Order(x1);
            if t1 gt t then
      	       x := x1; 
               t := t1; 
            end if;
         end for;
      end if;
      if t ne 1 then
         pEchelonization(x,p,q,~pgens,~gens,~ords);
      end if;
   end while;
   A := AbelianGroup(ords);
   return A, hom< A -> G | x :-> 
         &*[ gens[i]^c[i] : i in [1..#gens] ] where c is Eltseq(x) >;
end function;

procedure pEchelonization(y,p,q,~pgens,~gens,~ords)
   y_ord := Order(y);
   yp := y^(y_ord div p);
   if #gens eq 0 then
      Append(~gens,y);
      Append(~pgens,yp);
      Append(~ords,y_ord);
      return;
   end if;
   while y_ord ne 1 do
      k := Min([ i : i in [1..#gens] | ords[i] ge y_ord ] cat [#ords+1]);
      pdeps := [ Universe(gens) | pgens[i] : i in [k..#gens] ];  
      val, v := Is_pDependent(yp,p,pdeps);
      if val then
         e := [ Integers()|a : a in Eltseq(v) ];  
         y *:= &*[ gens[i]^(-e[i+1-k]*(ords[i] div y_ord)) 
   	              : i in [k..#gens] ];
         y_ord := Order(y); 
         yp := y^(y_ord div p);
      else
         gens_init := [ gens[i] : i in [1..k-1] ];
         gens := [ y ] cat [ gens[i] : i in [k..#ords] ];
         pgens := [ yp ] cat [ pgens[i] : i in [k..#ords] ];
         ords := [ y_ord ] cat [ ords[i] : i in [k..#ords] ];
         for z in gens_init do
            if &*ords eq q then
               // printf "Breaking early at list element %o of %o\n",
	       //    Index(gens_init,z)-1, #gens_init;    
  	       break z; 
            end if;
	    pEchelonization(z,p,q,~pgens,~gens,~ords);
         end for;                           
      end if;
   end while;
end procedure;

function Is_pDependent(y,p,pgens)
   // For p = 2 the value of b equals p, therefore there 
   // is no savings in the BSGS partition.  Instead this 
   // should do a partition using the rank, but this is 
   // not implemented here.
   r := #pgens;
   V := VectorSpace(GF(p),r);
   if r eq 0 then
      return false, V!0;
   end if;
   G := Universe(pgens);
   exps := [ V | ];
   BabyS := {@ G | @};
   GiantS := {@ G | @};
   b := Ceiling(Sqrt(p));
   C := CartesianPower({0..b-1},r);
   for c in C do
      Append(~exps,V![ c[i] : i in [1..r] ]);
      x := &*[ pgens[i]^c[i] : i in [1..r] ];
      Include(~BabyS, rep(x));
      Include(~GiantS, rep(x^b));
   end for;   
   for x1 in GiantS do
      y1 := rep(x1*y);
      if y1 in BabyS then
         v := exps[Index(BabyS,y1)] - b*exps[Index(GiantS,x1)];
         return true, v;
      end if;
   end for;
   return false, V!0;
end function;

