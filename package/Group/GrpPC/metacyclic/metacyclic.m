freeze;

/* list and identify metacyclic p-groups;
   the group listing and identification functions follow 
   notes prepared by Michael Vaughan-Lee, October 2005;
   code prepared by Eamonn O'Brien April 2006 */

/* metacyclic p-groups of order p^m */

GeneralMetacyclicPGroups := function (p, m)

   if IsPrime (p) eq false then return false; end if;

   if p eq 2 then min := 2; else min := 1; end if;

   L := []; // I := [];
   for s in [min..m - 1] do
   for t in [min..s] do
   for r in [min..t] do
   for n in [t..t + r] do
      if s + n eq m then 
         F := FreeGroup (m);
         R := [F.i^p = F.(i + 1) : i in [1..n - 1]]; 
         S := [F.(n + i)^p = F.(n + i + 1) : i in [1..s - 1]]; 
         a := F.1; b := F.(n + 1);
         Q := quo <F | R, S, F.n^p, F.m^p = F.t^p, a^b = a * F.r^p>;
         // Q := Group <a, b | a^(p^n), b^(p^s) = a^(p^t), a^b = a^(1 + p^r)>;
         // Append (~I, <r, s, t, n>);
         Append (~L, Q);
      end if;
   end for;
   end for;
   end for;
   end for;

   return L;
end function;

/* metacyclic groups of order p^m where G/G' = C_2 x C_{2^s} */

SpecialMetacyclicCase := function (m)
   
   if m le 1 then return []; end if;

   F := FreeGroup (m);

   s := m - 1;
   R := [F.i^2 = F.(i + 1): i in [1..s - 1]];
   Q := quo <F | R, F.s^2, F.m^2, (F.1, F.m)>;
   
   L := [Q];

   for n in [2..m - 1] do 
      s := m - n;
      R := [F.i^2 = F.(i + 1) : i in [1..n - 1]]; 
      S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]]; 
      a := F.1; b := F.(n + 1);
      A := quo <F | R, S, F.n^2, F.m^2, a^b = a^-1>;
      // A := Group <a, b | a^(2^n) = 1, b^(2^s), a^b = a^-1>;
      Append (~L, A);
   end for;

   for n in [2..m - 1] do 
      s := m - n;
      R := [F.i^2 = F.(i + 1) : i in [1..n - 1]]; 
      S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]]; 
      a := F.1; b := F.(n + 1);
      B := quo <F | R, S, F.n^2, F.(n-1)^2 = F.(n+s)^2, a^b = a^-1>;
      // B := Group <a, b | a^(2^n), a^(2^(n-1)) = b^(2^s), a^b = a^-1>;
      Append (~L, B);
   end for;

   for n in [3..m - 1] do 
      s := m - n;
      R := [F.i^2 = F.(i + 1) : i in [1..n - 1]]; 
      S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]]; 
      a := F.1; b := F.(n + 1);
      C := quo <F | R, S, F.n^2, F.m^2, F.(n-1)^2 = (a^-1)^b * a^-1>;
      // C := Group <a, b | a^(2^n), b^(2^s), a^b = a^(-1 - 2^(n-1))>;
      Append (~L, C);
   end for;

   for n in [4..m - 1] do 
      s := m - n;
      if s ge n - 2 then 
         R := [F.i^2 = F.(i + 1) : i in [1..n - 1]]; 
         S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]]; 
         a := F.1; b := F.(n + 1);
         D := quo <F | R, S, F.n^2, F.m^2, a^b = a^3>;
         // D := Group <a, b | a^(2^n), b^(2^s), a^b = a^3>;
         Append (~L, D);
      end if;
   end for;

   for n in [4..m - 1] do 
      s := m - n;
      if s ge n - 1 then 
         R := [F.i^2 = F.(i + 1) : i in [1..n - 1]]; 
         S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]]; 
         a := F.1; b := F.(n + 1);
         E := quo <F | R, S, F.n^2, F.m^2 = F.(n -1)^2, a^b = a^3>;
         // E := Group <a, b | a^(2^n), a^(2^(n-1)) = b^(2^s), a^b = a^3>;
         Append (~L, E);
      end if;
   end for;

   for n in [5..m - 1] do 
      for k in [3..n - 2] do 
         s := m - n;
         if s ge n - k then 
            R := [F.i^2 = F.(i + 1) : i in [1..n - 1]]; 
            S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]]; 
            a := F.1; b := F.(n + 1);
            f := quo <F | R, S, F.n^2, F.m^2, F.(k)^2 = (a^-1)^b * a^-1>;
            // F := Group <a, b | a^(2^n), b^(2^s), a^b = a^(-1 -2^k)>;
            Append (~L, f);
         end if;
      end for;
   end for;

   for n in [5..m - 1] do 
      for k in [3..n - 2] do 
         s := m - n;
         if s ge n - k + 1 then 
            R := [F.i^2 = F.(i + 1) : i in [1..n - 1]]; 
            S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]]; 
            a := F.1; b := F.(n + 1);
            G := quo <F | R, S, F.n^2, F.m^2 = F.(n -1)^2, 
                          F.(k)^2 = (a^-1)^b * a^-1>;
            // G := Group <a, b | a^(2^n), b^(2^s) = a^(2^(n - 1)), a^b = a^(-1 -2^k)>;
            Append (~L, G);
         end if;
      end for;
   end for;

   return L;

end function;

/* metacylic groups of order 2^m */

EvenMetacyclicPGroups :=  function (m)
   X := GeneralMetacyclicPGroups (2, m);
   Y := SpecialMetacyclicCase (m); 
   return X cat Y; 
end function;

/* list metacyclic groups of order p^m */

intrinsic MetacyclicPGroups (p :: RngIntElt, m :: RngIntElt : 
                             PCGroups := true) -> []
{list of metacyclic groups of order p^m; if PCGroups is true, then 
 return groups in category GrpPC, otherwise GrpFP} 

   require IsPrime(p): "Argument 1 is not prime";
   requirege m, 1;

   if p eq 2 then 
      L := EvenMetacyclicPGroups (m);
   else 
      L := GeneralMetacyclicPGroups (p, m);
   end if;

   /* add cyclic group */
   F := FreeGroup (1);
   H := pQuotient (F, p, m: Print := 0);

   if PCGroups eq true then 
      P := [H] cat [pQuotient (q, p, m - 1: Print := 0): q in L];
   else 
      P := [FPGroup (H)] cat L;
   end if;

   return P;

end intrinsic;

intrinsic IsMetacyclicPGroup (P :: Grp) -> BoolElt
{P is a p-group, either pc- or matrix or permutation group; 
 if P is metacyclic, then return true, else false} 

   require Type (P) in [GrpMat, GrpPerm, GrpPC] :
       "Argument must be a pc-, matrix, or permutation group"; 

   if IsPrimePower (#P) eq false then return false; end if;
   // "Argument must be p-group"; 

   if Ngens (P) eq 1 then return true, [P.1]; end if;

   if Type (P) eq GrpMat or Type (P) eq GrpPerm then 
      P := PCGroup (P);
   end if;

   if IsCyclic (P) then return true, [P.1]; end if;
   
   A, f := AbelianQuotient (P);
   if #Generators (A) gt 2 then return false, _; end if;
   
   // if IsAbelian (P) then return true, [P.1, P.2]; end if;
   
   D := DerivedGroup (P);
   if not IsCyclic (D) then return false, _; end if;
   if Order (A) eq 4 then return true, [P.1, P.2]; end if;
   
   /* we now know that A is 2-generator */
   
   assert #Generators (A) eq 2;
   
   /* find "good" generating set for P / P' */
   trial := 0; found := false;
   repeat 
     X := Random (A); Y := Random (A);
     x := Order (X); y := Order (Y);
     if x gt y then temp := X; X := Y; Y := temp; end if;
     H := sub< A | X, Y >;
     if #H eq #A then 
        a := X @@ f;
        b := Y @@ f;
        if (Order (X) eq 2 or (Order (X) gt 2 and (Order (a) le Order (b)))) then 
           found := true;
        end if;
     end if;
     trial +:= 1;
   until found eq true;
   // "Number of trials is ", trial;
          
   s1 := Eltseq (X);
   s2 := Eltseq (Y);
   
   m := Order (A.1);
   n := Order (A.2);
   MA := MatrixAlgebra (Integers (n), 2);
   M := MA![s1[1], s1[2], s2[1], s2[2]];
   N := M^-1;
   Z := Integers();
   x := Z!N[1][1]; y := Z!N[1][2]; z := Z!N[2][1]; t := Z!N[2][2];
   a1 := a^x*b^y; b1 := a^z*b^t;
   // "Orders of the 2 canonical generators are ", Order (a1), Order (b1);

   if Order (a1) eq m*(#D) or Order(b1) eq n*(#D) then
      return true, [a1, b1];
   else
      // "failed order test";
      return false, _;
   end if;
end intrinsic;

/* are all finite p-quotients of G metacyclic? */

ArePQuotientsMetacyclic := function (G) 
   // require Type (P) in [GrpFp]: "Argument must be a fp-group";
   A := AbelianQuotientInvariants (G);
   if 0 in A or #A eq 0 then return false; end if;
   B := [PrimeBasis (x): x in A];
   P := Set (&cat (B));
   for p in P do 
      n := #[x : x in B | p in x]; 
      if n gt 2 then 
         return false;
      elif n eq 2 then
         H := pQuotient (G, p, 2);  
         if #H gt p^4 then return false; end if;
         id := IdentifyGroup (H);
         if not (id in [<p^3, 2>, <p^3, 4>, <8, 3>, <p^4, 2>, <p^4, 4>]) then 
            return false;
         end if;
      end if;
   end for;
   return true;
end function;
