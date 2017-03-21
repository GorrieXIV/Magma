freeze;

GeneralMP := function (p, r, s, t, n)
   m := s + n;
   F := FreeGroup (m);
   R := [F.i^p = F.(i + 1) : i in [1..n - 1]];
   S := [F.(n + i)^p = F.(n + i + 1) : i in [1..s - 1]];
   a := F.1; b := F.(n + 1);
   Q := quo <F | R, S, F.n^p, F.m^p = F.t^p, a^b = a * F.r^p>;
   H := pQuotient (Q, p, m: Print := 0);
   return H;
end function;

CaseA := function (p, r, s, t, n)
   m := s + n;
   F := FreeGroup (m);
   R := [F.i^2 = F.(i + 1) : i in [1..n - 1]];
   S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]];
   a := F.1; b := F.(n + 1);
   A := quo <F | R, S, F.n^2, F.m^2, a^b = a^-1>;
   // A := Group <a, b | a^(2^n) = 1, b^(2^s), a^b = a^-1>;
   H := pQuotient (A, p, m: Print := 0);
   return H;
end function;

CaseB := function (p, r, s, t, n)
   m := s + n;
   F := FreeGroup (m);
   R := [F.i^2 = F.(i + 1) : i in [1..n - 1]];
   S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]];
   a := F.1; b := F.(n + 1);
   B := quo <F | R, S, F.n^2, F.(n-1)^2 = F.(n+s)^2, a^b = a^-1>;
   // B := Group <a, b | a^(2^n), a^(2^(n-1)) = b^(2^s), a^b = a^-1>;
   H := pQuotient (B, p, m: Print := 0);
   return H;
end function;
 
CaseC := function (p, r, s, t, n)
   m := s + n;
   F := FreeGroup (m);
   R := [F.i^2 = F.(i + 1) : i in [1..n - 1]];
   S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]];
   a := F.1; b := F.(n + 1);
   C := quo <F | R, S, F.n^2, F.m^2, F.(n-1)^2 = (a^-1)^b * a^-1>;
   // C := Group <a, b | a^(2^n), b^(2^s), a^b = a^(-1 - 2^(n-1))>;
   H := pQuotient (C, p, m: Print := 0);
   return H;
end function;

CaseD := function (p, r, s, t, n)
   m := s + n;
   F := FreeGroup (m);
   R := [F.i^2 = F.(i + 1) : i in [1..n - 1]];
   S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]];
   a := F.1; b := F.(n + 1);
   D := quo <F | R, S, F.n^2, F.m^2, a^b = a^3>;
   // D := Group <a, b | a^(2^n), b^(2^s), a^b = a^3>;
   H := pQuotient (D, p, m: Print := 0);
   return H;
end function;

CaseE := function (p, r, s, t, n)
   m := s + n;
   F := FreeGroup (m);
   R := [F.i^2 = F.(i + 1) : i in [1..n - 1]];
   S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]];
   a := F.1; b := F.(n + 1);
   E := quo <F | R, S, F.n^2, F.m^2 = F.(n -1)^2, a^b = a^3>;
   // E := Group <a, b | a^(2^n), a^(2^(n-1)) = b^(2^s), a^b = a^3>;
   H := pQuotient (E, p, m: Print := 0);
   return H;
end function;

CaseF := function (p, r, s, t, n, k)
   m := s + n;
   F := FreeGroup (m);
   R := [F.i^2 = F.(i + 1) : i in [1..n - 1]];
   S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]];
   a := F.1; b := F.(n + 1);
   f := quo <F | R, S, F.n^2, F.m^2, F.(k)^2 = (a^-1)^b * a^-1>;
   // F := Group <a, b | a^(2^n), b^(2^s), a^b = a^(-1 -2^k)>;
   H := pQuotient (f, p, m: Print := 0);
   return H;
end function;

CaseG := function (p, r, s, t, n, k)
   m := s + n;
   F := FreeGroup (m);
   R := [F.i^2 = F.(i + 1) : i in [1..n - 1]];
   S := [F.(n + i)^2 = F.(n + i + 1) : i in [1..s - 1]];
   a := F.1; b := F.(n + 1);
   G := quo <F | R, S, F.n^2, F.m^2 = F.(n -1)^2,
                 F.(k)^2 = (a^-1)^b * a^-1>;
   // G := Group <a, b | a^(2^n), b^(2^s) = a^(2^(n - 1)), a^b = a^(-1 -2^k)>;
   H := pQuotient (G, p, m: Print := 0);
   return H;
end function;

/* D has nuclear rank 1, Z has a unique involution */

AnotherDistinguishMaxClass := function (G: NumberRandom := 100)
   if NuclearRank (G) eq 1 then return "Dihedral"; end if;
   n := NPCgens (G);
   flag := IsCentral (G, G.n); 
   if flag then Z := sub <G | G.n>; else Z := Centre (G); end if;
   nmr := 0;
   P := RandomProcess (G);
   repeat
      nmr +:= 1;
      x := ElementOfOrder (P, 2, 20: Word := false);
      if Type (x) cmpeq GrpPCElt and not (x in Z) then 
         return "Semidihedral"; 
      end if;
   until nmr gt NumberRandom;
   return "Quaternion"; 
end function;

/* distinguish among the three maximal class 2-groups:
   if the generators g, h are independent of the Frattini subgroup, then 
   the number of involutions among  g, h, (g * h) distinguishes among them */

DistinguishMaxClass := function (G: NumberRandom := 100)
   gens := [G.1, G.2];

   if sub <G | gens> ne G then 
      flag, gens := IsMetacyclicPGroup (G); 
      if not flag then error "This is not a maximal class 2-group"; end if;
   end if;

   O := [Order (gens[1]), Order (gens[2]), Order (gens[1] * gens[2])];
   n := #[x : x in O | x eq 2]; 
   case n:
      when 2: return "Dihedral"; 
      when 1: return "Semidihedral"; 
      when 0: return "Quaternion"; 
   end case;
   error "This is not a maximal class 2-group";
end function;
   
intrinsic InvariantsMetacyclicPGroup (P::Grp) -> SeqEnum
{Sequence of invariants which uniquely identify metacyclic p-group P}

   require Type (P) in [GrpMat, GrpPerm, GrpPC] :
       "Argument must be a pc-, matrix, or permutation group";

   if IsPrimePower (#P) eq false then return false; end if;

   // require IsPrimePower (#P): "Argument must be p-group";

   if Type (P) eq GrpMat or Type (P) eq GrpPerm then
      P := PCGroup (P);
   end if;

   flag, Gens := IsMetacyclicPGroup (P);
   if not flag then return false; end if;

   o := FactoredOrder (P);
   p := o[1][1]; m := o[1][2];

   if IsCyclic (P) then return <m, 0, 0, m, [#P], "">; end if;

   D := DerivedGroup (P);
   if #D eq 1 then 
      nmr := 0;
   else 
      d := FactoredOrder (D);
      nmr := d[1][2];
   end if;

   A := AbelianQuotientInvariants (P);
   E := [Ilog (p, x): x in A];
   if #E ne 2 then return false; end if;
   r := E[1]; s := E[2];
   n := nmr + r;
   
   e := Exponent (P);
   e := Ilog (p, e);
   t := -e + s + n;

   // assert n - r eq NPCgens (D);
   // assert p^(n + s - t) eq Exponent (P);
   // assert #quo < P | DerivedGroup (P)> eq p^(r + s);

   Z := Centre (P);
   z := NPCgens (Z); 
   if r eq 1 and p eq 2 then
     A := AbelianQuotientInvariants (Z);
     if s eq 1 and z eq 1 then 
        name := DistinguishMaxClass (P); 
        return <r, s, t, n, A, name>;
     elif s gt 1 and A eq [2, 2^(s - 1)] then 
        a := Gens[1];
        b := Gens[2];
        H := sub <P | b^2>;
        n1 := DistinguishMaxClass (quo < P | H>);
        // assert Order (H) eq 2^(s - 1);
/* 
        K := sub <P | b^2 * a^(2^(n - 1))>;
        n2 := DistinguishMaxClass (quo < P | K>);
*/
        // assert Order (K) eq 2^(s - 1);
        return <r, s, t, n, A, n1>;
     else 
        return <r, s, t, n, A, "">;
     end if;
   else 
      return <r, s, t, n, [], "">;
   end if;
end intrinsic;


intrinsic StandardMetacyclicPGroup (P:: Grp) -> GrpPC
{return standard pc-presentation for metacyclic p-group P}

   require Type (P) in [GrpMat, GrpPerm, GrpPC] :
       "Argument must be a pc-, matrix, or permutation group";

   if IsPrimePower (#P) eq false then return false; end if;
   // require IsPrimePower (#P): "Argument must be p-group";

   if Type (P) eq GrpMat or Type (P) eq GrpPerm then
      P := PCGroup (P);
   end if;

   parms := InvariantsMetacyclicPGroup (P);
   if parms cmpeq false then return false; end if;

   o := FactoredOrder (P);
   p := o[1][1]; m := o[1][2];

   r := parms[1]; s := parms[2]; t := parms[3]; n :=parms[4];
   A := parms[5]; n1 := parms[6]; 

   if s eq 0 then 
      H := pQuotient (P, p, m);
      return H;
   end if;

   if IsOdd (p) then 
      return GeneralMP (p, r, s, t, n);
   end if;

   if p eq 2 and r gt 1 then 
      return GeneralMP (p, r, s, t, n);
   end if;

   if s eq m - 1 then 
      F := FreeGroup (m);
      s := m - 1;
      R := [F.i^2 = F.(i + 1): i in [1..s - 1]];
      Q := quo <F | R, F.s^2, F.m^2, (F.1, F.m)>;
      H := pQuotient (Q, p, m: Print := 0);
      return H;
   end if;

   if s eq 1 then 
      if n1 eq "Dihedral" then return CaseA (p, r, s, t, n);
      elif n1 eq "Quaternion" then return CaseB (p, r, s, t, n);
      elif n1 eq "Semidihedral" then return CaseC (p, r, s, t, n);
      end if;
   end if;

   case A: 
     when [2, 2^(s - 1)]:  
        if n1 in ["Dihedral", "Quaternion"] then return CaseA (p, r, s, t, n);
        elif n1 in ["Semidihedral"] then return CaseC (p, r, s, t, n);
        end if;
     when [2^s]: 
        return CaseB (p, r, s, t, n);
     when [2, 2^(s - n + 2)]: 
        return CaseD (p, r, s, t, n);
     when [2^(s - n + 3)]: 
        return CaseE (p, r, s, t, n);
   end case;

   if #A eq 2 then 
      max := Maximum (A);
      u := Ilog (p, max);
      k := u - s + n;
      return CaseF (p, r, s, t, n, k);
   elif #A eq 1 then 
      u := Ilog (p, A[1]);
      k := u - s + n - 1;
      return CaseG (p, r, s, t, n, k);
   end if;

   error "Parameters for metacyclic p-group identification are wrong"; 
end intrinsic;

AreIsomorphic := function (G, H)
   pG := InvariantsMetacyclicPGroup (G);
   if pG cmpeq false then return false; end if;
   pH := InvariantsMetacyclicPGroup (H);
   if pH cmpeq false then return false; end if;
   return pG eq pH;
end function;
