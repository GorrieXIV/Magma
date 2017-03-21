freeze;

import "functions.m": SetExtraSpecialFlag, SetExtraSpecialGroup, 
                      SetExtraSpecialNormaliser, 
                      SetExtraSpecialParameters, 
                      ExtraSpecialFlag, SetExtraSpecialGenerators, 
                      SetExtraSpecialBasis, ExtraSpecialGenerators; 

import "normaliser.m": RecogniseNormaliserExtraSpecial, EpimorphicImage; 

forward Stripped;
 
/* matrices generate a finite matrix group G over a field of 
   characteristic p.
   S is a set of invertible matrices in G, assumed to act absolutely 
   irreducibly on the underlying vector space of G.
   If (mod scalars) <S> is an extraspecial r group  E of order 
   r^(2k+1), for some prime r, or a 2-group of symplectic type 
   (that is, the central product of an extraspecial 2-group with 
   a cyclic group of order 4) of order 2^(2k+2), normalised by G, 
   then the function stores r, k, normal-matrices, action-matrices, 
   where r, k are as above, normal-matrices are generators of 
   <S> ordered as x[1], .., x[k], y[1], .., y[k], (z) (see below), 
   and action-matrices is a sequence of matrices in 
   GL (2k, r), giving the action of matrices on the quotient 
   space of E.  Otherwise it returns false.
  
   It attempts to prove that S is extra-special or of symplectic 
   type by construction. That is, it tries to find elements 
   x[1], y[1], x[2], y[2], ..., x[k], y[k], z which generate
   S (mod scalars) so that the x[i]'s and y[i]'s 
   are non-central in <S>, z is central and scalar of order r, 
   x[i] and x[j] commute for all i, j, 
   y[i] and y[j] commute for all i, j, 
   x[i] and y[j] commute for distinct i, j, 
   but the commutator of x[i] and y[i] is equal to z for all i.
   Such generators  are found by adjusting the set S. 
   x[1] and y[1] can be chosen as any two non-commuting 
   non-scalar elements of S (if there are none then S cannot 
   be extraspecial/of symplectic type), 
   and z is set equal to their commutator.
   Each other generator x[i] or y[i] is equal to a different 
   non-scalar element of S multiplied by a word in those 
   x[j]'s and y[j]'s already selected, or a power of such. 
   More specifically, the function Stripped, applied to a 
   generator in S, multiplies it by a word in 
   x[1], ..x[i-1], y[1], ..y[i-1] until the product commutes 
   with all of those generators. We find x[i] and y[i], 
   if possible, by finding two such elements, both non-scalar, 
   and non-commuting. x[i] is the first, and y[i] is a 
   non-scalar power of the second such that [x[i], y[i]] = z.
   If the construction fails at any stage, the function
   returns false. Otherwise, the construction stops when 
   S is exhausted.  Finally conjugates of each x[i] and y[i] 
   by generators of G are computed, and checked for membership 
   of <S> using the function Stripped.  If some conjugate is 
   not in S false is returned, otherwise the function
   returns true.  */
 
ExtraSpecialDecomposition := function (M, S) 
 
   vprintf Smash: "\nTesting to see if the group normalises an extraspecial group\n";

   if #S eq 0 then return false; end if;

   d, F := BasicParameters (M);
 
   fac := Factorisation (d);
   if #fac ne 1 then
      vprintf Smash: "Dimension %o is not a prime power\n", d;
      return false;
   end if;
   r := fac[1][1];
   m := fac[1][2];

   matrices := GroupGenerators (M);
   gl := GL (d, F);
 
   ngensG := #matrices;
   ngensS := #S;
   x := [];
   y := [];
   doneGen := [];
 
   /* Each nonscalar element of S should have order r*t or r^2*t, 
      where r is prime to t. If not, we return false. 
      If so, we replace the element by its t-th power.
      We also replace elements of S to eliminate scalars.  */
 
   for j in [1..ngensS] do 
      h := S[j];
      if IsScalar (h) then
         S[j] := Identity (gl);
         doneGen[j] := true; 
      elif IsScalar (h^r) then 
         t := Order (h^r);
         if t mod r eq 0 then
            t div:= r;
         end if;
         if t mod r eq 0 then
            vprint Smash: "S contains elements of order", r^3;
            return false;
         end if;
         h := h^t;
         S[j] := h;
         if x eq [] then
            Append (~x, h);
            doneGen[j] := true; 
         else
            doneGen[j] := false; 
         end if;
      else
         vprintf Smash: "%o-th power of matrix is not scalar\n", r;
         return false;
      end if;
   end for;
 
   if x eq [] then
      vprint Smash: "Error - All matrices in S are scalar";
      return false;
   end if;
 
   j := 1;
   id := Identity (gl);
   while y eq [] and j le ngensS do
      if doneGen[j] eq false then
         z := (x[1], S[j]);
         if z ne id then
            if z^r ne id then 
               vprintf Smash: "%o-th power of commutator is not identity\n", r;
               return false;
            else 
               Append (~y, S[j]);
               doneGen[j] := true;
            end if;
         end if;
      end if;
      j +:= 1;
   end while;
 
   if y eq [] then
      vprintf Smash: "Error - Z(S) contains non-scalar, S cannot act \
absolutely irreducibly";
      return false;
   end if;
 
   for i in [2..m] do
      j := 1;
      while #x lt i and j le ngensS do
         if doneGen[j] eq false then
            flag, h := Stripped (S[j], x, y, z, r);
            if flag eq false then 
               vprint Smash: "Strip failed, group is not extraspecial";
               return false;
            elif IsScalar (h[1]) eq false then
               if IsScalar (h[1]^r) then
                  Append (~x, h[1]);
                  doneGen[j] := true;
               else 
                  vprintf Smash: "%o-th power of matrix in S is not scalar\n", r;
                  return false;
               end if;
            end if;
         end if;
         j +:= 1;
      end while;
 
      if #x lt i then
         vprint Smash: "ExtraSpecialDecomposition - Could not construct x[i]";
         return false;
      end if;
 
      j := 1;
      while #y lt i and j le ngensS do
         if doneGen[j] eq false then
            flag, h := Stripped (S[j], x, y, z, r);
            if flag eq false then 
               vprint Smash: "Strip failed, group is not extraspecial";
               return false;
            else
               comm := (x[i], h[1]);
               if comm ne id then 
                  u := 0;
                  while u lt r and comm ne z^u do
                     u +:= 1;
                  end while;
                  if u eq r then
                     vprint Smash: "Commutator is not a power of z";
                     return false;
                  end if;
                  if u ne 0 then 
                     h[1] := h[1]^InverseMod (u, r); 
                     if IsScalar (h[1]^r) then
                        Append (~y, h[1]);
                        doneGen[j] := true;
                     else 
                        vprintf Smash: "%o-th power of matrix is not scalar\n", r;
                        return false;
                     end if;
                  end if;
               end if;
            end if;
         end if;
         j +:= 1;
      end while;
 
      if #y lt i then
         vprint Smash: "ExtraSpecialDecomposition - Could not construct y[i]";
         return false;
      end if;
 
   end for; // from: for i in [2..m] do

   symp := false;
 
   for j in [1..ngensS] do
      if doneGen[j] eq false then
         flag, h := Stripped (S[j], x, y, z, r);
         if flag eq false then 
            vprint Smash: "Group is not extraspecial";
            return false;
         elif IsScalar (h[1]) eq false then
            vprint Smash: "Group is not extraspecial";
            return false;
         elif r eq 2 and Order (h[1]) eq 4 then
            symp := true;
         end if;
      end if;
   end for;
 
   /* Now we are ready to calculate the action of the generators 
      of G on <S>.  If G does not normalise <S> (mod scalars), 
      then we return false. Otherwise, we calculate matrices 
      in GL (2k, F) giving the actions of these 
      generators mod scalars. */
 
   k := #x;
   gl := GL (2*k, GF (r));
   action := [];
   for i in [1..#matrices] do
      g := matrices[i];
      seq := [];
      for j in [1..m] do
         flag, h := Stripped (x[j]^g, x, y, z, r);
         if flag eq false then 
            vprint Smash: "Strip failed, extraspecial group is not normalised";
            return false;
         elif IsScalar (h[1]) eq false then
            vprint Smash: "Extraspecial group is not normalised by G";
            return false;
         end if;
         t := Order (h[1]);
         if r eq 2 and t eq 4 then
            if symp eq false then
               symp := true;
               Append (~S, h[1]);
            end if;
         elif t ne r and t ne 1 then
            vprint Smash: "Extraspecial group is not normalised by G";
            return false;
         end if;
         seq cat:= h[2];
      end for;
 
      for j in [1..m] do
         flag, h := Stripped (y[j]^g, x, y, z, r);
         if flag eq false then 
            vprint Smash: "Strip failed, extraspecial group is not normalised";
            return false;
         elif IsScalar (h[1]) eq false then
            vprint Smash: "Extraspecial group is not normalised by G";
            return false;
         end if;
         t := Order (h[1]);
         if r eq 2 and t eq 4 then
            if symp eq false then
               symp := true;
               Append (~S, h[1]);
            end if;
         elif t ne r and t ne 1 then
            vprint Smash: "Extraspecialgroup is not normalised by G";
            return false;
         end if;
         seq cat:= h[2];
      end for;
      Append (~action, gl!seq);
   end for; // from: for i in [1..#matrices] do

   if symp then
      vprintf Smash: "Group normalises symplectic-type subgroup of order %o^%o\n", 
      r, 2 * #x + 2;
      SetExtraSpecialParameters (M, [r, 2 * #x + 2]);
   else
      vprintf Smash: "Group normalises extraspecial subgroup of order %o^%o\n", 
      r, 2 * #x + 1;
      SetExtraSpecialParameters (M, [r, 2 * #x + 1]);
   end if;
   
   SetExtraSpecialFlag (M, true);
   SetExtraSpecialGroup (M, sub <GL (d, F) | S>);
   SetExtraSpecialNormaliser (M, action);
   SetExtraSpecialGenerators (M, x cat y);

   return true;
 
end function;
 
/* r is a prime, h and z are invertible non-scalar matrices 
   and x, y lists of invertible matrices all in the same 
   general linear group.
   y has length t, and x length t or t+1.

   The function returns EITHER true and a tuple with two components:
   (i) a matrix hh equal to a product of h with a word in
       powers of x[1], y[1], ...x[t], y[t] (in that order), 
       and with the property that hh commutes with each of 
       x[1], y[1], ..., x[t], y[t].
   (ii) a sequence of length 2 * t, giving the negatives of 
       these powers
       (but in the order x[1], ..., x[t], y[1], ..., y[t]).
       This vector gives the value of the original element h  
       as a vector in terms of the x, y.  

   OR false, if (i) is not possible.  */
 
Stripped := function (h, x, y, z, r) 
 
   t := #y;
   hh := h;
   seq := [];
 
   for i in [1..t] do
     c1 := (x[i], hh);
     c2 := (y[i], hh);
     u := 0;
     while u lt r and c1 ne z^u do
        u +:= 1;
     end while;
     if u eq r then
       vprint Smash: "Commutator is not a power of z";
       return false, _;
     end if;
     v := 0;
     while v lt r and c2 ne z^v do
        v +:= 1;
     end while;
     if v eq r then
       vprint Smash: "Commutator is not a power of z";
       return false, _;
     end if;
   
     seq[i] := v eq 0 select 0 else r - v;
     seq[t + i] := u;
     if u eq 0 then
       hh *:= x[i]^v;
     else
       hh *:= x[i]^v * y[i]^(r-u);
     end if;
   end for;
 
   return true, <hh, seq>;
 
end function;
      
intrinsic IsExtraSpecialNormaliser (G::GrpMat) -> BoolElt
{True iff G is known to normalise an extraspecial p-group 
 or symplectic 2-group}

   flag := ExtraSpecialFlag (G); 
   if flag cmpeq true or flag cmpeq false then
      return flag;
   end if;

   d := Degree (G);
   fac := Factorisation (d);
   if #fac ne 1 then
      vprintf Smash: "Dimension %o is not a prime power\n", d;
      SetExtraSpecialFlag (G, false);
      return false;
   end if;
   r := fac[1][1];
   m := fac[1][2];
   if (#BaseRing(G)-1) mod r ne 0 then
      vprintf Smash:
         "Divisibility condition fails for extraspecial normaliser\n";
      SetExtraSpecialFlag (G, false);
      return false;
   end if;

   if IsPrime (d) and d ne 2 then 
      return RecogniseNormaliserExtraSpecial (G); 
   end if;

   symporder := r eq 2 select SimpleGroupOrder(<2,m,r>)
                     else 2 * SimpleGroupOrder(<2,m,r>);

   NmrTries := 50; nmr := 0;
   oldg := Random(G);
   for i in [1..NmrTries] do
      g := Random (G);
      o := ProjectiveOrder (g);
      if o mod r eq 0 then 
         nmr +:= 1;
         g := g^(o div r); 
         found := SearchForDecomposition
                            (G, [g]: Report := false, NoSymTens := true);
         if found then 
            flag := ExtraSpecialFlag (G); 
            if flag cmpeq true then
		vprintf Smash: "Found element of kernel after %o attempts\n", nmr;
               return flag;
            end if;
         end if;
      elif symporder mod o ne 0 then
         vprintf Smash: "Incompatible order of element\n", d;
         SetExtraSpecialFlag (G, false);
         return false;
      end if;
      gg := (g, oldg);
      oldg := g;
      g := gg;
      o := ProjectiveOrder (g);
      if o mod r eq 0 then 
         nmr +:= 1;
         g := g^(o div r); 
         found := SearchForDecomposition
                              (G, [g]: Report := false, NoSymTens := true);
         if found then 
            flag := ExtraSpecialFlag (G); 
            if flag cmpeq true then
		vprintf Smash: "Found element of kernel after %o attempts\n", nmr;
               return flag;
            end if;
         end if;
      end if;
      if symporder mod o ne 0 then
         vprintf Smash: "Incompatible order of element\n", d;
         SetExtraSpecialFlag (G, false);
         return false;
      end if;
   end for;

   return "unknown";
end intrinsic;

intrinsic ExtraSpecialAction (G::GrpMat, g::GrpMatElt) -> GrpMatElt
{Action matrix of element g on extraspecial or symplectic group normalised by G}

   esg := ExtraSpecialGroup (G);
   if esg cmpeq "unknown" then
      error "Group not known to normalise extraspecial or symplectic group";
   end if;

   d := Degree (G);
   if IsPrime (d) and d ne 2 then 
      return EpimorphicImage (esg, g); 
   end if;

   esgens := ExtraSpecialGenerators (G);
   params := ExtraSpecialParameters (G);
   r := params[1];
   m := #esgens div 2;
   x := [esgens[i] : i in [1..m]];
   y := [esgens[i] : i in [m+1..2*m]];
   z := (x[1], y[1]);
   gl := GL (2*m, GF (r));
   seq := [];
   for j in [1..m] do
      flag, h := Stripped (x[j]^g, x, y, z, r);
      if flag eq false then 
         error "Strip failed: Extraspecial group is not normalised by g";
      elif IsScalar (h[1]) eq false then
         error "Extraspecial group is not normalised by g";
      end if;
      t := Order (h[1]);
      if (not (r eq 2 and t eq 4)) and t ne r and t ne 1 then
         error "Extraspecial group is not normalised by g";
      end if;
      Append(~seq,h[2]);
   end for;
 
   for j in [1..m] do
      flag, h := Stripped (y[j]^g, x, y, z, r);
      if flag eq false then 
         error "Strip failed: Extraspecial group is not normalised by g";
      elif IsScalar (h[1]) eq false then
         error "Extraspecial group is not normalised by g";
      end if;
      t := Order (h[1]);
      if (not (r eq 2 and t eq 4)) and t ne r and t ne 1 then
         error "Extraspecial group is not normalised by g";
      end if;
      Append(~seq, h[2]);
   end for;

   return gl!(&cat(seq));
end intrinsic;
