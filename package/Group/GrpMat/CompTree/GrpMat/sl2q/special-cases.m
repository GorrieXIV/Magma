freeze;

/* identify standard generators for SL(2, p) */

SL2pStandardGenerators := function (G, p)

   NmrTimes := 100;

   /* element of order p */
   found := false;
   for i in [2..NmrTimes] do 
      flag, g := RandomElementOfOrder (G, p);
      if flag then found := true; break i; end if;
   end for;

   if not found then 
      vprint sl2q: "No element of order p found; probably not SL(2, p)"; 
      return false, _; 
   end if;

   /* non-commuting conjugate of G */
   P := RandomProcess (G);
   id := Identity (G);
   found := false;
   trial := 100; 
   repeat 
      x := Random (P);
      h := g^x;
      found := (g, h) ne id;
      trial -:= 1;
   until found or trial eq 0;
     
   if not found then 
      vprint sl2q: "No non-commuting conjugate found; probably not SL(2, p)"; 
      return false, false; 
   end if;

   return true, [g, h];

end function;

/* S is SL(2, p) in some repn, is G isomorphic to S? */

SL2pIsomorphic := function (S, G)
   p := Characteristic (BaseRing (G));
    
   MS := GModule (S);

   flag, gens := SL2pStandardGenerators (G, p);
   if flag eq false then return false, _; end if;
    
   /* now gens are standard generators for SL(2, p) */
   for i in [1..p - 1] do
      H := sub <G | gens[1], gens[2]^i>;
      M := GModule (H);
      flag, CB := IsIsomorphic (MS, M); 
      if flag then return true, CB; end if;
   end for;

   return false, _;

end function;

/* special case of n-th symmetric power recognition 
   for SL(2, p), when n >= (p - 5)/2 */

SpecialIsSymmetricPower := function (G)
   F := BaseRing (G);
   p := #F;
   if not IsPrime (p) then 
      vprint sl2q: "Special symmetric power code applies to prime case only"; 
      return false, _; 
   end if;
   n := Degree (G) - 1;

   /* standard generators for SL(2, p) in its natural repn */
   S := sub <GL(2, p) | [1,1,0,1], [1,0,1,1]>;    
   SP := ActionGroup (SymmetricPower (GModule (S), n));
   return SL2pIsomorphic (SP, G);

end function;
