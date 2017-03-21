freeze;
 
/* try to prove that G is perfect by proving that its generators
   are in G'; we do this by showing that the orders of the
   generators are 1 modulo G'

   algorithm is Monte-Carlo; if "true" is returned, then G is perfect;
   if "false" is returned, then G might still be perfect;

   basis of algorithm outlined in Leedham-Green and O'Brien;
   J. Algebra 253, 2002, 14-30 */

intrinsic IsProbablyPerfect (G :: GrpMat : NumberRandom := 100) -> BoolElt 
{this Monte-Carlo algorithm tries to prove that G is perfect by 
 establishing that its generators are in G'; if "true" is returned, then 
 G is perfect; if "false" is returned, then G might still be perfect} 

   K := sub<G | [ (G.i, G.j): i in [1..Ngens (G)], j in [1..Ngens (G)]]>;
   Z := Integers ();
   trial := [1..Ngens (G)];
   O := [{Z|} : i in [1..Ngens (G)]];
   for j in [1..NumberRandom] do
      k := NormalSubgroupRandomElement (G, K);
      for i in trial do
         o := Order (G.i * k:Proof:=false);
         Include (~O[i], o);
      end for;
      trial := [i : i in [1..Ngens (G)] | Gcd (O[i]) ne 1];
      if #trial eq 0 then return true; end if;
   end for;

   return false;

end intrinsic;

intrinsic IsProbablyPerfect (G :: GrpPerm : NumberRandom := 100) -> BoolElt 
{this Monte-Carlo algorithm tries to prove that G is perfect by 
 establishing that its generators are in G'; if "true" is returned, then 
 G is perfect; if "false" is returned, then G might still be perfect} 

   K := sub<G | [ (G.i, G.j): i in [1..Ngens (G)], j in [1..Ngens (G)]]>;
   Z := Integers ();
   trial := [1..Ngens (G)];
   O := [{Z|} : i in [1..Ngens (G)]];
   for j in [1..NumberRandom] do
      k := NormalSubgroupRandomElement (G, K);
      for i in trial do
         o := Order (G.i * k);
         Include (~O[i], o);
      end for;
      trial := [i : i in [1..Ngens (G)] | Gcd (O[i]) ne 1];
      if #trial eq 0 then return true; end if;
   end for;

   return false;

end intrinsic;
