freeze;

/* groups of order p^5 for prime p >= 5, translated by 
   O'Brien from GAP list prepared by Boris Girnat;
   since linear ordering does not coincide with existing
   list in SmallGroups for 5^5, we restrict to p > 5  */

/* add trivial commutator and power relations to f */

AddTrivials := function (f, p)
   n := Ngens (f);

   id := Identity (f);
   rels := Relations (f);
   L := [LHS (r): r in rels];
   new := [];
   for i in [1..n] do
     for j in [i + 1..n] do
        r := (f.j, f.i); 
        if not r in L then 
           f := AddRelation (f, r = id); 
           rels := Relations (f);
           L := [LHS (r): r in rels];
           id := Identity (f);
        end if; 
     end for;
   end for;
   for i in [1..n] do
        r := f.i^p; 
        if not r in L then 
           f := AddRelation (f, r = id); 
           rels := Relations (f);
           L := [LHS (r): r in rels];
           id := Identity (f);
        end if;
   end for;
   return f;
end function;

/* number of groups of order p^5 */

NumberOfGroupsOfOrderp5 := function(p)
   if p eq 2 then
      return 51;
   elif p eq 3 then
      return 67;
   elif IsPrime (p) then  
      return 61+2*p+2*Gcd(3,p-1)+Gcd(4,p-1);
   else
      error "p must be a prime";
   end if;
end function;

/* group #t of order p^5 */

GroupOfOrderp5 := function (p, t)

   SetPower := function (f, x, y)
      f := AddRelation (f, x^p = y);
      return f;
   end function;
   
   SetCommutator := function (f, x, y, z)
      f := AddRelation (f, (x, y) = z);
      return f;
   end function;
   
   f := FreeGroup(5);
   w := PrimitiveRoot (p);
   
   a := Gcd(3,p-1);
   b := Gcd(4,p-1);
   z := 61+2*p+2*a+b;
   
   if t eq 1 then
     f := SetPower(f,f.1,f.2);
     f := SetPower(f,f.2,f.3);
     f := SetPower(f,f.3,f.4);
     f := SetPower(f,f.4,f.5);
   elif t eq 2 then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.5);
   elif t eq 3 then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5);
   elif t eq 4 then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.2,f.5);
   elif t eq 5 then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.2,f.4);
   elif t eq 6 then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.2,f.4^w);
   elif t eq 7 then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.5);
   elif t eq 8 then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4*f.5);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.5);
   elif t eq 9 then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4*f.5^w);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.5);
   elif t eq 10 then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.5^w);
     f := SetCommutator(f,f.3,f.2,f.4);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.5);
   elif t in [11..11+(p-1) div 2-1] then
     k := t-10;
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5^(w^k mod p));
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.5);
   elif t in [11+(p-1) div 2..11+p-2] then
     k := t-(11+(p-1) div 2-1);
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4*f.5^(w^k mod p));
     f := SetCommutator(f,f.3,f.2,f.4^(w^(k-1) mod p)*f.5);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.5);
   elif t eq 10+p then
     f := SetPower(f,f.1,f.3);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 11+p then
     f := SetCommutator(f,f.2,f.1,f.5);
     f := SetPower(f,f.1,f.3);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 12+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.4,f.5);
   elif t eq 13+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetPower(f,f.1,f.4);
   elif t eq 14+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.5);
   elif t eq 15+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.5^w);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.5);
   elif t eq 16+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.4,f.5);
   elif t eq 17+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.1,f.4);
   elif t eq 18+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.5);
   elif t eq 19+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.4,f.5);
   elif t eq 20+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.5^w);
     f := SetCommutator(f,f.3,f.2,f.5^w);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.4,f.5);
   elif t eq 21+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetCommutator(f,f.4,f.2,f.5^(p-1));
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.3);
     f := SetPower(f,f.3,f.5); 
   elif t eq 22+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.2,f.3);
     f := SetPower(f,f.4,f.5);
   elif t eq 23+p then
     f := SetPower(f,f.1,f.3);
     f := SetPower(f,f.3,f.4);
     f := SetPower(f,f.4,f.5);
   elif t eq 24+p then
     f := SetCommutator(f,f.2,f.1,f.5);
     f := SetPower(f,f.1,f.3);
     f := SetPower(f,f.3,f.4);
     f := SetPower(f,f.4,f.5);
   elif t eq 25+p then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.4,f.1,f.5);
   elif t in [25+p+1..25+p+a] then
     k := t-(25+p);
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.4,f.1,f.5^(w^k mod p));
     f := SetPower(f,f.2,f.5);
   elif t eq 26+p+a then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.4,f.1,f.5);
     f := SetPower(f,f.1,f.5);
   elif t eq 27+p+a then
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.4,f.1,f.5);
     f := SetCommutator(f,f.3,f.2,f.5);
   elif t in [27+p+a+1..27+p+2*a] then
     k := t-(27+p+a);
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.4,f.1,f.5^(w^k mod p));
     f := SetCommutator(f,f.3,f.2,f.5^(w^k mod p));
     f := SetPower(f,f.2,f.5);
   elif t in [27+p+2*a+1..27+p+2*a+b] then 
     k := t-(27+p+2*a);
     f := SetCommutator(f,f.2,f.1,f.3);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.4,f.1,f.5^(w^k mod p));
     f := SetCommutator(f,f.3,f.2,f.5^(w^k mod p));
     f := SetPower(f,f.1,f.5);
   elif t eq 28+p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.3,f.1,f.5);
   elif t eq 29+p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 30+p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.3,f.5);
   elif t eq 31+p+2*a+b then
     f := SetCommutator(f,f.3,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 32+p+2*a+b then
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.3,f.5);
   elif t eq 33+p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.3,f.4);
   elif t eq 34+p+2*a+b then
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 35+p+2*a+b then
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 36+p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 37+p+2*a+b then
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 38+p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 39+p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.5);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 40+p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4*f.5);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 41+p+2*a+b then
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t in [41+p+2*a+b+1..41+p+2*a+b+(p-1) div 2] then
     k := t-(41+p+2*a+b);
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.3,f.1,f.5^(w^k mod p));
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 42+p+2*a+b+(p-1) div 2 then
     f := SetCommutator(f,f.2,f.1,f.5^w);
     f := SetCommutator(f,f.3,f.1,f.4);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t in [42+p+2*a+b+(p-1) div 2+1..42+p+2*a+b+p-1] then
     k := t-(42+p+2*a+b+(p-1) div 2);
     f := SetCommutator(f,f.2,f.1,f.4*f.5^(w^k mod p));
     f := SetCommutator(f,f.3,f.1,f.4^(w^(k-1) mod p)*f.5);
     f := SetPower(f,f.2,f.4);
     f := SetPower(f,f.3,f.5);
   elif t eq 42+2*p+2*a+b then
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.4,f.5);
   elif t eq 43+2*p+2*a+b then
     f := SetCommutator(f,f.3,f.2,f.5);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.4,f.5);
   elif t eq 44+2*p+2*a+b then
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetPower(f,f.1,f.4);
     f := SetPower(f,f.4,f.5);
   elif t eq 45+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.4,f.2,f.5);
   elif t eq 46+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.4,f.2,f.5);
     f := SetPower(f,f.3,f.5);
   elif t eq 47+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.4,f.2,f.5);
     f := SetPower(f,f.2,f.5);
   elif t eq 48+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.4,f.2,f.5);
     f := SetPower(f,f.1,f.5);
   elif t eq 49+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.4,f.2,f.5^w);
     f := SetPower(f,f.1,f.5); 
   elif t eq 50+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.4,f.2,f.5);
     f := SetCommutator(f,f.3,f.1,f.5);
   elif t eq 51+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.4,f.2,f.5);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetPower(f,f.3,f.5);
   elif t eq 52+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.4,f.2,f.5);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetPower(f,f.2,f.5);
   elif t eq 53+2*p+2*a+b then      
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.4,f.2,f.5);
     f := SetCommutator(f,f.3,f.1,f.5);
     f := SetPower(f,f.1,f.5);
   elif t eq 54+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.4);
     f := SetCommutator(f,f.4,f.2,f.5^w);
     f := SetCommutator(f,f.3,f.1,f.5^w);
     f := SetPower(f,f.1,f.5);
   elif t eq 55+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.5);
   elif t eq 56+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.5);
     f := SetCommutator(f,f.4,f.3,f.5);
   elif t eq 57+2*p+2*a+b then
     f := SetPower(f,f.1,f.5);
   elif t eq 58+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.5);
     f := SetPower(f,f.1,f.5);
   elif t eq 59+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.5);
     f := SetPower(f,f.3,f.5);
   elif t eq 60+2*p+2*a+b then
     f := SetCommutator(f,f.2,f.1,f.5);
     f := SetCommutator(f,f.4,f.3,f.5);
     f := SetPower(f,f.4,f.5);
   elif t eq 61+2*p+2*a+b then
   end if;
   
   f := AddTrivials (f, p);
   return pQuotient (f, p, 5);
end function;
   
GroupsOfOrderp5 := function (p)
   
   if not IsPrime (p) or p lt 7 then
      "p must be a prime at least 7";
      return false;
   end if;

   n := NumberOfGroupsOfOrderp5 (p);
   return [GroupOfOrderp5 (p, i): i in [1..n]];

end function;

intrinsic Internal_p5_list(p::RngIntElt) -> SeqEnum
{For internal use}
    return GroupsOfOrderp5(p);
end intrinsic;
