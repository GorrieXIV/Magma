freeze;
 
/* GroupsOfOrderp4 generates the 15 (14 for p=2) groups 
   with order p^4 for all primes p.
   We bypass AbelianGroup and big powers 
   IdentifyGroupOfOrderp4 identifies groups with order p^4 */

GroupsOfOrderp4 := function (p)

   if not IsPrime (p) then "p must be prime"; return false; end if;

   if p eq 2 then
      L := SmallGroups(2^4);
   elif p eq 3 then
      L := SmallGroups(3^4);
   else
      w := PrimitiveRoot(p);
      L := [];
   
      G := Group<a | >;
      Append(~L, pQuotient(G,p,4));
   
      G := Group<a,b | (b,a)>;
      Append(~L, pQuotient(G,p,2));
   
      G := Group<a,b | b^p>;
      Append(~L, pQuotient(G,p,2));
   
      G := Group<a,b | (b,a) = b^p>;
      Append(~L, pQuotient(G,p,2));
   
      G := Group<a,b | b^p, (b,a)>;
      Append(~L, pQuotient(G,p,3));
   
      // here bypass a^(p^2)
      G := Group<a,b,x | x = a^p, b^p, (b,a) = x^p>;
      Append(~L, pQuotient(G,p,3));
   
      G := Group<a,b | (b,a,b), a^p, b^p>;
      Append(~L, pQuotient(G,p,3));
   
      G := Group<a,b | (b,a,b), a^p = (b,a,a) , b^p>;
      Append(~L, pQuotient(G,p,3));
   
      G := Group<a,b | (b,a,b), a^p, b^p = (b,a,a) >;
      Append(~L, pQuotient(G,p,3));
   
      G := Group<a,b | (b,a,b), a^p, b^p = (b,a,a)^w >;
      Append(~L, pQuotient(G,p,3));
   
      G := Group<a,b,c | (b,a), (c,a), (c,b), b^p, c^p>;
      Append(~L, pQuotient(G,p,2));
   
      G := Group<a,b,c | (c,a), (c,b), a^p, b^p, c^p>;
      Append(~L, pQuotient(G,p,2));
   
      G := Group<a,b,c | (c,a), (c,b), a^p = (b,a), b^p, c^p>;
      Append(~L, pQuotient(G,p,2));
   
      G := Group<a,b,c | (c,a), (c,b), a^p, b^p, c^p = (b,a)>;
      Append(~L, pQuotient(G,p,2));
   
      G := Group<a,b,c,d | >;
      Append(~L, pQuotient(G,p,1));
   
   end if;
   
   return L;
   
end function;
   
/* identify group of order p^4 */
   
IdentifyGroupOfOrderp4 := function (G)
   
   /* count elements of order p; avoid conjugacy 
      classes for abelian groups */
   Elsdp := function (G, p)
      if not IsAbelian (G) then 
         C := Classes (G);
         return &+[C[i][2]: i in [1..#C] | C[i][1] eq p] + 1;
      else 
         return p ^ #AbelianInvariants(G); /* billu's version! */
      end if;
   end function;

   p := FactoredOrder(G)[1][1];
   n := FactoredOrder(G)[1][2];
   
   if n ne 4 then
      "order not p^4";
      return false;
   end if;

   if p eq 2 then
      dG := #Generators(G);
      if dG eq 1 then
         return <p^n, 1>; 
      elif dG eq 4 then 
         return <p^n, 14>; 
      elif dG eq 3 then  
         D := DerivedGroup(G);
         if #D eq 1 then
           return <p^n, 10>; 
         elif IsCyclic(Centre(G)) then
            return <p^n, 13>; 
         elif Elsdp(G,2) eq 12 then
            return <p^n, 11>; 
         else
            return <p^n, 12>; 
         end if; //IsAb
      else // generator number 2
         D := DerivedGroup(G);
         if pClass(G) eq 2 then  
            if #D eq 1 then 
               return <p^n, 2>; 
            else 
               P := sub<G | G.1^p, G.2^p, G.3^p>;
               if #P eq p then
                  return <p^n, 3>; 
               else
                  return <p^n, 4>; 
               end if;
            end if; //IsAb and orders
         else //pclass
            if #D eq 1 then
               return <p^n, 5>; 
            elif NilpotencyClass(G) eq 2 then
               return <p^n, 6>; 
            else //nilpclass 3
               C := Centraliser(G,D);
               if G.1 in C then
                  x := G.1;
                  y := G.1*G.2;
               elif G.2 in C then
                  x := G.2;
                  y := G.1*G.2;
               else
                  x := G.1;
                  y := G.2;
               end if;
               if x^2 eq Id(G) and y^2 eq Id(G) then
                  return <p^n, 7>; 
               elif x^2 ne Id(G) and y^2 ne Id(G) then
                  return <p^n, 9>; 
               else  
                  return <p^n, 8>; 
               end if;
            end if; //nilpclass
         end if; //pclass
      end if; //generator number
   else // odd prime
      dG := #Generators(G);
      if dG eq 1 then
         return <p^n, 1>; 
      elif dG eq 4 then 
         return <p^n, 15>; 
      elif dG eq 3 then
         D := DerivedGroup(G);
         if #D eq 1 then
            return <p^n, 11>; 
         elif Exponent(G) eq p then
            return <p^n, 12>; 
         elif IsCyclic(Centre(G)) then
            return <p^n, 14>; 
         else
            return <p^n, 13>; 
         end if; //IsAb and more
      else // generator number 2 
         D := DerivedGroup(G);
         if pClass(G) eq 2 then 
            if #D eq 1 then 
               return <p^n, 2>; 
            else 
               P := sub<G | G.1^p, G.2^p, G.3^p>;
               if #P eq p then
                  return <p^n, 3>; 
               else
                  return <p^n, 4>; 
               end if;
            end if; //IsAb and orders
         else //pclass
            if #D eq 1 then
               return <p^n, 5>; 
            elif NilpotencyClass(G) eq 2 then
               return <p^n, 6>; 
            else //nilpclass 3
               C := Centraliser(G, D);
               x := Random(C);
               while x in D do x := Random(C); end while;
               if p eq 3 then
                  if x^3 eq Id(G) then
                     return <p^n, 7>; 
                  else
                     y := Random(G);
                     while y in C do y := Random(G); end while;
                     if y^3 ne Id(G) then 
                        if ((x*y)^3 eq Id(G) or (x*x*y)^3 eq Id(G)) then
                           return <p^n, 8>; 
                        else
                           return <p^n, 10>; 
                        end if;
                     else
                        if ((x*y)^3 ne Id(G) or (x*x*y)^3 ne Id(G)) then
                           return <p^n, 8>; 
                        else
                           return <p^n, 9>; 
                        end if;
                     end if;
                  end if; 
               else // prime ge 5
                  C := Centraliser(G, D);
                  x := Random(C);
                  while x in D do x := Random(C); end while;
                  y := Random(G);
                  while y in C do y := Random(G); end while;
                  if x^p eq Id(G) then
                     if y^p eq Id(G) then 
                        return <p^n, 7>; 
                     else
                        return <p^n, 8>; 
                     end if;
                  else
                     sq := [];
                     b := Integers() ! ((p-1)/2);
                     for i in [1..b] do
                        Append(~sq, i^2 mod p);
                     end for;
                     S := [x^(p*k):k in sq];
                     if (x,y,y) in S then
                        return <p^n, 9>; 
                     else
                        return <p^n, 10>; 
                     end if;
                  end if; //details
               end if; //prime >= 5 
            end if; //nilpclass
         end if; //pclass
      end if; //generator number
   end if; //odd prime
   
end function;

intrinsic Internal_p4_list(p::RngIntElt) -> SeqEnum
{For internal use}
    vprintf User5:"Computing groups of order %o^4\n", p;
    listp := GroupsOfOrderp4(p);
    return listp;
end intrinsic;

intrinsic Internal_p4_id(G::GrpPC) -> RngIntElt
{For internal use}
    return IdentifyGroupOfOrderp4(G)[2];
end intrinsic;

intrinsic Internal_p4_id(G::GrpPerm) -> RngIntElt
{For internal use}
    P := PCGroup(G);
    return IdentifyGroupOfOrderp4(P)[2];
end intrinsic;
