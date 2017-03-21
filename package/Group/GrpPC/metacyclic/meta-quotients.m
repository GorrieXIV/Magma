freeze;

/* M.F. Newman 060429

three new functions

HasAllPQuotientsMetacyclicGlobalShort := function(G);
HasAllPQuotientsMetacyclicGlobalLong := function(G);
HasAllPQuotientsMetacyclicLocal := function(G,p);

the first returns true/false according as for all p
all p-quotients are metacyclic or not

the second returns a description of the set of primes for which
there is a non-metacyclic p-quotient

the third returns true/false according as 
all p-quotients are metacyclic or not for the given prime


*/

HasAllPQuotientsMetacyclicGlobalShort := function(G);

   // requires Type (G) in [GrpFP]: "Argument must be an fp-group";
   A := AbelianQuotientInvariants (G);
   if #A gt 2 then //refine to get exceptional primes
     return false;
   else
     if #A eq 2 then
       y := A[#A-1];
     else
       y := 1;
     end if;
     if y eq 0 then
       Q := NilpotentQuotient(G,2);
       return IsAbelian(Q);
     else // y ne 0 and test primes dividing y
       if y eq 1 then  
         return true;
       else  
         // for all p not dividing y all p-quotients are cyclic
         Y := PrimeDivisors(y);
         flag := true;
         for p in Y do
           Q := pQuotient (G, p, 2);
           if (#Q gt p^4) then
             flag := false; break p;
           else
             id := IdentifyGroup (Q);
             if (id eq <p^4,3>) or
               (p ne 2 and (id eq <p^3,3>)) then
               flag := false; break p;
             end if;
           end if;
         end for;
         return flag;
       end if; 
     end if;
   end if;
end function;

HasAllPQuotientsMetacyclicGlobalLong := function(G);

   // requires Type (G) in [GrpFP]: "Argument must be an fp-group";
   A := AbelianQuotientInvariants (G);
   if #A gt 2 then 
     x := A[#A-2];
   else 
     x := 1;
   end if;
   if x eq 0 then
     return false, ["all primes"];
   else
     // for primes dividing x have non-metacyclic quotient
     if #A gt 1 then
       y := A[#A-1];
     else //abelian quotients cyclic
       return true, [];
     end if;
     if y eq 0 then
       Q := NilpotentQuotient(G,2);
       D := DerivedGroup(Q); 
       if not IsFinite(D) then
         return false, ["all primes"];
       else // IsFinite(D)
         d := #D;
         // for primes dividing d has non-metacyclic quotient
         if LCM(x,d) eq 1 then
           return true, [];
         else 
           return false, PrimeDivisors(LCM(x,d));
         end if;
       end if; 
      else 
        // for all p not dividing y all p-quotients are cyclic
        Y := PrimeDivisors(y);
        X := PrimeDivisors(x);
        if X eq Y then
          if #X eq 0 then
            return true, X;
          else
            return false, X;
          end if;
        else // X ne Y
          flag := true;
          for p in Y do
            if p notin X then
            Q := pQuotient (G, p, 2);
            if (#Q gt p^4) then
              flag := false; 
              Append(~X,p);
            else
              id := IdentifyGroup (Q);
              if (id eq <p^4,3>) or
                (p ne 2 and (id eq <p^3,3>)) then
                flag := false; 
                Append(~X,p);
              end if;
            end if;
          end if;
        end for;
        if #X ne 0 then
          flag := false;
        end if;
        return flag, X;
      end if; 
    end if;
  end if;

end function;


HasAllPQuotientsMetacyclicLocal := function(G,p);

   A := AbelianQuotientInvariants (G,p);

   if #A gt 2 then 
     return false;
   else
     Q := pQuotient (G, p, 2);
     if (#Q gt p^4) then
       return false;
     else
       id := IdentifyGroup (Q);
       if (id eq <p^4,3>) or
         (p ne 2 and (id eq <p^3,3>)) then
         return false;
       else
         return true;
       end if;
     end if;
   end if;

end function;

intrinsic HasAllPQuotientsMetacyclic (G::GrpFP) -> BoolElt, SeqEnum
{ return true if for all primes p all p-quotients of G are metacyclic;
  otherwise return false and a description of the set of primes 
  for which G has non-metacyclic p-quotient
}
   require Type (G) in [GrpFP]: "Argument must be an fp-group";
   return HasAllPQuotientsMetacyclicGlobalLong (G);
end intrinsic;
 

intrinsic HasAllPQuotientsMetacyclic (G :: GrpFP, p:: RngIntElt) -> BoolElt
{returns true if all p-quotients of G are metacyclic for the selected prime p, 
 otherwise false} 
   require Type (G) in [GrpFP]: "First argument must be an fp-group";
   require IsPrime (p): "Second argument must be a prime";
   return HasAllPQuotientsMetacyclicLocal (G, p);
end intrinsic;
