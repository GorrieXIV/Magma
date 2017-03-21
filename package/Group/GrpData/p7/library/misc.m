freeze;

declare verbose Orderp7, 2;

FrattiniRank := function (Q) 
   return NPCgens (Q) - NPCgens (FrattiniSubgroup (Q));
end function;

/* sample procedure which takes as input a given presentation,
   relevant prime and class; Process flag determines if 
   resulting pcp is stored or simply processed; 
   procedure can be readily updated later */

procedure ProcessPresentation (~L, GR, p, c, ~count: Select := func<x|true>,
                                Process := true)
   Q := pQuotient (GR, p, c);
   if Select (Q) eq false then return; end if;

   count +:= 1;
   if not Process then 
      /* set up group */
      Append (~L, Q);
   else
      /* group is now available to process */
      vprint Orderp7, 2: "Group has p-class ", pClass (Q), 
           "and Frattini rank", FrattiniRank (Q);
   end if;
end procedure;
