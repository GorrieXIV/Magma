freeze;

/* module is a KG-module and constit is an irreducible constituent of
   module. MinimalSubmodule returns a submodule of module having only 
   constit in its head and no proper submodule of the returned 
   submodule can have constit as a constituent. */

MinimalSubmodule := function (module, constit)
   
   /* First see if there are any submodules isomorphic to constit. */

   h := GHom (constit, module);
   if Dimension (h) gt 0 then
     return Image (h.1);
   end if;

   /* There is not - so we have to work harder. */
   series, factors := CompositionSeries (module);
   found := 0;
   for i in [1..#series] do
     if IsIsomorphic (constit, factors[i]) then
       found := i;
       break;
     end if;
   end for;
   if found eq 0 then return module; end if;

   /* Our first candidate for the submodule we are looking 
      for is series[i].  We see if there is a smaller one 
      by looking for maps onto the other constituents. */

   submodule := series[found];
   constit_list := Constituents (module);
   for c in constit_list do
     if IsIsomorphic (c, constit) then
       Exclude (~constit_list, c);
       break;
     end if;
   end for;

   repeat
     smaller := false;
     for c in constit_list do
       h := GHom (submodule, c);
       if Dimension (h) gt 0 then
          submodule := Kernel (h.1);
          smaller := true;
          break;
       end if;
     end for;
   until smaller eq false;

   return submodule;
   
end function;
