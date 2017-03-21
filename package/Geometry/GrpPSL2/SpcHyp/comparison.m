freeze;

////////////////////////////////////////////////////////////////
//                                                            //
//            Membership and equality testing                 //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic 'in'(x::.,H::SpcHyp) -> BoolElt
   {}
   if Type(x) eq SpcHypElt then return true; end if;
   return false;
end intrinsic;
 
intrinsic 'eq' (X::SpcHyp,Y::SpcHyp) -> BoolElt
   {checks whether two hyperbolic spaces have the same dimension}
   return X`dimension eq Y`dimension;
end intrinsic;

intrinsic 'eq' (x::SpcHypElt,y::SpcHypElt) -> BoolElt
   {}
   if not [x`is_exact,x`is_cusp] eq [y`is_exact,y`is_cusp] then
      return false;
   end if;
   if not x`parent eq y`parent then
      return false;
   end if;
   case [x`is_exact,x`is_cusp]:
   when [true, true]:
       return  (x`exact_value eq y`exact_value);   
   when [true, false]:
       return (Parent(x`exact_value) cmpeq Parent(y`exact_value)) and 
                  (x`exact_value eq y`exact_value);
   when [false,false]:
       return x`complex_value eq y`complex_value;
   else return false;
   end case;              

end intrinsic;

// note, the following function might not be needed if
// SpcHypElt was not a HackObj
// note, forced to use misleading name; this should not be
// in export version

intrinsic 'lt' (x::SpcHypElt,Y::[SpcHypElt]) -> BoolElt
   {}
   found := false;
   i := 1;
   while not found and i le #Y do
      if x eq Y[i] then
	 return true;
	 found := true;
      end if;
      i +:=1;
   end while;
   return found;
end intrinsic;


// similar comments to above, only more so, this being
// related to William's SetCspElt type.

intrinsic 'lt' (x::SetCspElt,Y::[SetCspElt]) -> BoolElt
   {}
   found := false;
   i := 1;
   while not found and i le #Y do
      if x eq Y[i] then
	 return true;
	 found := true;
      end if;
      i +:=1;
   end while;
   return found;
end intrinsic;



