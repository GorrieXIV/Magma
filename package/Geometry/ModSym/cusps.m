freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: cusps.m (The set of cusps Q union {infinity}.)

   $Header: /home/was/modsym/RCS/cusps.m,v 1.1 2001/04/20 04:45:59 was Exp $

   $Log: cusps.m,v $
   Revision 1.1  2001/04/20 04:45:59  was
   Initial revision

   Revision 1.2  2000/05/02 07:53:34  was
   Added $Log: cusps.m,v $
   Added Revision 1.1  2001/04/20 04:45:59  was
   Added Initial revision
   Added to header

                                                                            
 ***************************************************************************/


/*

EXAMPLE:

      > Cusps();
      Set of cusps
      > Cusp(2,3);
      2/3
      > Cusp(1,0);
      oo
      > X:=Cusps();
      > X![4,6];
      2/3
      > X!(4/6);
      2/3
      > X!Infinity();
      oo
      > c:=X![3,9];
      > Eltseq(c);
      [ 1, 3 ]

*/

////////////////////////////////////////////////////////////////
//                                                            //
//                  Attribute declarations                    //
//                                                            // 
////////////////////////////////////////////////////////////////

declare type SetCsp [SetCspElt];

// nothing yet:
// declare attributes SetCsp: 

declare type SetCspElt;

declare attributes SetCspElt:
   parent,
   u, v;

////////////////////////////////////////////////////////////////
//                                                            // 
//                   Creation functions                       // 
//                                                            //
////////////////////////////////////////////////////////////////

TheCusps := New(SetCsp);

intrinsic Cusps() -> SetCsp
   {The set of cusps in the upper half plane; consists of the
    rational numbers together with infinity.}
   
   return TheCusps;
end intrinsic;


procedure Reduce(z)
   g := GCD(z`u,z`v);
   z`u := z`u div g;
   z`v := z`v div g;
end procedure;


intrinsic Cusp(u::RngIntElt, v::RngIntElt : Quick:=false) -> SetCspElt
{Create the cusp u/v. (The 'Quick' option skips checking that u and v are coprime)}
   if Quick then
      z := New(SetCspElt);
      z`parent := TheCusps;
      z`u := u;
      z`v := v;
   else
      require u ne 0 or v ne 0 : "One of arguments 1 and 2 must be nonzero.";
      z := New(SetCspElt);
      z`parent := TheCusps;
      z`u := u; 
      z`v := v;
      Reduce(z);
   end if;
   return z;
end intrinsic;


intrinsic Cusp(x::FldRatElt) -> SetCspElt
{Create the cusp at the given element of P^1(Q)}
   return Cusp(Numerator(x),Denominator(x));
end intrinsic;


intrinsic Cusp(x::RngIntElt) -> SetCspElt
{"} // "
   return Cusp(x,1);
end intrinsic;

intrinsic Cusp(x::Infty) -> SetCspElt
{"} // "
   return Cusp(1,0);
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//                     Coercions                              //
//                                                            // 
////////////////////////////////////////////////////////////////

intrinsic IsCoercible(X::SetCsp,x::.) -> BoolElt, SetCspElt
   {}
   case Type(x):
      when SetCspElt:
         return true, x;
      when SeqEnum:
         if #x ne 2 then
            return false, "Illegal coercion"; 
         end if;
         U := Type(Universe(x));
         if U eq FldRat then 
            d := LCM(Denominator(x[1]), Denominator(x[2]));
            x := [Integers()| d*x[1], d*x[2]];
         elif U ne RngInt then
            return false, "Illegal coercion"; 
         end if;
         return true, Cusp(x[1],x[2]);
      when RngIntElt, FldRatElt, Infty:
         return true, Cusp(x);
      else
         return false, "Illegal coercion"; 
   end case;
end intrinsic;

/*
intrinsic IsCoercible(X::SetCspElt,x::.) -> BoolElt, SetCspElt
{}
   return true, Parent(X)!x;
end intrinsic;
*/

////////////////////////////////////////////////////////////////
//                                                            //
//                     Printing                               //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic Print(X::SetCsp, level::MonStgElt)
   {}
   printf "Set of all cusps";
end intrinsic;


intrinsic Print(x::SetCspElt, level::MonStgElt)
   {}
   printf "%o", x`v eq 0 select "oo" else x`u/x`v;
end intrinsic;



////////////////////////////////////////////////////////////////
//                                                            //
//            Membership and equality testing                 //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., X::SetCsp) -> BoolElt
   {Returns true if x is in X.}
   if Type(x) eq SetCspElt then
      return x`parent eq X;
   end if;
   return false;
end intrinsic;

intrinsic Parent(x::SetCspElt) -> SetCsp
   {}
   return x`parent;
end intrinsic;

intrinsic 'eq' (x::SetCsp,Y::SetCsp) -> BoolElt
   {}
   return true;  // there is only one set of cusps.
end intrinsic;

intrinsic 'eq' (x::SetCspElt,y::SetCspElt) -> BoolElt
   {}
   return x`parent eq y`parent and 
          x`u eq y`u and x`v eq y`v;
end intrinsic;




////////////////////////////////////////////////////////////////
//                                                            //
//                Attribute Access Functions                  //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic Eltseq(x::SetCspElt) -> SeqEnum
   {For internal use}
   return [x`u, x`v];
end intrinsic;


////////////////////////////////////////////////////////////////
//                                                            //
//         Functionality, arithmetic operations, etc.         //
//                                                            //
////////////////////////////////////////////////////////////////


