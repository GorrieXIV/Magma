freeze;

/*--- This file contains functions for constructing involutions ---*/

import "prelims.m": IdentifyBasis;


/* construct involution on given algebra by specifying images of gens */

__Star_image := function (alg, MS, S, a)
     c := Coordinates (MS, MS!a);
     aa := &+[ c[i] * S[i] : i in [1..#c] ];
     return alg!aa;
end function;

StarOnBasis := function (A, S) 
     // first find a basis of the input <A>
     Q := [ Vector (A.i) : i in [1..Ngens (A)] ];
     positions := IdentifyBasis (Q);
     bas := [ A.i : i in positions ];
     ims := [ S[i] : i in positions ];
     MS := KMatrixSpace (BaseRing (A), Degree (A), Degree (A));
     MS := KMatrixSpaceWithBasis ([ MS!(bas[i]) : i in [1..#bas] ]);
return hom < A -> A | a :-> __Star_image (A, MS, ims, a) >;
end function;


/* construct the natural involution on a group algebra */

intrinsic StarOnGroupAlgebra (A::AlgGrp) -> Map

  { The natural involution on the group algebra 
    A induced by inversion }   

     BasA := Basis (A);
     iBasA := [ BasA[i]^-1 : i in [1..#BasA] ];
     star := hom < A -> A | a :-> &+ [ c[i] * iBasA[i] : i in [1..#c] ]     
                            where c := Coefficients (a) >;
     A`Star := star;

return star;
end intrinsic;


intrinsic IsStarAlgebra (A::AlgMat) -> BoolElt
   { True if the algebra A is equipped with an involution. }
return assigned (A`Star);
end intrinsic;


intrinsic IsStarAlgebra (A::AlgGrp) -> BoolElt
   { True if the group algebra A has an assigned involution. Note that 
     A always has a canonical involution even if one is not assigned. }
return assigned (A`Star);
end intrinsic;


intrinsic Star (A::AlgMat) -> Map
   { Access the involution of A. }
     require IsStarAlgebra (A) : "argument is not a *-algebra";
return A`Star;
end intrinsic;


intrinsic Star (A::AlgGrp) -> Map
   { Access the involution of A. }
     if not IsStarAlgebra (A) then
         /* equip <A> with its natural involution */
         star := StarOnGroupAlgebra (A);
         A`Star := star;
     end if;
return A`Star;
end intrinsic;
