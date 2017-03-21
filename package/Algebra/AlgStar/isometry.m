freeze;

   /*--- This file contains main intrinsics for package. ---*/

import "verify.m": IsIsometry, IsSimilarity;

import "prelims.m": PreimageUsingWordGroup;

import "form.m": BilinearForm, SesquilinearForm;


          /*--- isometries of arbitrary systems of forms ---*/

intrinsic IsometryGroup (S::SeqEnum : 
  			    Autos := [0 : i in [1..#S]],
			    DisplayStructure := false
                        ) -> GrpMat

  { Find the group of isometries of the system of reflexive forms }

     require #S gt 0 : "argument 1 is empty";
     
     require #S eq #Autos : "arguments have unequal length";

     require forall { i : i in [1..#S] | 
                       Type (S[i]) eq AlgMatElt } :
        "elements of argument 1 are not forms";
     
     n := #S;
     MA := Parent (S[1]);
     k := BaseRing (MA);
     
     require Type (k) eq FldFin : 
        "Base ring of argument 1 is not a finite field.";
        
     require Characteristic (k) ne 2 : 
        "Base ring of argument 1 has characteristic 2.";
     
     d := Degree (MA);
     e := Degree (k);
     
     require forall { i : i in [2..n] | 
                      BaseRing (Parent (S[i])) eq k } :
        "Elements of argument 1 are not forms on a common module";
 
     require forall { i : i in [2..n] |
                      Degree (Parent (S[i])) eq d } :
        "Elements of argument 1 are not forms on a common module";
        
     require forall {f : f in Autos | (f eq 0) or (e mod f) eq 0} :
         "argument 2 is not a list of Frobenius exponents";

     /* deal with trivial case */
     if (#S eq 1) then
	 ISOM := IsometryGroup (S[1] : Auto := Autos[1]);
         return ISOM;
     end if;


         /*--- find the isometry group via the adjoint algebra ---*/
       
     /* reduce to the nondegenerate case */
     rad := &meet [ Nullspace (FrobeniusImage (S[i], Autos[i])) : 
                    i in [1..#S] ];
     r := Dimension (rad);
     if r gt 0 then
         comp := Complement (Generic (rad), rad);
         C := GL (d, k)!Matrix (Basis (comp) cat Basis (rad));
         nForms := [ ];
         for i in [1..n] do
            FC := FrobeniusImage (C, Autos[i]) * S[i] * Transpose (C);
	    F := ExtractBlock (FC, 1, 1, d-r, d-r);
            Append (~nForms, F);
	 end for;
     else
         nForms := S;
     end if;


     /* construct the adjoint algebra of <nForms> */
     ADJ := AdjointAlgebra (nForms : Autos := Autos);

     /* recognise the adjoint algebra */
     assert RecogniseStarAlgebra (ADJ);

     /* construct gens for the isometry group <nSigma> */
     gens := ADJ`StarAlgebraInfo`sharpGroupGenerators;
     ord := ADJ`StarAlgebraInfo`sharpGroupOrder;

     /* are we over the correct (input) field or over a subfield? */
     if #BaseRing (ADJ) lt #k then
         assert assigned ADJ`StarAlgebraInfo`mapToCorrectField;
         mtcf := ADJ`StarAlgebraInfo`mapToCorrectField;
         gens := [ GL (d-r, k)!(gens[t] @ mtcf) : t in [1..#gens] ];
     end if;
 
     /* make necessary adjustments in the case of a nontrivial radical */
     if (r gt 0) then
 
	 /* embed the generators from <ADJ> */
         ngens := [ ];
         for t in [1..#gens] do
            x := Identity (GL (d, k));
            InsertBlock (~x, gens[t], 1, 1);
            Append (~ngens, x);
         end for;

         /* add in GL(r,k) generators */
         gl_gens := [ GL (r, k).i : i in [1..Ngens (GL (r, k))] ];
         for i in [1..#gl_gens] do
            x := Identity (GL (d, k));
            InsertBlock (~x, gl_gens[i], d-r+1, d-r+1);
            Append (~ngens, x);
         end for;
         ord *:= #GL (r, k);

         /* to be safe, add in all unipotent generators */
         for i in [1..d-r] do
            for j in [d-r+1..d] do
               x := Identity (MatrixAlgebra (k, d));
               x[i][j] := 1;
               Append (~ngens, GL (d, k)!x);
	    end for;
         end for;
         ord *:= (#k)^(r*(d-r));

         /* conjugate back */
         gens := [ C^-1 * ngens[i] * C : i in [1..#ngens] ];

     end if;

     ISOM := sub < GL (d, k) | gens >;

     /* final sanity check */ 
     assert forall {t: t in [1..Ngens (ISOM)] |
     forall {i: i in [1..#S] | IsIsometry (S[i], Autos[i], ISOM.t) }};


     /* get simple types */
     stypes := [ S`StarSimpleInfo`simpleParameters : 
                 S in ADJ`StarAlgebraInfo`srComponents ];

     /* convert to group notation */
     if (r gt 0) then
         sgroups := [ < "GL" , r , [Characteristic (k), Degree (k)] > ];
     else
         sgroups := [ ];
     end if;
     for t in stypes do
         n := t[2];
         q := Factorization (t[3]);
         if t[1] eq "symplectic" then
            X := "Sp";
         elif t[1] eq "unitary" then
            X := "GU";
            q[1][2] := q[1][2] div 2;
         elif t[1] eq "orthogonalcircle" then
            X := "GO";
         elif t[1] eq "orthogonalminus" then
            X := "GOMinus";
         elif t[1] eq "orthogonalplus" then
            X := "GOPlus";
         else
            X := "GL";
            n := n div 2;
         end if;
         Append (~sgroups, <X, n, [q[1][1],q[1][2]]>);
     end for;

     p := Characteristic (k);
     f := Degree (k);

     exp := #ADJ`StarAlgebraInfo`alternatingRadical + f*r*(d-r);

     if DisplayStructure then
         "   G";
         for t in sgroups do
	    "   |  ", t[1],"(",t[2],",",t[3][1],"^",t[3][2],")";
            "   *";
	 end for;
         "   |  ", p,"^",exp,"   (unipotent radical)";
         "   1";
     end if;

     RF := recformat < order , facUROrder , simpleTypes >;
     SI_data := rec < RF | order := ord,
			   facUROrder := <p, exp>,
                           simpleTypes := sgroups
                     >;

     ISOM`StructuralInformation := SI_data;

return ISOM;

end intrinsic;


           /* ---- classical intersection ---- */

__my_determinant_map := function (X)
   return GL (1, BaseRing (X))![Determinant (X)];
end function;

__my_spinor_map := function (X, F)
   a := SpinorNorm (X, F);
   if a eq 0 then
      return Identity (GL (1, 3));
   else
      return -Identity (GL (1, 3));
   end if;
end function;

intrinsic ClassicalIntersection (S::SeqEnum) -> GrpMat

  { Find the intersection of a collection of classical groups defined
    on the same underlying module }

     require forall { G : G in S | Type (G) eq GrpMat } :
        "elements of argument are not matrix groups";
  
     k := BaseRing (S[1]);
     d := Degree (S[1]);
     
     require Characteristic (k) ne 2 : 
        "groups in argument are not defined over a finite field
         of odd characteristic";
         
     require forall { i : i in [2..#S] | BaseRing (S[i]) eq k } :
        "groups in argument are not defined on the same module";
  
     require forall { i : i in [2..#S] | Degree (S[i]) eq d } :
        "groups in argument are not defined on the same module"; 

     /* find forms preserved by <grps> */
     Forms := [ ];
     Autos := [ ];
     for i in [1..#S] do
         X := S[i];
         flag, F := BilinearForm (X);
         if (not flag) then
	    flag, F := SesquilinearForm (X);
            require flag : "argument is not a list of classical groups";
	    auto := Degree (k) div 2;
	 else
	    auto := 0;
         end if;
         Append (~Forms, F);
         Append (~Autos, auto);
     end for;

     /* find intersection of full isometry groups of these forms */
     ISOM := IsometryGroup (Forms : Autos := Autos, 
                                    DisplayStructure := false
                           );


         /*--- descend to the correct intersection ---*/

     /* first make sure we have the correct determinant */
     I := ISOM;
     D := GL (1, k);
     Idet_gens := [ __my_determinant_map (I.i) : i in [1..Ngens (I)]];
     Idet := sub < D | Idet_gens >;
     K := Idet;
     for i in [1..#S] do
         G := S[i];
         Gdet_gens := [ __my_determinant_map (G.j) : j in [1..Ngens (G)] ];
         Gdet := sub < D | Gdet_gens >;
         K meet:= Gdet;
      end for;
      if K ne Idet then
         J := PreimageUsingWordGroup (I, Idet, Idet_gens, K);
         J`StructuralInformation := I`StructuralInformation;
         J`StructuralInformation`order := 
               J`StructuralInformation`order div (#Idet div #K);
         I := J;
      end if;

      /* next impose individual spinor norm restrictions */
      D := GL (1, 3);
      for i in [1..#S] do
         G := S[i];
         F := Forms[i];
         if (Autos[i] eq 0) and (F eq Transpose (F)) then
            Isp_gens := [ __my_spinor_map (I.j, F) : j in [1..Ngens (I)] ];
            Isp := sub < D | Isp_gens >;
            Gsp_gens := [ __my_spinor_map (G.j, F): j in [1..Ngens (G)] ];
            Gsp := sub < D | Gsp_gens >;
            if not (Isp subset Gsp) then
               K := Isp meet Gsp;
               J := PreimageUsingWordGroup (I, Isp, Isp_gens, K);
               J`StructuralInformation := I`StructuralInformation;
               J`StructuralInformation`order := 
                     J`StructuralInformation`order div (#Isp div #K);
               I := J;
            end if;
         end if;
      end for;

return I;
end intrinsic;
