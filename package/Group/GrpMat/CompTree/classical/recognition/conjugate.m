freeze;

//$Id:: conjugate.m 1112 2008-10-14 02:53:47Z jbaa004                        $:

import "../../GrpMat/ClassicalRec/sld2.m": OrthogonalForm2;

StandardSpForm := function (n, q)
   assert IsEven (n);
   A := MatrixAlgebra (GF (q), 2);
   J := A![0,1,-1,0];
   m := n div 2;
   return DiagonalJoin ([J: i in [1..m]]);
end function;

StandardSUForm := function (n, q)
   A := MatrixAlgebra (GF (q^2), 2);
   J := A![0,1,1,0];
   m := n div 2;
   form := DiagonalJoin ([J: i in [1..m]]);
   if IsOdd (n) then
      a := Identity (MatrixAlgebra (GF(q^2), 1));
      form := DiagonalJoin (form, a);
   end if;
   return form;
end function;

StandardOPlusForm := function (n, q)
   A := MatrixAlgebra (GF (q), 2);
   J := A![0,1,1,0];
   m := n div 2;
   return DiagonalJoin ([J: i in [1..m]]);
end function;

StandardOMinusForm := function (n, q)
   F := GF (q);
   E<delta> := GF (q^2);
   mu := delta^((q + 1) div 2);
   A := MatrixAlgebra (GF (q), 2);
   J := A![0,1,1,0];
   m := (n - 2) div 2;
   a := A![-2, 0, 0, 2 * mu^2];
   form := DiagonalJoin ([J: i in [1..m]] cat [a]);
   return form;
end function;

StandardOForm := function (n, q)
   A := MatrixAlgebra (GF (q), 2);
   J := A![0,1,1,0];
   m := (n - 1) div 2;
   J := DiagonalJoin ([J: j in [1..m]]); 
   MA := MatrixAlgebra (GF(q), n);
   form := Zero (MA);
   InsertBlock (~form, J, 1, 1);
   form[n][n] := -1/2;
   return form;
end function;

OrthogonalForm := function (G)
   if Degree (G) eq 2 then 
      flag, type, form := OrthogonalForm2(G);
   else 
     //print G;
     flag, form, type := SymmetricBilinearForm (G);
     /*
      if type eq 1 then type := "orthogonalplus";
      elif type eq 0 then type := "orthogonalcircle";
      elif type eq -1 then type := "orthogonalminus";
      else error "Error in Type returned by SBF"; 
      end if;
	*/
   end if;
   return flag, form, type;
end function;

/* G is a classical group of supplied type, 
   construct standard copy and transformation matrix */
 
ConjugateToStandardCopy := function (G, type) 

   F := BaseRing (G);
   q := #F;
   d := Degree (G);

   if type eq "orthogonalminus" then 
      flag, form, type := OrthogonalForm (G);
      standard := StandardOMinusForm (d, q);
   elif type eq "orthogonalplus" then  
      flag, form, type := OrthogonalForm (G);
      standard := StandardOPlusForm (d, q);
   elif type eq "orthogonal" then  
      flag, form, type := OrthogonalForm (G);
      standard := StandardOForm (d, q);
   elif type eq "unitary" then 
      flag, form := UnitaryForm (G);
      assert flag;
      standard := StandardSUForm (d, Isqrt (q));
   elif type eq "symplectic" then 
       flag, form := SymplecticForm (G);
       if not flag then
	   flag, form := SymplecticForm (G : Scalars := true);
       end if;
      assert flag;
      standard := StandardSpForm (d, q);
   else
      error "Type incorrect for ConjugateToStandardCopy";
   end if;
  
   if form eq standard then return G, Identity (G); end if;

   x := TransformForm (form, type);
   y := TransformForm (standard, type);
   cb := x * y^-1;

   return G^cb, cb;
end function;

StandardO := function (n, q: Special := false)
   form := StandardOForm (n, q);
   if Special then
      G := SO (n, q);
   else
      G := Omega (n, q);
   end if;
   CB := TransformForm (form, "orthogonalcircle");
   return G^(CB^-1), form;
end function;

StandardOMinus := function (n, q: Special := false)
   form := StandardOMinusForm (n, q);
   if Special then
      G := SOMinus (n, q);
   else
      G := OmegaMinus (n, q);
   end if;
   CB := TransformForm (form, "orthogonalminus");
   return G^(CB^-1), form;
end function;

StandardOPlus := function (n, q: Special := false)
   form := StandardOPlusForm (n, q);
   if Special then
      G := SOPlus (n, q);
   else
      G := OmegaPlus (n, q);
   end if;
   CB := TransformForm (form, "orthogonalplus");
   return G^(CB^-1), form;
end function;

StandardSU := function (n, q)
   form := StandardSUForm (n, q);
   G := SU (n, q);
   CB := TransformForm (form, "unitary");
   return G^(CB^-1), form;
end function;

StandardSp := function (n, q)
   form := StandardSpForm (n, q);
   G := Sp (n, q);
   CB := TransformForm (form, "symplectic");
   return G^(CB^-1), form;
end function;
