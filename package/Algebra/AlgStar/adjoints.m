freeze;

   /*--- Compute algebra of adjoints of system of forms ---*/


import "prelims.m":  SolveSystem, __RF_SETUP, IdentifyBasis;

import "star.m": StarOnBasis;

import "form.m": PrepareSystem, SlopeOfPair, IdentifyOrthogonalType;

import "centraliser.m": CentraliserOfMatrix;

import "complements.m": TaftComplement;


      /* ---- the default method for general systems ---- */

/* 
   Computes <A>, the algebra of adjoints of a system of 
   bilinear forms by solving a system of linear equations.

   It is assumed here that all forms in <Forms> have
   radicals; otherwise it's faster to compute ADJ as
   the centralizer of an algebra.
   
   It is also assumed that all forms are bilinear.

   It is easy enough here to decompose <A> into
   its symmetric and alternating parts, so we do.
*/
   
__default_adj := function (Forms)

     MA := Parent (Forms[1]);

     /* basis for SYM */     
     SYM := &meet [ SolveSystem (M, -M) : M in Forms ];
     SYM_BASIS := [ MA!Eltseq (b) : b in Basis (SYM) ];
     
     /* basis for ALT */
     ALT := &meet [ SolveSystem (M, M) : M in Forms ];
     ALT_BASIS := [ MA!Eltseq (b) : b in Basis (ALT) ];
     ALT := sub < MA | ALT_BASIS >;

     /* construct ADJ and its involution */
     ADJ := sub < MA | SYM_BASIS cat ALT_BASIS >;
     ADJ`IsBasis := true;
     STAR_BASIS := SYM_BASIS cat [ -ALT_BASIS[i] : i in [1..#ALT_BASIS] ];
     star := StarOnBasis (ADJ, STAR_BASIS);
     ADJ`Star := star;

     /* we need to start from scratch to find a Taft decomp */
     RAD, TAFT := TaftDecomposition (ADJ);
     RAD`Star := ADJ`Star;
     TAFT`Star := ADJ`Star;
     TAFT_RF := __RF_SETUP ("algebra");
     TAFT_data := rec < TAFT_RF | >;
     TAFT_data`isSemisimple := true;
     TAFT_data`taftComplement := TAFT;
     TAFT_data`jacobsonRadical := sub < Generic (TAFT) | TAFT!0 >;
     TAFT`StarAlgebraInfo := TAFT_data;

     /* compute generators for <alternating_radical> */
     space := KMatrixSpace (BaseRing (ADJ), Degree (ADJ), Degree (ADJ));
     if Dimension (RAD) * Dimension (ALT) eq 0 then
         ALT_RAD := sub < space | space!0 >;
     else
         ALT_SPACE := sub < space | 
                   [ space!(ALT_BASIS[i]) : i in [1..#ALT_BASIS] ] >;
         RAD_SPACE := sub < space | 
                              [ space!(RAD.i) : i in [1..Ngens (RAD)] ] >;
         ALT_RAD := ALT_SPACE meet RAD_SPACE;
     end if;
       
     /* convert <ALT_RAD> to a basis over the prime field */
     k := BaseRing (MA);
     e := Degree (k);
     BAR := Basis (ALT_RAD);
     ALT_RAD := [ (k.1)^f * BAR[i] : f in [0..e-1], i in [1..#BAR] ];
              
     RF := __RF_SETUP ("algebra");
     ADJ_data := rec < RF | >;

     ADJ_data`alternatingRadical := ALT_RAD;
     ADJ_data`isSemisimple := (Dimension (RAD) eq 0);
     ADJ_data`taftComplement := TAFT;
     ADJ_data`jacobsonRadical := RAD;

     ADJ`StarAlgebraInfo := ADJ_data;
                     
return ADJ;
end function;


               /*--- the centraliser method ---*/

/*
   Computes <A>, the algebra of adjoints of a system of 
   reflexive forms of the same basic type, and whose 
   first member is nondegenerate.
   
   In this method all <F> in <Forms> must have the same
   basic type, but all can be specified Hermitian by
   redefining <auto> to be the appropriate Frobenius power.
*/
__centraliser_adj := function (Forms : auto := 0)

     F := Forms[1];
     assert Rank (F) eq Nrows (F);
     Fi := F^-1;
     MA := Parent (F);

     gens := [ FrobeniusImage (Forms[i] * Fi, auto) : i in [2..#Forms] ];
     alg := sub < MA | gens >;
     ADJ := Centraliser (MA, alg);
     ADJ`Star := hom < ADJ -> ADJ | 
                        r :-> Transpose (Fi * FrobeniusImage (r, auto) * F) >;
     
     /* we need to start from scratch to find a Taft decomp */
     RAD, TAFT := TaftDecomposition (ADJ);
     RAD`Star := ADJ`Star;
     TAFT`Star := ADJ`Star;
     TAFT_RF := __RF_SETUP ("algebra");
     TAFT_data := rec < TAFT_RF | >;
     TAFT_data`isSemisimple := true;
     TAFT_data`taftComplement := TAFT;
     TAFT_data`jacobsonRadical := sub < Generic (TAFT) | TAFT!0 >;
     TAFT`StarAlgebraInfo := TAFT_data;
     
     RF := __RF_SETUP ("algebra");
     ADJ_data := rec < RF | >;
     ADJ_data`isSemisimple := (Dimension (RAD) eq 0);
     ADJ_data`taftComplement := TAFT;
     ADJ_data`jacobsonRadical := RAD;
     ADJ`StarAlgebraInfo := ADJ_data;
     
return ADJ;
end function;


                  /*--- the slope method ---*/

/*
   Computes <A>, the algebra of adjoints of a pair of reflexive
   forms, <F> and <G>, where <F> is assumed nondegenerate.
   <btF> and <btG> are the basic types of <F> and <G> 
   (bilinear or sesquilinear).
   
   It also decomposes <A> into <J> + <T> where <J> is the
   Jacobson radical and <T> is a *-invariant complement.
   Finally, it attaches to <T> its list of minimal *-ideals, as
   well as the basic types of these ideals (classical or exchange).
*/

__slope_adj := function (F, G, autF, autG)

     assert Nrows (F) eq Rank (F);
     Finv := F^-1;

     d := Degree (Parent (F));
     K := BaseRing (Parent (F));
     e := Degree (K);

     f, S := SlopeOfPair (F, G, autF, autG);

     if f eq 0 then
         ADJ := CentraliserOfMatrix (S);
         ADJ`IsBasis := true;
     else   /* <ADJ> is the centraliser of a semilinear transformation */
       error ("cross-type slope method has not yet been implemented");
       /* at present, code is set up to default to generic method */
     end if;

     /* define the involution on <ADJ> */
     ADJ_star := hom < ADJ -> ADJ | 
                 c :-> Transpose (Finv * FrobeniusImage (c, autF) * F) 
                      >;

     ADJ`Star := ADJ_star;
     
     /* find a *-invariant complement to <rad> */
     RAD := ADJ`AlgebraInfo`jacobsonRadical;
     WED := ADJ`AlgebraInfo`wedderburnComplement;
     TAFT, phi := TaftComplement (ADJ, RAD, WED);
     TAFT`Star := ADJ`Star;
     RAD`Star := ADJ`Star;
     
     RF := __RF_SETUP ("algebra");

     /* find the minimal *-ideals of <TAFT> */
     simples := ADJ`AlgebraInfo`simpleComponents;
     images := < >;
     imspaces := < >;
     for i in [1..#simples] do
        Si := simples[i];
        Xi := sub < Generic (ADJ) | 
                      [ (Si.j) @ phi : j in [1..Ngens (Si)] ] >;
        Append (~images, Xi);
        Append (~imspaces, 
                     &+ [ Image (Xi.j) : j in [1..Ngens (Xi)] ]);
     end for;
       
     star_simples := < >;
     btypes := < >;             
     for i in [1..#images] do

         Xi := images[i];
         assert exists (xi){ z : z in Generators (Xi) | z ne 0 };
         im := Image (xi @ ADJ`Star);
         test := [ imspaces[l] meet im : l in [1..#imspaces] ];
         assert exists (j){ l : l in [1..#test] | 
                                    Dimension (test[l]) gt 0 };

         if (j ge i) then

            if (i eq j) then

               btype := "classical";
               Ui := Xi;

            elif (j gt i) then

               btype := "exchange";
               Ui := sub < Generic (ADJ) | 
                       [ Xi.j : j in [1..Ngens (Xi)] ] cat
                    [ (Xi.j) @ ADJ`Star : j in [1..Ngens (Xi)] ] >;

            end if;

            Ui`Star := ADJ`Star;

            Ui_data := rec < RF | isSimple := true,
                                  isSemisimple := true,
                                  jacobsonRadical := 
                                     sub < Generic (ADJ) | ADJ!0 >,
                                  taftComplement := Ui,
                                  basicSimpleTypes := < btype >
                           >;

            Ui`StarAlgebraInfo := Ui_data;

            Ui`IsBasis := true;

            Append (~star_simples, Ui);
            Append (~btypes, btype);

         end if;

     end for;

     /* find a nice basis that exhibits the *-simples */ 
     newbas := [ ];
     srdegrees := [ ];
     for i in [1..#star_simples] do
         U := star_simples[i];
         imU := &+ [ Image (U.j) : j in [1..Ngens (U)] ];
         newbas cat:= Basis (imU);
         Append (~srdegrees, Dimension (imU));
     end for;
     COB := GL (d, K)!Matrix (newbas);
     COBi := COB^-1;


     /* find the semi-reduced versions of the *-simples */
     srcomps := < >;
     pos := 1;
     for i in [1..#star_simples] do
	  m := srdegrees[i];
	  U := star_simples[i];
          X := [ COB * U.j * COBi : j in [1..Ngens (U)] ];
          Y := [ ExtractBlock (X[j], pos, pos, m, m) : j in [1..#X] ];
          UU := sub < MatrixAlgebra (K, m) | Y >;
          UtoUU := hom < U -> UU | r :-> 
                      ExtractBlock (COB * r * COBi, pos, pos, m, m) >;
          UUtoU := hom < UU -> U | r :-> 
            COBi * InsertBlock (MatrixAlgebra (K, d)!0, r, pos, pos) * COB >;
          UU`Star := hom < UU -> UU | r :-> ((r @ UUtoU) @ U`Star) @ UtoUU >;
          UU`IsBasis := true;
          UU`StarAlgebraInfo := U`StarAlgebraInfo;
          Append (~srcomps, UU);
          pos +:= m;
     end for;
                      
     TAFT_data := rec < RF | isSemisimple := true,
                             jacobsonRadical := 
                                 sub < Generic (TAFT) | TAFT!0 >,
                             taftComplement := TAFT,
			     transitionMatrix := COB,
                             basicSimpleTypes := btypes,
                             srComponents := srcomps,
			     srDegrees := srdegrees,
                             isSimple := (#star_simples eq 1)
                      >;
                             
     TAFT`StarAlgebraInfo := TAFT_data;
                      
     ADJ_data := rec < RF | isSemisimple := (Dimension (RAD) eq 0),
                            jacobsonRadical := RAD,
                            taftComplement := TAFT,
			    transitionMatrix := COB,
                            basicSimpleTypes := btypes,
                            srComponents := srcomps,
			    srDegrees := srdegrees,
                            isSimple := (Dimension (RAD) eq 0) and 
			                    (#star_simples eq 1)
                     >;
                     
     ADJ`StarAlgebraInfo := ADJ_data;
                            
return ADJ;

end function;

              

/* The adjoint algebra of a single reflexive form */

AdjointsOfAForm := function (F, Auto) 
        
     d := Degree (Parent (F));
     k := BaseRing (Parent (F));
    
     /* determine the type of the reflexive form */
     if Auto ne 0 then
         type := "unitary";
     else 
         if (F + Transpose (F) eq 0) then
	    type := "symplectic";
         else
            type := IdentifyOrthogonalType (F);
         end if;
     end if;
      
     T := FrobeniusImage (TransformForm (F, type), Auto); 
     Ti := T^-1;
    
     STAN := SimpleStarAlgebra (type, d, k);
    
     ADJ := sub < Generic (STAN) | 
                   [ T * STAN.i * Ti : i in [1..Ngens (STAN)] ]>;
     ADJtoSTAN := hom < ADJ -> STAN | r :-> Ti * r * T >;
     STANtoADJ := hom < STAN -> ADJ | r :-> T * r * Ti >;
     ADJ`Star := hom < ADJ -> ADJ | 
                        r :-> ((r @ ADJtoSTAN) @ STAN`Star) @ STANtoADJ >;
                                                      
     RF_SAI := __RF_SETUP ("algebra");
                         
     RF_SSI := __RF_SETUP ("simple");
       
     SAI_data := rec < RF_SAI | >;
     SAI_data`isSimple := true;
     SAI_data`isSemisimple := true;
     SAI_data`jacobsonRadical := sub < ADJ | ADJ!0 >;
     SAI_data`taftComplement := ADJ;
SAI_data`transitionMatrix := Identity (Generic (ADJ));
SAI_data`alternatingRadical := [ ];
     SAI_data`srComponents := < ADJ >;
     SAI_data`srDegrees := [ Degree (ADJ) ];
     SAI_data`basicSimpleTypes := <"classical">;
     SAI_data`sharpGroupOrder := STAN`StarAlgebraInfo`sharpGroupOrder;
     SAI_data`sharpGroupGenerators := 
        [ STAN`StarAlgebraInfo`sharpGroupGenerators[i] @ STANtoADJ :
                i in [1..#STAN`StarAlgebraInfo`sharpGroupGenerators] ];
                                
     SSI_data := rec < RF_SSI | >;
     SSI_data`simpleParameters := < type , d , #k >;
     SSI_data`standardSimple := STAN;
     SSI_data`standardIsomorphism := ADJtoSTAN;
     SSI_data`standardInverse := STANtoADJ;
     SSI_data`sharpGroup := 
      sub < Generic (STAN`StarSimpleInfo`sharpGroup) | 
        [ STAN`StarSimpleInfo`sharpGroup.i @ STANtoADJ : 
           i in [1..Ngens (STAN`StarSimpleInfo`sharpGroup)] ] >;
     SSI_data`sharpGroupOrder := STAN`StarSimpleInfo`sharpGroupOrder;
                            
     ADJ`StarAlgebraInfo := SAI_data;
     ADJ`StarSimpleInfo := SSI_data;
                           
return ADJ;
end function;


/* The adjoint algebra of a general system of reflexive forms. */

intrinsic AdjointAlgebra (S::SeqEnum : Autos := [0 : i in [1..#S]]) 
                                                -> AlgMat
                             
  { The algebra of adjoints of a nondegenerate system of reflexive forms }


     require (#S gt 0): "argument is empty";

     require (#S eq #Autos): "argument and parameter have unequal length";

     n := #S;

     require forall { i : i in [1..n] | 
               Type (S[i]) eq AlgMatElt } :
        "elements of argument are not forms";
        
     require forall { i : i in [1..n] |
               Type (Autos[i]) eq RngIntElt } :
        "elements of parameter <Autos> are not integers";
     
     K := BaseRing (Parent (S[1]));
     
     require Type (K) eq FldFin : 
         "Base ring of argument is not a finite field";

     e := Degree (K);

     require forall {f : f in Autos | (f eq 0) or (e mod f) eq 0} :
         "parameter <Autos> is not a list of Frobenius exponents";

     /* reduce to the nondegenerate case */
     rad := &meet [ Nullspace (FrobeniusImage (S[i], Autos[i])) : 
                    i in [1..#S] ];
     require Dimension (rad) eq 0 : "argument is a degenerate system";


     /* deal with the trivial case */
     if #S eq 1 then
         return AdjointsOfAForm (S[1], Autos[1]);
     end if;
       
     /* prepare the system of forms and select appropriate method */
     nForms, nAutos, method, mtcf := PrepareSystem (S, Autos); 

     if (method eq "slope") then
  
         F := nForms[1];
         autF := nAutos[1];
         G := nForms[2];
         autG := nAutos[2]; 
         ADJ := __slope_adj (F, G, autF, autG);         

     elif (method eq "centraliser") then  
     
         ADJ := __centraliser_adj (nForms : auto := &* nAutos);  
    
     else   /* use the default method */
       
         ADJ := __default_adj (nForms); 
                                               
     end if;

     if not assigned (ADJ`StarAlgebraInfo`alternatingRadical) then

         k := BaseRing (ADJ);
         n := Degree (ADJ);
         RAD := ADJ`StarAlgebraInfo`jacobsonRadical;
         Rgens := [ (k.1)^f * RAD.i : f in [0..Degree (k) - 1],
                                      i in [1..Ngens (RAD)] ];

         if Dimension (RAD) eq 0 then

             ALT_RAD := [ ];

         else

             X := { Rgens[i] - Rgens[i] @ ADJ`Star : 
                                  i in [1..#Rgens] };
             X := [ a : a in X | a ne RAD!0 ];
             if (#X gt 0) then
                VXK := [ Vector (X[i]) : i in [1..#X] ];
                U := VectorSpace (PrimeField (k), n^2 * Degree (k));
                VXk := [ U!(&cat [Eltseq (VXK[i][j]) : j in [1..n^2]]) : 
                                                         i in [1..#VXK] ]; 
                positions := IdentifyBasis (VXk);
                ALT_RAD := [ X[i] : i in positions ];
             else
                ALT_RAD := [ ];
             end if;

         end if;

         ADJ`StarAlgebraInfo`alternatingRadical := ALT_RAD;

     end if;

     if assigned (mtcf) then
         ADJ`StarAlgebraInfo`mapToCorrectField := mtcf;
     end if;

return ADJ;

end intrinsic;
