freeze;

   /*--- file contains functions for handling reflexive forms ---*/


import "verify.m": IsIsometry, IsSimilarity;

import "prelims.m": EltseqWithBasis;


/*
   We assume here that: 
   <F> is (the matrix representing) a nondegenerate reflexive form; 
   <G> is any reflexive form on the same underlying space; 
   
   The output is a pair [ <f> , <S> ] encoding the semilinear
   slope of <F> and <G>.
*/

SlopeOfPair := function (F, G, autF, autG)

     S := FrobeniusImage (G * F^-1, autF);             
     
return AbsoluteValue (autF - autG), S;
end function;


__K_to_k := function (H, k, bas)

     d := Degree (Parent (H));
     K := BaseRing (Parent (H));
     e := Degree (K) div Degree (k);
     rho := bas[2];

     h := MatrixAlgebra (k, e*d)!0;
     for i in [1..d] do
         for j in [1..d] do
            for s in [1..e] do
               c := EltseqWithBasis (K, k, bas, rho^(s-1) * H[i][j]);
               for t in [1..e] do
	          h[e*(i-1)+s][e*(j-1)+t] := c[t];
	       end for;
	    end for;
	 end for;
     end for;

return h;
end function;



__k_to_K := function (h, K, bas)

     k := BaseRing (Parent (h));
     e := Degree (K) div Degree (k);
     d := Degree (Parent (h)) div e;
     rho := bas[2];

     H := MatrixAlgebra (K, d)!0;
     for i in [1..d] do
         for j in [1..d] do
	    H[i][j] := &+ [ h[e*(i-1)+1][e*(j-1)+t] * rho^(t-1) : 
                                                      t in [1..e] ]; 
	 end for;
     end for;

return H;
end function;


/* writes a <K>-reflexive form as a system over prescribed subfield */

__Kform_to_system := function (F, sigma, k, bas)
     K := BaseRing (Parent (F));
     rho := bas[2];
     d := Degree (Parent (F));
     e := Degree (K) div Degree (k);
     Phi := [ MatrixAlgebra (k, d*e)!0 : l in [1..e] ];
     for i in [1..d] do
         for j in [1..d] do
            for s in [1..e] do
               for t in [1..e] do

                  lambda := EltseqWithBasis (K, k, bas, 
                       Frobenius (rho^(s-1), sigma) * rho^(t-1) * F[i][j]);
                  for l in [1..e] do
                     Phi[l][e*(i-1)+s][e*(j-1)+t] := lambda[l];
                  end for;

               end for;
            end for;
         end for;
     end for;
return Phi;
end function;


/*
  Given a system <Sigma> of reflexive K-forms with associated field 
  automorphisms specified by the list <autos>, return an equivalent
  system of k-bilinear forms, where [K : k] = e. Return also a 
  k-linear embedding M_d(K) -> M_{ed}(k) and its inverse.
*/

SwitchFields := function (Sigma, autos, rho, k)

     K := BaseRing (Parent (Sigma[1]));
     d := Degree (Parent (Sigma[1]));
     f := Degree (K);
     e := f div Degree (k);
     bas := [ rho^(l-1) : l in [1..e] ];

     nSigma := &cat [ __Kform_to_system (Sigma[z], autos[z], k, bas) :
	 			    z in [1..#Sigma] ];

     K_to_k := hom < MatrixAlgebra (K, d) -> MatrixAlgebra (k, e*d) |
                                       H :-> __K_to_k (H, k, bas) >;

     k_to_K := hom < MatrixAlgebra (k, e*d) -> MatrixAlgebra (K, d) |
                                         h :-> __k_to_K (h, K, bas) >;

return nSigma, K_to_k, k_to_K;
end function;



/* Tries to find a nondegenerate form in the given system. */

__find_nondegenerate := function (Sigma, k : Limit := 20)

     n := #Sigma;
     U := VectorSpace (k, n);

     found := false;
     i := 1;
     while (not found) and (i lt Limit) do
         u := Random (U);
         F := &+ [ u[j] * Sigma[j] : j in [1..n] ];
         if Rank (F) eq Nrows (F) then
            found := true;
         end if;
         i +:= 1;
     end while;

     if (not found) then
         return Sigma;
     end if;

     assert exists (t){j : j in [1..n] | u[j] ne 0};

     nSigma := [ F ] cat [ Sigma[j] : j in [1..n] | j ne t ];

return nSigma;
end function;


/*
   A worker function which, if possible, returns an equivalent
   system whose first member is nondegenerate.

   If the system contains at least 3 forms of different basic
   types, then it will first replace the system with an
   equivalent system over a subfield that defining an 
   Hermitian bimap whose adjoints are naturally isomorphic
   to those of the original system.

   The function also returns a string that indicates which 
   method should be used to compute the adjoint algebra.
*/

PrepareSystem := function (Forms, Autos)

     assert #Forms gt 1;
     S := Set (Autos);

     K := BaseRing (Parent (Forms[1]));

     if (#Forms eq 2) then

	if (#S eq 1) then  

	   if (S eq {0}) then  

              nForms := __find_nondegenerate (Forms, K);
              if (Rank (nForms[1]) eq Nrows (nForms[1])) then
	         return nForms, Autos, "slope", _;
              else
	         return nForms, Autos, "default", _;
              end if;  
        
	   else

              e := Degree (K);
              assert e mod 2 eq 0;
              f := e div 2;
              rho := PrimitiveElement (K);
              k := sub < K | rho * Frobenius (rho, f) >; 
              nForms := __find_nondegenerate (Forms, k);
              if (Nrows (nForms[1]) eq Rank (nForms[1])) then
	         return nForms, Autos, "slope", _;
              else
	          /* 
                    2-space of degenerate Hermitian forms;
                    Adj will computed via default method, hence 
                    we need convert system to one over smaller field
	          */
                 xi := K.1;
                 e := Degree (K);
                 xiq := Frobenius (xi, e div 2);
                 k := sub < K | xi * xiq >;
                 rho := xi - xiq;
                 nForms, f, g := SwitchFields (Forms, Autos, rho, k); 
                 return nForms, [ 0 : i in [1..4] ], "default", g;
              end if;	   

           end if;

        else

  	   flag := exists (i){j : j in [1,2] | 
			 Rank (Forms[j]) eq Nrows (Forms[j])};
           if flag then 
              //"cross-type slope method: not yet implemented"; 
           end if;
           //uncomment following once semilinear centralisers are plugged in.
           /*
           if flag then
	   "cross-type slope method: not implemented yet";
              F := Sigma[i];
              return [ F ] cat [ Sigma[3-i] ], [ btypes[i] , btypes[3-i] ], 
                     "slope", _;
	   else
           */
	      /* here we have mixed types of degenerates */
               assert Degree (K) mod 2 eq 0;
               xi := K.1;
               e := Degree (K);
               xiq := Frobenius (xi, e div 2);
               k := sub < K | xi * xiq >;
               rho := xi - xiq;
               nForms, f, g := SwitchFields (Forms, Autos, rho, k); 
               return nForms, [ 0 : i in [1..4] ], "default", g;
           //end if;

	end if;

     else   /* <Forms> contains more than two forms */

	if S eq {0} then
  
           nForms := Forms;
           nAutos := Autos;         

        else
             
 	   /* we must convert to system over ground field */
           assert Degree (K) mod 2 eq 0;
           xi := K.1;
           e := Degree (K);
           xiq := Frobenius (xi, e div 2);
           k := sub < K | xi * xiq >;
           rho := xi - xiq;
           nForms, f, g := SwitchFields (Forms, Autos, rho, k);
           nAutos := [ 0 : i in [1..#nForms] ];

        end if;

        /* the forms in <nSigma> are now bilinear */
        n := #nForms;
        k := BaseRing (Parent (nForms[1]));

        nForms := __find_nondegenerate (nForms, k);
         
        if Rank (nForms[1]) eq Nrows (nForms[1]) then
	     if assigned (g) then
	        return nForms, nAutos, "centraliser", g;
	     else
                return nForms, nAutos, "centraliser", _;
             end if;
	else
	     if assigned (g) then
  	        return nForms, nAutos, "default", g;
	     else
                return nForms, nAutos, "default", _;
             end if;
        end if;
              
     end if;

end function;


/*
   This function was written original after correspondence
   with D. Holt to work around a bug in the Magma function
   TransformForm. Has that bug has been fixed now?
*/

__transform_form := function (form, d, q, type)
    E := BaseRing (Parent (form));
assert #E eq q;
    K := GF (q);
    Embed (K, E);
    Embed (E, K);
    M := MatrixAlgebra (K, d)!form;
    C := TransformForm (M, type);
return MatrixAlgebra (E, d)!C;
end function;


/* return the isometry type of the given symmetric form */
IdentifyOrthogonalType := function (F)
     if not (F eq Transpose (F)) then
         error ("input matrix is not symmetric");
     end if;  
     d := Nrows (F);
     k := BaseRing (Parent (F));
     if (d mod 2 eq 1) then
         C := __transform_form (F, d, #k, "orthogonalcircle");
         return "orthogonalcircle", C;
     else
         type := SymmetricBilinearFormType (F);
         C := __transform_form (F, d, #k, type); 
         return type, C;
     end if;
end function;



           /*--- intrinsic functions ---*/


/* Substitute for ClassicalForms when looking specifically for bilinear. */

BilinearForm := function (G)
     if not IsAbsolutelyIrreducible (G) then
         return false, _;
     end if;
     M := GModule (G);
     N := GModule (sub < Generic (G) | 
                    [ Transpose (G.i^-1) : i in [1..Ngens (G)] ] >);                 X := AHom (M, N);
     if Dimension (X) ne 1 then
         return false, _;
     end if;
     BX := Basis (X);
return true, MatrixAlgebra (BaseRing (G), Degree (G))!BX[1];
end function;


/* similarly */

SesquilinearForm := function (G) 
     e := Degree (BaseRing (G));
     if (e mod 2 eq 0) then
         f := e div 2;
     else
         return false, _;
     end if;
     if not IsAbsolutelyIrreducible (G) then
         return false, _;
     end if;
     M := GModule (sub < Generic (G) | 
                  [ FrobeniusImage (G.i, f) : i in [1..Ngens (G)] ] >);
     N := GModule (sub < Generic (G) | 
                       [ Transpose (G.i^-1) : i in [1..Ngens (G)] ] >);              X := AHom (M, N);
     if Dimension (X) ne 1 then
         return false, _;
     end if;
     BX := Basis (X);
return true, MatrixAlgebra (BaseRing (G), Degree (G))!BX[1];
end function;


StandardReflexiveForm := function (name, d, K)                                       assert d gt 0;
     if d eq 1 then
         assert (name eq "unitary" or name eq "orthogonalcircle");
         return Identity (MatrixAlgebra (K, d));
     end if;
     if (d eq 2) and (#K le 3) and (name eq "orthogonalplus") then
         return Identity (MatrixAlgebra (K, d));
     end if;
     if name eq "unitary" then
         assert Degree (K) mod 2 eq 0;
         e := Degree (K) div 2;
         G := GU (d, K);
         M := ClassicalForms (G)`sesquilinearForm;
         M := FrobeniusImage (M, e);
     else
        e := 0;
        if name eq "symplectic" then 
           assert d mod 2 eq 0;
           G := Sp (d, K); 
        elif name eq "orthogonalcircle" then
           assert d mod 2 eq 1;
           G := GO (d, K);
        elif name eq "orthogonalplus" then
           assert d mod 2 eq 0;
           G := GOPlus (d, K);
        else
           assert name eq "orthogonalminus";
           assert d mod 2 eq 0;
           G := GOMinus (d, K);
        end if;
        M := ClassicalForms (G)`bilinearForm;
     end if;
assert forall { i : i in [1..Ngens (G)] | IsIsometry (M, e, G.i) };       
return M;
end function;


                /*--- intrinsic functions ---*/


/*
   Return the group of all matrices satisfying g * M * g^t = M
   where <M> is a possibly degenerate form of specified <type>.
*/

__standard_isometry_group := function (name, d, k)
     if (name eq "symplectic") then
         G := Sp (d, k);
     elif (name eq "unitary") then
         e := Degree (k) div 2;
         H := GU (d, k);
         G := sub < Generic (H) | 
              [ FrobeniusImage (H.i, e) : i in [1..Ngens (H)] ] >;
         G`Order := Order (H);
     elif (name eq "orthogonalcircle") then
         G := GO (d, k);
     elif (name eq "orthogonalminus") then
         G := GOMinus (d, k);
     else
         G := GOPlus (d, k);
     end if;
return G;
end function;


intrinsic IsometryGroup (M::AlgMatElt : Auto := 0) -> GrpMat

   { The group of isometries of the (possibly degenerate) 
     reflexive form M. }
     
     k := BaseRing (Parent (M));
     require Type (k) eq FldFin : 
        "Base ring of argument 1 is not a finite field";

     require Auto in [0, Degree (k) div 2] :
        "parameter setting is not a legitimate Frobenius exponent";  

     r := Rank (M);
     d := Degree (Parent (M));
     if (r eq 0) then return GL (d, k); end if;

     /*
       conjugate into the form [ F 0 ]
                               [ 0 0 ]
     */
     N := Nullspace (FrobeniusImage (M, Auto));
     C := Complement (Generic (N), N);
     T1 := GL (d, k)!Matrix (Basis (C) cat Basis (N));
     M1 := T1 * M * Transpose (T1);
     F := ExtractBlock (M1, 1, 1, r, r);

     /* determine the type of <F> */
     if Auto ne 0 then
         type := "unitary";
     else 
         if (F + Transpose (F) eq 0) then
	    type := "symplectic";
         else
            type := IdentifyOrthogonalType (F);
         end if;
     end if;

     /*
       transform <F> to standard form and hence obtain
       generators for the conformal symplectic group of <F>
     */
     T2 := FrobeniusImage (TransformForm (F, type), Auto);
     iso := __standard_isometry_group (type, r, k);
     iso_gens := [ T2 * iso.i * T2^-1 : i in [1..Ngens (iso)] ];

     /* embed them back into a group of the correct degree */
     if (r lt d) then
         iso_gens := [ DiagonalJoin (iso_gens[i], Identity (GL (d-r, k))) :
                                     i in [1..#iso_gens] ];
     end if;

     /* build the generators of the general linear part */
     if (r lt d) then
        GLgens := [ DiagonalJoin (Identity (GL (r, k)), GL (d-r, k).i) :
                              i in [1..Ngens (GL (d-r, k))] ];
        ordgl := #GL (d-r, k);
     else
        GLgens := [ ];
        ordgl := 1;
     end if;

     gens := iso_gens cat GLgens;

     /* add a unipotent generator */
     if (r lt d) then
         X := Identity (MatrixAlgebra (k, d));
         X[1][r+1] := 1;
         Append (~gens, X);
     end if;

     /* conjugate back to original group */
     gens := [ T1^-1 * gens[i] * T1 : i in [1..#gens] ];

     assert forall{ i : i in [1..#gens] | IsIsometry (M, Auto, gens[i]) };
     
     ISOM := sub < GL (d, k) | [ GL (d, k)!gens[i] : i in [1..#gens] ] >;
     ord := #iso * ordgl * (#k)^(r*(d-r));
     
     RF := recformat < order , pCoreOrder , simpleTypes >;
     SI_data := rec < RF | order := ord,
                           pCoreOrder := (#k)^(r*(d-r)),
                           simpleTypes := [ < type, d, #k > ]
                     >;
                     
     ISOM`StructuralInformation := SI_data;

return ISOM;
end intrinsic;



/*
   Return the group of all matrices satisfying g * M * g^t = a * M
   where <M> is a possibly degenerate form of specified <name>.
*/

__standard_similarity_group := function (name, d, k)
     if (name eq "symplectic") then
         G := ConformalSymplecticGroup (d, k);
     elif (name eq "unitary") then
         G := ConformalUnitaryGroup (d, k);
     elif (name eq "orthogonalcircle") then
         G := ConformalOrthogonalGroup (d, k);
     elif (name eq "orthogonalminus") then
         G := ConformalOrthogonalGroup (-1, d, k);
     else
         G := ConformalOrthogonalGroup (1, d, k);
     end if;
return G;
end function;


intrinsic SimilarityGroup (M::AlgMatElt : Auto := 0) -> GrpMat

   { Given a matrix representing a reflexive form of known type, 
     return its group of similitudes.}
        
     k := BaseRing (Parent (M));
     require Type (k) eq FldFin : 
        "Base ring of argument 1 is not a finite field";

     require Auto in [0, Degree (k) div 2] :
        "parameter setting is not a legitimate Frobenius exponent";

     r := Rank (M); 
     d := Degree (Parent (M));
     if (r eq 0) then return GL (d, k); end if;

     /*
       conjugate into the form [ F 0 ]
                               [ 0 0 ]
     */
     N := Nullspace (FrobeniusImage (M, Auto));
     C := Complement (Generic (N), N);
     T1 := GL (d, k)!Matrix (Basis (C) cat Basis (N));
     M1 := T1 * M * Transpose (T1);
     F := ExtractBlock (M1, 1, 1, r, r);

     /* determine the type of <F> */
     if Auto ne 0 then
         type := "unitary";
     else 
         if (F + Transpose (F) eq 0) then
	    type := "symplectic";
         else
            type := IdentifyOrthogonalType (F);
         end if;
     end if;

     /*
       transform <F> to standard form and hence obtain
       generators for the conformal symplectic group of <F>
     */
     T2 := FrobeniusImage (TransformForm (F, type), Auto);
     sim := __standard_similarity_group (type, r, k);
     sim_gens := [ T2 * sim.i * T2^-1 : i in [1..Ngens (sim)] ];

     /* embed them back into a group of the correct degree */
     if (r lt d) then
         sim_gens := [ DiagonalJoin (sim_gens[i], Identity (GL (d-r, k))) :
                                     i in [1..#sim_gens] ];
     end if;

     /* build the generators of the general linear part */
     if (r lt d) then
        GLgens := [ DiagonalJoin (Identity (GL (r, k)), GL (d-r, k).i) :
                              i in [1..Ngens (GL (d-r, k))] ];
     else
        GLgens := [ ];
     end if;

     gens := sim_gens cat GLgens;

     /* add a unipotent generator */
     if (r lt d) then
         X := Identity (MatrixAlgebra (k, d));
         X[1][r+1] := 1;
         Append (~gens, X);
     end if;

     /* conjugate back to original group */
     gens := [ T1^-1 * gens[i] * T1 : i in [1..#gens] ];

     /* temporary sanity check */
     assert forall { i : i in [1..#gens] | IsSimilarity (M, Auto, gens[i]) };

     SIM := sub < GL (d, k) | [ GL (d, k)!gens[i] : i in [1..#gens] ] >;
     //order := #sim * #GL (d-r, k) * (#k)^(r*(d-r)); 
     //SIM`Order := order;

return SIM;
end intrinsic;



   /*--- constructors for systems of forms from p-group ---*/


intrinsic PGroupToForms (P::GrpPC) -> SeqEnum

   { The system of forms determined up to 
     isometry by the p-group P. }

     if IsAbelian (P) then return [ ]; end if;

     ord := FactoredOrder (P);
     require #ord eq 1 : "argument is not a p-group";
     p := ord[1][1];
   
     gamma := LowerCentralSeries (P);
     require #gamma[#gamma] eq 1 : "argument is not nilpotent.";

     zeta := UpperCentralSeries (P);
     phi := FrattiniSubgroup (P);

     N := sub < P | [ zeta[#zeta - 1], phi ] >;
     V, f := quo < P | N >;
     d := Ngens (V);
     W, h := quo < gamma[2] | gamma[3] >;
     U, g := ElementaryAbelianQuotient (W, p);
     e := Ngens (U);

     Forms := [ MatrixAlgebra (GF (p), d)!0 : i in [1..e] ];
     
     for i in [1..d] do
         for j in [1..d] do

            vecij := Eltseq ( ( (V.i @@ f, V.j @@ f) @ h ) @ g ); 
            for s in [1..e] do
               Forms[s][i][j] := vecij[s];
            end for;

         end for;
     end for;

return Forms;

end intrinsic;


intrinsic PGroupToForms (P::GrpMat) -> SeqEnum

   { The system of forms determined up to isometry by the 
     matrix p-group P of nilpotency class 2. }

     if IsAbelian (P) then return [ ]; end if;

     d := Ngens (P);
     gens := [ (P.i, P.j) : i in [1..d], j in [1..d] ];

     DP := sub < Generic (P) | gens >;
     require IsElementaryAbelian (DP) : 
                 "argument is not a class 2 p-group";
     p := Order (DP.1);

     U, g := AbelianGroup (DP);
     e := Ngens (U);

     Forms := [ MatrixAlgebra (GF (p), d)!0 : i in [1..e] ];

     for i in [1..d] do
         for j in [1..d] do

             vecij := Eltseq ( (P.i, P.j) @ g );
             for s in [1..e] do
	        Forms[s][i][j] := vecij[s];
             end for;

         end for;
     end for;

     /* remove the radical */
     N := &meet [ Nullspace (F) : F in Forms ];
     n := Dimension (N);
     if (n gt 0) then
         V := VectorSpace (GF (p), d);
         C := Complement (V, N);
         X := GL (d, GF (p))!Matrix (Basis (C) cat Basis (N));
         XForms := [ X * Forms[i] * Transpose (X) : i in [1..e] ];
         Forms := [ ExtractBlock (XForms[i], 1, 1, d-n, d-n) : 
                                                     i in [1..e] ];
     end if;

return Forms;

end intrinsic;

