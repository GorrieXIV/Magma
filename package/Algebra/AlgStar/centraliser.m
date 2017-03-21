freeze;

    /*--- Construct the algebra centralising a matrix ---*/

import "prelims.m": Collected;
 
/*
  File contains code to construct the algebra
  centralising a matrix. It is based on the account in:

  S.H. Murray, Conjugacy classes in maximal parabolic subgroups 
  of general linear groups, J. Algebra 233, 135-155 (2000).

  It seems like the eventual function "CentraliserOfMatrix"
  would be a useful intrinsic. Perhaps incorporated into the
  "Centraliser" function for matrix algebras for the case when
  the algebra being centralised is the enveloping algebra of a
  single matrix. We have not, however, made it an intrinsic
  of this package. 
*/   


__make_basis := function (r, s, A : Start := 0)

     d := Nrows (A);
     basis := [];
     Z := KMatrixSpace (BaseRing (Parent (A)), r * d, s * d)!0;

     if (r ge s) then
      
         for i in [1..s-Start] do 
            blocks := < A : j in [1..s-i-Start+1] >;
            X := DiagonalJoin (blocks);
            for j in [0..d-1] do
		  B := InsertBlock (Z, X^j, 1, (i - 1 + Start) * d + 1);
               Append (~basis, B);
            end for;  
   	 end for;

     else

         for i in [1..r-Start] do
            blocks := < A : j in [1..r-i-Start+1] >;
            X := DiagonalJoin (blocks);
            for j in [0..d-1] do
		  B := InsertBlock (Z, X^j, 1, 
                             (s - r) * d + (i - 1 + Start) * d + 1);
               Append (~basis, B);
            end for; 
         end for;

     end if;

return basis;
end function;


/*
   Given an irreducible polynomial <p> over a field <k>,
   and a <partition>, construct the generalised Jordan
   block determined by these parameters.
   The Jordan block has the form used by Murray, as
   opposed to the standard Magma form.
*/

__build_Murray_JF := function (p, partition)
     Cp := CompanionMatrix (p);
     s := #partition;
     m := &+ partition;
     k := BaseRing (Parent (p));
     d := Degree (p);
     IdBlock := Identity (MatrixAlgebra (k, d));
     MurrayJF := DiagonalJoin (< Cp : i in [1..m] >);
     mm := 1;      
     for i in [1..s] do
         mi := partition[i];
         for j in [1..mi - 1] do
	     InsertBlock (~MurrayJF, IdBlock, mm, mm + d);
             mm +:= d;
	 end for;
         mm +:= d;
     end for;
return MurrayJF;
end function;


/*
   Given a primary matrix <P>, return Murray's version of the
   generalized Jordan normal form of <P> and the partition
   associated with the invariant factors of <P>
*/

__primary_Murray_JF := function (P)

     k := BaseRing (Parent (P));

     // first conjugate <P> to Magma JNF
     J, D := JordanForm (P);

     mpol := MinimalPolynomial (J);
     mfac := Factorisation (mpol);

     if (#mfac gt 1) then
        error "<P> must be primary";
     end if;
  
     p := mfac[1][1];
     ifacs := InvariantFactors (J);
     partition := [ Factorisation (ifacs[i])[1][2] : 
                                      i in [1..#ifacs] ];

     if (Degree (p) gt 1) then   
       
	 /* build <MurrayJNF> for parameters given parameters */
         MurrayJF := __build_Murray_JF (p, partition);
         J, C := JordanForm (MurrayJF);
         D := C^-1 * D;
         
     else

         /* <MurrayJNF> agrees with Magma */       
         MurrayJF := J;
    
     end if;     
     
return MurrayJF, D, partition;
end function;


/* simple test for whether a list is weakly increasing */
__is_partition := function (part)
return forall { i : i in [1..#part-1] | part[i] le part[i+1] };
end function;


/* 
   given an irreducible polynomial <p> and a <partition>
   return a basis for the algebra centralising the
   associated generalized Jordan block

   the Jordan block is assumed to be in the form described in:

   S.H. Murray, Conjugacy classes in maximal parabolic subgroups
   of the general linear group, J. Algebra 233, 135--155 (2000)

   the basis of the centraliser algebra exhibits a natural 
   wedderburn decomposition
*/

__centraliser_of_primary_Murray_JF := function (p, partition)

     if (not IsIrreducible (p)) then
        error "polynomial must be irreducible";
     end if;
       
     if (not __is_partition (partition)) then
        error "partition must be weakly increasing";
     end if;
      
     coll_part := Collected (partition);
     t := #coll_part;
     
     d := Degree (p);
     n := (&+ partition) * d;
     k := BaseRing (Parent (p)); 
     BigZero := MatrixAlgebra (k, n)!0;

     /* two useful small block matrices */
     IdBlock := Identity (MatrixAlgebra (k, d));
     Cp := CompanionMatrix (p);
     

     /* first write down the semisimple part */
     SimpleBases := < >;
     start := 1;
     for i in [1..t] do
       
	 /* construct semisimple contribution of i-th block */

         fi := coll_part[i][1];
         entries := [ ];
         for l in [0..d-1] do
            blocks := < Cp^l : j in [1..fi] >;
            Append (~entries, DiagonalJoin (blocks));
         end for;
    
         ni := coll_part[i][2];

         SimpleBasis := [ ];
         for u in [1..ni] do
            for v in [1..ni] do
               for E in entries do
                  Append (~SimpleBasis,
                    InsertBlock (BigZero, E, 
                                   start + (u - 1) * d * fi, 
                                   start + (v - 1) * d * fi)
                         ); 
               end for;
            end for;
         end for;
           
         Append (~SimpleBases, SimpleBasis);
         
         start +:= ni * fi * d;
         
     end for;


     /* next write down the radical */
     RadicalBasis := [ ];

     /* begin with contribution of the diagonal blocks to radical */
     start := 1;
     for i in [1..t] do
       
         fi := coll_part[i][1];
         ni := coll_part[i][2];
         DiagRadBas := __make_basis (fi, fi, Cp : Start := 1);
         
         for u in [1..ni] do
            for v in [1..ni] do
              
               RadicalBasis cat:=
                  [ InsertBlock (
                      BigZero, DiagRadBas[r], start + (u-1) * d * fi,
                                              start + (v-1) * d * fi
                                ) : r in [1..#DiagRadBas] ];
            end for;
         end for;
         
         start +:= ni  * fi * d;
         
     end for;
       
       
     /* next contribution of non-diagonal blocks to radical */
     for i in [1..t] do

        for j in [1..i-1] cat [i+1..t] do
         
          fi := coll_part[i][1];
          ni := coll_part[i][2]; 
          fj := coll_part[j][1];
          nj := coll_part[j][2];
          
          posi := &+ ([0] cat [ &* coll_part[c] : c in [1..i-1] ]) * d + 1;
          posj := &+ ([0] cat [ &* coll_part[c] : c in [1..j-1] ]) * d + 1;
          RadBas := __make_basis (fi, fj, Cp);
          
          for u in [1..ni] do
             for v in [1..nj] do
         
                RadicalBasis cat:= 
                    [ InsertBlock (BigZero, RadBas[r], 
                          posi + (u - 1) * fi * d,
                          posj + (v - 1) * fj * d
                                  ) : r in [1..#RadBas] ];
             
             end for;
          end for;
            
        end for;
          
     end for;

return RadicalBasis, SimpleBases;
end function;


/*
   Given a matrix <T>, return the algebra <C> centralising <T>. 
   The output is specified by a basis that exhibits a 
   Wedderburn decomposition of <C>. 
*/

CentraliserOfMatrix := function (T) 

     k := BaseRing (Parent (T));
     n := Degree (Parent (T));
     
     mpol := MinimalPolynomial (T);
     mfac := Factorisation (mpol);
     
     PrimaryComponents := < >;
     PrimaryDimensions := [ ];
     for i in [1..#mfac] do
         g := mfac[i][1] ^ mfac[i][2];
         Xi := Evaluate (g, T);
         Vi := Nullspace (Xi);
         Append (~PrimaryComponents, Vi);
         Append (~PrimaryDimensions, Dimension (Vi));
     end for;
       
     PrimaryBasis := &cat [ Basis (PrimaryComponents[i]) :
                               i in [1..#mfac] ];
     COB := MatrixAlgebra (k, n)!Matrix (PrimaryBasis);
     T0 := COB * T * COB^-1;   
     /* 
       <T0> is in block diagonal form exhibiting the 
       decomposition of <V> into its <T>-primary components
     */        
     pos := 1;
     JB0 := [ ];
     SB0 := < >;
     BigZero := Parent (T)!0;

     for i in [1..#PrimaryDimensions] do

         ni := PrimaryDimensions[i];
         pi := mfac[i][1];
         Pi := ExtractBlock (T0, pos, pos, ni, ni);
         
         /* conjugate to Murray form and write down centraliser */        
         MJFi, Di, parti := __primary_Murray_JF (Pi);       
         JBi, SBi := __centraliser_of_primary_Murray_JF (pi, parti);

         /* conjugate back again */
         Ei := Di^-1;
         SBi := < [ Ei * SBi[r][j] * Di : j in [1..#SBi[r]] ] :
                           r in [1..#SBi] >;
         JBi := [ Ei * JBi[j] * Di : j in [1..#JBi] ];
         
         /* embed in big matrix */
         SBi := < [ InsertBlock (BigZero, SBi[r][j], pos, pos) :
                        j in [1..#SBi[r]] ] : r in [1..#SBi] >;
         JBi := [ InsertBlock (BigZero, JBi[j], pos, pos) :
                        j in [1..#JBi] ];

         for r in [1..#SBi] do
            Append (~SB0, SBi[r]);
         end for;

         JB0 cat:= JBi;
 
         /* update position */        
         pos +:= ni;
         
     end for;

     COBinv := COB^-1;
     JB := [ COBinv * JB0[j] * COB : j in [1..#JB0] ];
     
     Simples := < >;
     SB := [ ];
     for i in [1..#SB0] do
        SBi := [ COBinv * SB0[i][j] * COB : j in [1..#SB0[i]] ];
        SB cat:= SBi;
        Si := sub < Parent (T) | SBi >;  
        Append (~Simples, Si);
     end for;

     J := sub < Parent (T) | JB >;
     W := sub < Parent (T) | SB >;
     C := sub < Parent (T) | JB cat SB >;
     
     is_simple := (Dimension (J) eq 0) and (#Simples eq 1);
     

     /* record structural information */
     
     RF := recformat < isSimple , jacobsonRadical , simpleComponents , 
                       wedderburnComplement >;
                       
     data := rec < RF | 
                              isSimple := is_simple,
                       jacobsonRadical := J,
                  wedderburnComplement := W,
                      simpleComponents := Simples 
                 >;
     
     C`AlgebraInfo := data;

return C;
end function;

