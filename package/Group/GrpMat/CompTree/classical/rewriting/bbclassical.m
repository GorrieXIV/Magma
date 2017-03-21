freeze;

// the main ingredients of ClassicalRewrite are the functions
// ClearFirstRow, ClearFirstColumn, SmallerMatrix, SmallerMatrixToSLP,
// DiagonalElementToSLP. These are implemented separately for the 
// different types of classical groups in the black-box and in the 
// char p context.

import "natural.m":ClassicalElementToSLP;

import "selection.m":ClearFirstRow;

import "elements.m":X_, RootElementsOfOmega, X12_, Xr2_,
  ConjugateClassicalStandardToClassicalNatural;

import "smallermatrix.m": SmallerMatrix, SmallerMatrixToSLP,
  ClassicalStandardForm;

import "diagonal.m":DiagonalElementToSLP;

// we define a record format to store the invariant of classical groups
bbclassicalattributesrf := recformat< Type : MonStgElt, 
                                   Dimension : RngIntElt,
                                   Field : FldFin >;

// the attribute StabilizerOfE1 holds the stabilizer of e1
AddAttribute( Grp, "StabilizerOfE1" );
AddAttribute( Grp, "StabilizerOfE1Transpose" );

AddAttribute( Grp, "IsBlackBoxClassicalGroup" );
AddAttribute( Grp, "AttributesOfBlackBoxClassicalGroup" );
AddAttribute( Grp, "StandardGenerators" );
AddAttribute( Grp, "BBGenerators" );
AddAttribute( Grp, "BBInverseGenerators" );
AddAttribute( Grp, "BBGroup" );
AddAttribute( Grp, "ClassicalStandardGenerators" );

AddAttribute( Grp, "Xin" );
AddAttribute( Grp, "RootElements" );
AddAttribute( Grp, "RootElementsTranspose" );
AddAttribute( Grp, "SiegTrans" );
AddAttribute( Grp, "SiegTransTranspose" );

AddAttribute( Grp, "ConjugatingElementToInternalForm" );

declare verbose ClassicalRewrite, 2;


B := SLPGroup( 11 );

BBStandardGenerators := function( G )
    
    return G`StandardGenerators;
end function;

BBGenerators := function( G )
    
    return G`BBGenerators;
end function;

BBInverseGenerators := function( G )
  
  return G`BBInverseGenerators;
end function;

BBDimension := function( G ) 
    
    return G`AttributesOfBlackBoxClassicalGroup`Dimension;
end function;

BBField := function( G ) 
  
  return G`AttributesOfBlackBoxClassicalGroup`Field;
end function;


BBType := function( G ) 
  
  return G`AttributesOfBlackBoxClassicalGroup`Type;
end function;
    
IsBlackBoxClassicalGroup := function( G ) 
                      
       return assigned G`IsBlackBoxClassicalGroup and 
       G`IsBlackBoxClassicalGroup;
end function;
    
IsBlackBoxClassicalGroupWithParameters := function ( G, gens, type, dim, q ) 
                    
    q1 := case< type | "SU": q^2, default: q >;                     
    
    return assigned G`IsBlackBoxClassicalGroup and 
           G`IsBlackBoxClassicalGroup and
           G`ClassicalStandardGenerators eq gens and 
           BBType( G ) eq type and 
           BBDimension( G ) eq dim and 
           BBField( G ) eq GF( q1 );
    
end function;

BBGroup := function( G ) 

  return G`BBGroup;
end function;

Evaluate2 := function( slp, list )
  
    for i in [1..#Generators( Parent( slp ))-#list] do
            Append( ~list, list[1]^0 );
    end for;
    
    return Evaluate( slp, list );
end function;


BlackBoxClassicalGroup := procedure( ~G, gens, type, dim, q  ) 

  if IsBlackBoxClassicalGroupWithParameters( G, gens, type, dim, q ) then
    return;
  end if; 

  if type eq "SU" then
      qq := q^2;  
  else
      qq := q;
  end if;
  
  stgens := gens;

  if type eq "SL" then
      
      bbgens := [ B.1^B.2, B.2^-1, B.3^(B.1^-1*B.2), B.4, B.1, 
                  B.3, One( B ), One( B ), One( B ), One( B ), One( B )];
      bbgensinv := [ B.5, B.2^-1, B.6, B.4 ];
      newgens := [ Evaluate2( x, gens ) : x in bbgens ];
      gens := newgens;
      bbgroup := SLPGroup( 4 );

  elif type eq "Sp" then
        
      bbgens := [ B.1, B.2, B.3, B.4, B.5, ((B.6^B.2^2)^B.1)^-1,
                  (((B.6^B.2^2)^B.1)^-1)^(B.1^B.2), One( B ), One( B ),
                  B.4, One( B ) ];
      bbgensinv := [ B.1, B.2, B.3, B.4, B.5, (B.6^(B.1^-1*B.2^-2))^-1 ];
      newgens := [ Evaluate2( x, gens ) : x in bbgens ];
      gens := newgens; 
      bbgroup := SLPGroup( 6 );
        
    elif type eq "SU" and IsEven( dim ) then
        
        /* the output of ClassicalStandardGenerators contains
          a different root element to the one we usually use
          we append T_{f_1,e_2} as it is more convenient for
          our procedures.    */
          
        bbgens := [ B.1, B.2, B.3, B.7^B.2^2, B.5, B.6^B.2^2, 
                    (B.6^B.2^2)^(B.1^B.2), One( B ), One( B ), B.4, One( B )];
        bbgensinv := [ B.1, B.2, B.3, B.10,B.5,B.6^B.2^-2,B.4^B.2^-2 ];
        newgens := [ Evaluate2( x, gens ) : x in bbgens ];  
        gens := newgens;
        bbgroup := SLPGroup( 7 );
        
    elif type eq "SU" and IsOdd( dim )  then
        
       /* the output of ClassicalStandardGenerators contains
          a different root element to the one we usually use
          we append T_{f_1,w}(-1/2) as it is more convenient for
          our procedures.    */
        
        w := X_( type, dim, q );
        bbgens := [ B.1, B.2, B.3, B.7^B.2, B.5, w,
                    w^(B.1^B.2), B.6^B.2, One( B ), B.4, One( B ) ];
        bbgensinv := [ B.1, B.2, B.3, B.10, B.5, B.8^B.2^-1, B.4^B.2^-1 ];
        newgens := [ Evaluate2( x, gens ) : x in bbgens ];  
        gens := newgens;
        bbgroup := SLPGroup( 7 );

    elif type eq "Omega+" then

        bbgens := [ B.1, B.8, One( B ), B.3, B.4, B.5,
		     B.2, One( B ), One( B ), B.6*B.3, One( B )];
        bbgensinv := [ B.1, B.7, B.4, B.5, B.6, B.10*B.4^-1, 
                       One( B ), B.2 ];
        newgens := [ Evaluate2( x, gens ) : x in bbgens ];
        gens := newgens;
        bbgroup := SLPGroup( 8 );
        
    elif type eq "Omega" then
        
        w1, w2 := RootElementsOfOmega( type, dim, q );
        _, p := IsPrimePower( q );
    
        if dim mod 4 eq 1 then
            l1 := Integers()!( GF(p)!(-1/2));
            l2 := -2;
        else
            l1 := Integers()!( GF(p)!(1/2));
            l2 := 2;
        end if; 
        
        bbgens := [ B.1^B.4, B.4, One( B ), B.3^B.4, B.5, 
                    w1, w2, (B.2^B.4)^l1, One( B ), B.3^B.4, One( B )];
        bbgensinv := [ B.1^B.2^-1,(B.8^l2)^B.2^-1,B.4^B.2^-1,B.2,B.5 ];
        newgens := [ Evaluate2( x, gens ) : x in bbgens ];
        gens := newgens;  
        bbgroup := SLPGroup( 5 );
        
    elif type eq "Omega-" and IsEven( q ) then
        
        w1, w2 := X12_( type, dim, q );
        w3 := Xr2_( dim, q );
        exp := case< dim mod 4 | 0: 1, 2: -1, default: false >;
        bbgens := [ (B.1*B.2)^B.5, B.5, One( B ), (B.3^B.5),
                    B.4, w1, w2, (B.1^B.5)^exp, 
                    w3, (B.3^B.5)^(q+1), B.3 ];
        bbgensinv := [ (B.8^-exp)^(B.2^-1), (B.8^exp)^(B.2^-1)*B.1^(B.2^-1),
                       B.4^(B.2^-1),B.5,B.2];
        newgens := [ Evaluate2( x, gens ) : x in bbgens ];
        gens := newgens;   
        bbgroup := SLPGroup( 5 );
           
    elif type eq "Omega-" then
        
        w1, w2 := X12_( type, dim, q );
        w3 := Xr2_( dim, q );
        exp := case< dim mod 4 | 0: 1, 2: -1, default: false >;
        bbgens := [ B.1^B.5, B.5, One( B ), (B.3^B.5),
                    B.4, w1, w2, (B.2^B.5)^exp, 
                            w3, (B.3^B.5)^(q+1), B.3 ];
        bbgensinv := [ B.1^B.2^-1, (B.8^exp)^B.2^-1, 
                       B.11, B.5, B.2 ];
        newgens := [ Evaluate2( x, gens ) : x in bbgens ];
        gens := newgens;  
        bbgroup := SLPGroup( 5 );
        
    end if;

    if assigned G`SiegTrans then delete G`SiegTrans; end if; 
    if assigned G`SiegTransTranspose then delete G`SiegTransTranspose; end if;
    if assigned G`StabilizerOfE1Transpose then 
        delete G`StabilizerOfE1Transpose; end if;
    if assigned G`StabilizerOfE1 then delete G`StabilizerOfE1; end if;
    if assigned G`Xin then delete G`Xin; end if;
    if assigned G`RootElements then delete G`RootElements; end if;
    if assigned G`RootElementsTranspose then 
        delete G`RootElementsTranspose; end if;
    
    G`StandardGenerators := gens;
    G`BBGenerators := bbgens;
    G`BBInverseGenerators := bbgensinv;
    G`BBGroup := bbgroup;
    G`ClassicalStandardGenerators := stgens;
    
    G`AttributesOfBlackBoxClassicalGroup := rec< bbclassicalattributesrf | 
                                                 Type := type, 
                                                 Dimension := dim, 
                                                 Field := GF( qq ) >;
       
    G`IsBlackBoxClassicalGroup := true;
end procedure;
          

intrinsic ClassicalRewriteNatural( G::GrpMat[FldFin], type::MonStgElt, 
        tr::GrpMatElt[FldFin], g::GrpElt :
	CheckResult := false,
	CheckMembership := true )
                       -> BoolElt, GrpElt 
 { For g in GL( n, q ), the function tests the membership of g in the subgroup generated by ClassicalStandardGenerators( type, dim, q )^tr and writes g as an SLP in these generators. The string type must be equal to one of SL, Sp, SU, Omega, Omega+, Omega-. (CS)}

    require type in { "SL", "Sp", "SU", "Omega+", "Omega-", "Omega" }: 
    "Argument 1 should be a classical type";

     dim := Dimension( G );
     F := CoefficientRing( G );
     gl := GL( dim, F );
     q := #F; q0 := case< type | "SU": Round( Sqrt( q )), default: q >;
       
     // check membership in classical group first
       
     if CheckMembership then
         g0 := tr*MatrixAlgebra( F, dim )!g*tr^-1;
         if Determinant( g0 ) ne 1 then 
             return false, false; 
         end if;
         
         mat := ClassicalStandardForm( type, dim, #F ); 
                        
             if type eq "SU" then
             g01 := Transpose( MatrixAlgebra( F, dim )!
                            [ x^q0 : x in Eltseq( g0 )]);
             
         else
             
             g01 := Transpose( g0 );
             
         end if;
         
         newmat := g0*mat*g01; 
         
         if type in { "Sp", "SU" } and newmat ne mat then 
             return false, false;
         elif type in { "Omega", "Omega+", "Omega-" } then
             
             if mat + Transpose( mat ) ne newmat + Transpose( newmat ) then
                 return false, false;
             end if;
                            
             if Characteristic( F ) ne 2 and SpinorNorm( gl!g0, mat ) ne 0 then
                 return false, false;
             end if;
             
         end if;
         
     end if;


     gens := ClassicalStandardGenerators( type, dim, q0 );
     BlackBoxClassicalGroup( ~G, gens^tr, type, dim, q0 );

     // conj will conjugate the group G into the internal form used
     // by ClassicalElementToSLP
     conj := ConjugateClassicalStandardToClassicalNatural( type,
                     dim, q );
     
     G`ConjugatingElementToInternalForm := tr^-1*conj;

     w := ClassicalElementToSLP( G, type, dim, q, g :
				 CheckResult := CheckResult );
     if CheckMembership then
        return true, w;
     else
        return w;
     end if;
     
end intrinsic;       

intrinsic ClassicalRewriteNatural( type::MonStgElt, 
        tr::GrpMatElt[FldFin], g::GrpElt :
        CheckResult := false, 
        CheckMembership := true )  -> BoolElt, GrpElt 
 { For g in GL( n, q ), the function tests the membership of g in the subgroup generated by ClassicalStandardGenerators( type, dim, q )^tr and writes g as an SLP in these generators. The string type must be equal to one of SL, Sp, SU, Omega, Omega+, Omega-. (CS)}

    require type in { "SL", "Sp", "SU", "Omega+", "Omega-", "Omega" }: 
    "Argument 1 should be a classical type";

     gl := Parent( g ); 
     dim := Dimension( gl );
     F := CoefficientRing( gl );
     q := #F; q0 := case< type | "SU": Round( Sqrt( q )), default: q >;
     gens := ClassicalStandardGenerators( type, dim, q0 )^tr;
     G := sub< Universe( gens ) | gens >;
          
     return ClassicalRewriteNatural( G, type, tr, g : 
                    CheckResult := CheckResult, 
                    CheckMembership := CheckMembership );
end intrinsic;
 
intrinsic ClassicalRewrite( G::Grp, gens::SeqEnum, 
        type::MonStgElt, dim::RngIntElt, q::RngIntElt, g::GrpElt : 
        Method := "choose" ) -> BoolElt, GrpElt
  { Write the element g as an SLP in the standard generators <gens> of G, 
 which must be isomorphic to a classical group defined by the arguments <type>, <dim> and q.  The string <type> is one of SL, Sp, SU, Omega, Omega+, Omega- (CS). }

    require type in { "SL", "Sp", "SU", "Omega+", "Omega-", "Omega" }: 
    "Argument 3 should be a classical type";
    
    requirege dim, 2;
    requirege q, 2;
    require IsPrimePower( q ): "the field size should be a prime-power";
    
    mem := GetMaximumMemoryUsage();
    q2 := case< type | "SU": q^2, default: q >;
     
    /* 
      choosing method
    */
      
    if Method eq "choose" then 

        if Category( G ) eq GrpMat and 
           #CoefficientRing( G ) eq q2  and Dimension( G ) eq dim 
           and gens eq ClassicalStandardGenerators( type, dim, q ) 
           and < type, IsEven( q )> ne < "Omega", true > then
            v, p := ClassicalRewriteNatural( G, type, g^0, g );
            return v, p;
            
        elif Category( G ) eq GrpMat and 
          Characteristic( CoefficientRing( G )) eq
          PrimeBasis( q )[1] and IsAbsolutelyIrreducible( G ) then
            
            Method := "CharP";
            
        else
            
            Method := "BB";
            
        end if;
        
    end if;

    /* if Method eq "BB" and type in { "Omega+", "Omega-", "Omega" } then
       error "Black-box methods are not implemented for orthogonal groups";
    end if;
    */
    
    BlackBoxClassicalGroup( ~G, gens, type, dim, q );  
        
    /* 
       Is some cases we use the existing isomorphisms between
       the classical groups.
    */
      
    // Sp( 2,q ) equal to SL( 2, q )
      
    if type eq "Sp" and dim eq 2 then
           
         newgens := [ gens[1], gens[1], gens[3], gens[4]]; 
         newG := sub< Universe( gens ) | newgens >;
         
         v, p := ClassicalRewrite( newG, newgens, "SL", 
                         2, q, g : Method := Method );

         if not Category( p ) eq BoolElt then
             BB := BBGroup( G );
             return v, Evaluate2( p, [ BB.1, BB.1, BB.3, BB.4]);
         else
             return v, p;
         end if;
         
     // SU( 2, q ) isom SL( 2, q )    
         
     elif type eq "SU" and dim eq 2 then
         
         newgens := [ gens[1], gens[1], gens[3], gens[4]];
         newG := sub< Universe( gens ) | newgens >;
         v, p := ClassicalRewrite( newG, newgens, "SL", 
                         2, q, g );
         if not Category( p ) eq BoolElt then
             BB := BBGroup( G );
             return v, Evaluate2( p, [ BB.1, BB.1, BB.3, BB.4]);
         else
             return v, p;
         end if;  
     
     // Omega( 3, q ) isom SL( 2, q )
       
     elif type eq "Omega" and dim eq 3 and Method eq "BB" then
         
         newgens := [ gens[1], gens[1], gens[2], gens[3]];
         newG := sub< Universe( gens ) | newgens >;
         v, p := ClassicalRewrite( newG, newgens, "SL", 
                         2, q, g );
         if not Category( p ) eq BoolElt then
             BB := BBGroup( G );
             return v, Evaluate2( p, [ BB.1, BB.1, BB.2, BB.3]);
         else
             return v, p;
         end if;  
         
     //    Omega-(4,q) isom SL(2,q^2)
           
     elif type eq "Omega-" and dim eq 4 and IsOdd( q ) and Method eq "BB" then
         
         newgens := [ gens[1], gens[1], gens[2], gens[3]];
         newG := sub< Universe( gens ) | newgens >;
         v, p := ClassicalRewrite( newG, newgens, "SL", 
                             2, q^2, g );
         if not Category( p ) eq BoolElt then
             BB := BBGroup( G );
             return v, Evaluate2( p, [ BB.1, BB.1, BB.2, BB.3]);
         else
             return v, p;
         end if;  
         
     elif type eq "Omega-" and dim eq 4 and IsEven( q ) and Method eq "BB" then
         
         newgens := [ gens[2]*gens[1]*gens[2], gens[2]*gens[1]*gens[2], 
                      gens[1], gens[3]];

         newG := sub< Universe( gens ) | newgens >;
         v, p := ClassicalRewrite( newG, newgens, "SL", 
                             2, q^2, g );
         if not Category( p ) eq BoolElt then
             BB := BBGroup( G );
             return v, Evaluate2( p, [ BB.2*BB.1*BB.2, BB.2*BB.1*BB.2, 
                            BB.1, BB.3]);
         else
             return v, p;
         end if;  
         
         // Omega+(4,q) isom SL(2,q) Y SL(2,q)
           
     elif type eq "Omega+" and dim eq 4 and Method eq "BB" then
             
             
          newgens1 := [ gens[4], gens[4], gens[5], gens[6]];
          newgens2 := [ gens[1], gens[1], gens[2], gens[3]];
          newG1 := sub< Universe( gens ) | newgens1 >;
          newG2 := sub< Universe( gens ) | newgens2 >;
          
          v1, p1 := ClassicalRewrite( newG1, newgens1, "SL", 2, q, g );
          if Category( p1 ) eq BoolElt then
              return v1, p1;
          end if;
          
          g1 := Evaluate( p1, newgens1 );
          
          v2, p2 := ClassicalRewrite( newG2, newgens2, "SL", 2, q, g1*g^-1 );
          if Category( p2 ) eq BoolElt then
              return v2, p2;
          end if;
          
                    
          BB := BBGroup( G );
          
          p1 := Evaluate2( p1, [BB.4, BB.4, BB.5, BB.6 ] );
          p2 := Evaluate2( p2, [BB.1, BB.1, BB.2, BB.3 ] );
          
          return v2, p1*p2^-1;
             
     end if;
              
   /* 
       First we need to decorate G with some attributes that describe
       it as a classical group                        
    */
      

    type := BBType( G );
    gens := BBStandardGenerators( G );

    /* 
      The following function executes the rewriting procedure. 
      The procedure has 5 main steps. Let g be in element in the black-box
      group G isomorphic to SX(n,q). Then in the first step we 
      find elements xl and xr such that xl*g*xr has e_1-row [1,0,...,0]. 
      Then we replace g by  xl*g*xr and we find such elements
      such that the e_1 row and the e_1-column of xl*g*xr are [1,...,0]. 
      We replace g by  xl*g*xr and this element
      is considered as an element of the black-box group isomorphic to 
      SL(n-1,q) or SX(n-2,q) modulo the (e_1,e_1) entry. 
      The third step recovers
      this element as an explicit element of SX(n-[1,2],q) 
      and in the fourth step we write this element as an SLP in the standard
      generators of SX(n-[1,2],q) using the implementation for the 
      natural representation.
        
      After doing these reductions, we obtain an 
      element which corresponds to a
      diagonal matrix and we write such an element as an SLP in the last 
      step. 
    */
        
   if type eq "Omega+" then
       S1 := gens[1]*gens[5]; progS1 := B.1*B.5;        
   else
       S1 := gens[1]; progS1 := B.1;
   end if;

   pr1l, pr1r, xl, xr := ClearFirstRow( G, g : 
                                 Method := Method, 
                                 FirstCall := true ); 

   if Category( pr1l ) eq BoolElt then return false, false; end if;
   g := xl*g*xr;

   if type eq "SL" then

       pr2l, pr2r, el1, el2 := ClearFirstRow( G, g : Method := Method, 
                                       Transpose := true );
       if Category( pr2l ) eq BoolElt then return false, false; end if;
       g := el1*g*el2; 
       
   else
       
       g := g^S1; 
       pr2l, pr2r, el1, el2 := ClearFirstRow( G, g : Method := Method );
       if Category( pr2l ) eq BoolElt then return false, false; end if;
       pr2l := pr2l*progS1^-1; pr2r := progS1*pr2r;
       g := el1*g*el2; 

   end if;

   mat := SmallerMatrix( G, g : Method := Method );
   if Category( mat ) eq BoolElt then return false, false; end if;

   pr3, pr4, el := SmallerMatrixToSLP( G, g, mat ); 
   if Category( pr3 ) eq BoolElt then return false, false; end if;
   g := el*g*Evaluate2( pr3, gens )^-1;

   pr5, el := DiagonalElementToSLP( G, g : Method := Method );
   if Category( pr5 ) eq BoolElt then return false, false; end if;

   g := g*el; 
   p := pr1l^-1*pr2l^-1*pr4^-1*pr5^-1*pr3*pr2r^-1*pr1r^-1;
   
   p := Evaluate2( p, BBGenerators( G ));
   bbgroup := BBGroup( G );
   p := Evaluate2( p, [ bbgroup.i : i in [1..#Generators( bbgroup )]]);
                
   vprint ClassicalRewrite, 1: "ClassicalRewrite finished... memory used: ",
                GetMaximumMemoryUsage() - mem;
                
   return g eq One( G ), p;
end intrinsic;

