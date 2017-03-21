freeze;

/* 
  This file contains the functions that are specific to the CharP case
  of the rewriting process.
*/

import "MatrixPGroup.m":MatrixPGroupWordInGen;
import "bbclassical.m":B, Evaluate2, BBType, BBField, BBStandardGenerators, 
BBDimension, BBGenerators;
import "unipotent.m":UnipotentStabiliser;
import "subgroups.m":SLPToSiegelTrans, StabilizerOfE1;
import "elements.m": ConjugateClassicalStandardToMyBasis, RootElements;


/*
  This is the first step of the rewriting process. The is an element
  g in G. The output is x such that gx stabilizes <e1>.
  
  The optional parameters are
  
  FirstCall: The function is called twice at the beginning of the 
  rewriting process. First to clear the first row and then
  to clear the first column. FirstCall is true in the first call.
      
  Transpose: In the SL case we need somewhat different methods to 
  clear the first column. This parameter is used in this case.  
*/
   
ClearFirstRowCharP := function( G, g : FirstCall := false, Transpose := false )
      
    gens := BBStandardGenerators( G );
    dim := BBDimension( G );
    type := BBType( G );
    V := gens[2]; 

    H := StabilizerOfE1( G : Transpose := Transpose );
    pgens, _, P := SLPToSiegelTrans( G : Transpose := Transpose,
                        EvaluateSLPs := true  );
    M := GModule( H );
    U := MinimalSubmodule( M );
          
    /* 
      H is a maximal parabolic. Since it has a normal p-subgroup, it is
      reducible, and hence U neq 0. Then PSubgroup is usually transitive
      on the H-orbit of U. Thus there is an element p in PSubgroup
      such that Ug=Up. Then gp^-1 will be in the stabilizer of U which
      is H. Hence gp^-1 stabilizes <e1>.
    */  

    W := VectorSpace( CoefficientRing( G ), Degree( G ));
    U := sub<  W | [ W!(M!x) : x in Basis( U )]>;
      
    /*
      Unipotent stabilizer is used to find p.
    */

    _, C, x, w := UnipotentStabiliser( P, U^g : ComputeBase := false ); 
    _, C1, x1, w1 := UnipotentStabiliser( P, U : ComputeBase := false );
    /* 
      The procedure stops here if g[e1,e1] ne 0. This is tested by 
      checking if C eq C1. This is always the case
      for instance in the second call. Otherwise g needs to be modified
      until g[e1,e1] ne 0.                            
    */  
                                  
    if C ne C1 then                              
       up := dim/2;
       pS1 := case< type | "SL": One( B ), default: B.1 >;
       S1 := Evaluate( pS1, gens );

       c := 0;
       while C ne C1 do
           c := c+1;
           if c gt dim+1 then 
               return false, false, false, false;
           end if;
           
           if c le up then
               g1 := g*V^c;
           else
               g1 := g*V^c*S1;
           end if;
           
           St, C, x, w := UnipotentStabiliser( P, U^g1 : 
                                  ComputeBase := false );
            
       end while;

       if c le up then
           prog := B.2^c;
           el := V^c;
       else
           prog := B.2^c*pS1;
           el := V^c*S1;
       end if;
       
    else
        
        prog := One( B ); el := One( G );
        
    end if;
    
    p := Evaluate2( w*w1^-1, pgens );
    
    return One( B ), prog*p, One( G ), el*x*x1^-1;
end function;
    

/* 
  The following function writes an element of the form
  
  e1 -> a1 e1 + a2 e2 + ... + 
  e2 -> e2 + c1 f1
  ...
  
  as an slp in the standard generators. In addition, it determines
  the coefficients a1, a2, etc.
*/

    
EntriesOfRootElementCharP := function( G, g : GetWE1Entry := true )
    
    gens := BBStandardGenerators( G );
    dim := BBDimension( G );
    type := BBType( G );
    F := BBField( G ); q := #F;
            
    genspslp, _, P := SLPToSiegelTrans( G : EvaluateSLPs := true );
    p := MatrixPGroupWordInGen( g, P : ComputeBase := false );
    p := Evaluate2( p, genspslp );
    p := Evaluate( p, BBGenerators( G ));
    
    q0 := case< type | "SU": Round( Sqrt( #F )), default: #F >;
    dim0 := case< type | "SL": dim, default: dim-1 >;        
    mat := Evaluate2( p, ClassicalStandardGenerators( type, dim, q0 ));
    
    mat := mat^ConjugateClassicalStandardToMyBasis( type, dim, #F );

    if type eq "Omega" or ( type eq "SU" and IsOdd( dim )) then
         
        vec := [mat[1,x] : x in [2..dim-2] cat [dim]];
        
    elif type eq "Omega-" then
        
        vec := [mat[1,x] : x in [2..dim-3] cat [dim-1, dim ] ];
        
    else
        
        vec := [ mat[1,x] : x in [2..dim0] ];
        
    end if;
    
    return vec;
end function;    
    
    
/* 
  the next function is a special case of the previous one.
  here g is a element of the form 
  
  e1 -> e1 + alpha b. 
  b' -> b' + alppha' f1.
  
  where (b,b') is a hyperbolic pair. We recover alpha.
*/
  
WriteSimpleRootElementAsSLPCharP := function( G, g, pos )

    dim := BBDimension( G );
    type := BBType( G );
    F := BBField( G ); q := #F;
    _, _, d := IsPrimePower( q );  
        
    gensp, _, P := SLPToSiegelTrans( G : EvaluateSLPs := true );
        
    /*
      Determine the generators of the p-group that contain g.
    */
    
    if type eq "SU" and pos eq dim then
        range := [(dim-2)*d+1..(dim-2)*d+d/2];
    else
        range := [(pos-2)*d+1..(pos-1)*d];
    end if;
    
    genssub := [ P.x : x in range ];
    genssubslp := [ gensp[x] : x in range ];
    
    P := sub< GL( Degree( G ), BaseRing( G )) | genssub >;
    p := MatrixPGroupWordInGen( g, P : ComputeBase := false );
    
    p := Evaluate2( p, genssubslp );
    p := Evaluate( p, BBGenerators( G ));
    
    q0 := case< type | "SU": Round( Sqrt( q )), default: q >;
    mat := Evaluate2( p, ClassicalStandardGenerators( type, dim, q0 ));
    
    mat := mat^ConjugateClassicalStandardToMyBasis( type, dim, q );

    if type eq "Omega" or ( type eq "SU" and IsOdd( dim )) then
        return mat[1,pos];
    else
        return mat[1,pos];
    end if;
    
end function;
