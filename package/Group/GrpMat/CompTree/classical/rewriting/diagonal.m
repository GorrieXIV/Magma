freeze;

forward DiagonalElementToSLPCharP;

import "subgroups.m": SLPToSiegelTrans;
import "elements.m": DiagonalElement, SiegelTransformToSLP;
import "selection.m": WriteSimpleRootElementAsSLP, EntriesOfRootElement;
import "bbclassical.m": B, Evaluate2, BBField, BBDimension, BBType, 
  BBStandardGenerators;
import "MatrixPGroup.m": MatrixPGroupWordInGen;
import "sl.m":DiagonalElementToSLPBBSL2;
import "su34.m":DiagonalElementToSLPSUBBDim3, DiagonalElementToSLPSUBBDim4;

/* 
  The diagonal elements of Omega-(4,q) are written as SLP by the next 
  function.
*/

DiagonalElementToSLPOmegaMinus4CharP := function( G, g )
      
    q := #BBField( G );
    stgens := ClassicalStandardGenerators( "Omega-", 4, q );
    _, _, f := OrthogonalForm( sub< GL( 4, q ) | stgens >);
        
    if IsOdd( q ) then
        a := f[3,3]; b := f[4,4];
    else
        a := f[3,4]; b := a;
    end if;
    
    if IsEven( q ) then
        _, Q := QuadraticForm(  sub< GL( 4, q ) | stgens > );
        r := Q[3,4]; s := Q[4,4];
    end if;
    
    gens := BBStandardGenerators( G );
    if IsOdd( q ) then
        T := gens[8]; 
    else
        T := gens[8];
    end if;
    
    v := EntriesOfRootElement( G, T^g : Method := "CharP" ); 
    
    if IsOdd( q ) then
        c := Sqrt( -(v[1]^2*a+v[2]^2*b)/2)^-1;
    else
        c := Sqrt( (v[1]*(v[1]+r*v[2])+v[2]*s*v[2])^-1 );
    end if;
 
    bas1 := stgens[3][1,1];
    ex := Log( bas1, c );
    el := gens[4]^-ex; pr := B.4^-ex;
    g := g*el;
    
    v1 := EntriesOfRootElement( G, T^g : Method := "CharP" );
    V2 := VectorSpace( GF(q), 2 );
    v1 := V2!v1;
    
    if IsEven( q ) then
        
        t1 := stgens[1]^stgens[3];
        T1 := gens[8]^gens[4];
        c := t1[1,3]; d := t1[1,4];
        w := EntriesOfRootElement( G, T1^g : Method := "CharP" );
        w := V2!w;
        v2 := (w-c*v1)/d;
        M := MatrixAlgebra( GF( q^2 ), 2 )![ v1[1],v1[2],v2[1],v2[2]];
        
    else
        
        M := MatrixAlgebra( GF( q ), 2 )![ v1[1]*a, v1[2]*b, -v1[2], v1[1] ];
        b := V2![0,1];
        b := M^-1*Transpose( Matrix( b ));
        c := b[1,1]; d := b[2,1];
        M := MatrixAlgebra( GF( q^2 ), 2 )![ v1[1], v1[2], c, d ];
    end if;
    
    a := {@ x[1] : x in Eigenvalues( M ) @}[1];

    exp := case< IsOdd( q ) | true: (q-1) div 2, false: q-1, 
           default: false >;
    
    stmat := GL(4,q^2)!(stgens[3])^exp;
    bas := {@ x[1] : x in Eigenvalues( stmat ) | not x[1] in GF( q ) @}[1];
    
    ex1 := Log( bas, a ); ex2 := Log( bas, a^-1 );
    ex3 := Log( bas, -a ); ex4 := Log( bas, -a^-1 );
    
    el1 := gens[4]^(-ex1*exp); pr1 :=  B.4^-(ex1*exp);
    el2 := gens[4]^(-ex2*exp); pr2 :=  B.4^-(ex2*exp);
    el3 := gens[4]^(-ex3*exp); pr3 :=  B.4^-(ex3*exp);
    el4 := gens[4]^(-ex4*exp); pr4 :=  B.4^-(ex4*exp);
    c := gens[4]^((q-1)*(q+1) div 4); pc := B.4^((q-1)*(q+1) div 4);
    
    els := [ el1, el2, el3, el4, el1*c, el2*c, el3*c, el4*c ];
    prs := [ pr1, pr2, pr3, pr4, pr1*pc, pr2*pc, pr3*pc, pr4*pc ];
    
    gels := [ g*els[x] : x in [1..8] ];
    
    t := exists( x ){ x : x in [1..8] | gels[x] eq One( G ) };
    
    if not t then
        t := exists( x ){ x : x in [1..8] | (gels[x],T) eq One( G ) };
    end if;
    
    if t then
        return pr*prs[x], el*els[x];
    else 
        return false, false;
    end if;
end function;

/* 
  The next function write a diagonal element of G as SLP. The element
  g is in the diagonal form diag(alpha,beta,beta,...,beta) in SL; 
  or diag(alpha,beta,beta,...,beta,alpha') otherwise where
    
  alpha' = alpha^-1 (Sp)
  alpha' = alpha^-q (SU)
  beta^2 = 1 (Sp)  
    
  The idea is that we find the product alpha^-1 beta and use the information 
  above with the eqation that det g = 1 to recover alpha and beta. 
*/  

DiagonalElementToSLP := function( G, g : Method := Method )
    
    dim := BBDimension( G );
    type := BBType( G );
    
    // some small-dimensional cases are handled separately
    
    if Method eq "BB" and type eq "SL" and dim eq 2 then
        return DiagonalElementToSLPBBSL2( G, g );
    elif <type,dim> eq <"Omega-",4> then
        return DiagonalElementToSLPOmegaMinus4CharP( G, g );
    elif <type,dim,Method> eq <"SU",4,"BB"> then
        return DiagonalElementToSLPSUBBDim4( G, g );
    elif <type,dim,Method> eq <"SU",3,"BB"> then
        return DiagonalElementToSLPSUBBDim3( G, g );
    end if;

    F := BBField( G );
    gamma := PrimitiveElement( F );
    q := case< type | "SU": Round( Sqrt( #F )), default: #F >;
    gens := BBStandardGenerators( G );
    
    // we use a root element to find alpha^-1 beta. generally we use 
    // f_{f1,e2} except when it does not exists  
    
      if <type,dim> in { <"SU",3>, <"Omega",3> } then
        X := gens[8];
        c := EntriesOfRootElement( G, X^g : Method := Method );
        c := c[1];
    else
        X := gens[6];
        c := WriteSimpleRootElementAsSLP( G, X^g, 2 : Method := Method );
    end if;

    /* 
      d will be the first diagonal element used to write g as an SLP.
      it is a diagonal element of the form
      diag( alpha0,beta0,...,beta0,alpha0')
      where alpha0' relates to alpha0 as alpha' relates to alpha above.
    */
    
    dp := DiagonalElement( type, dim, q );
    d := Evaluate( dp, gens );  
    
    /* 
      now solve the equations explained before the function.    
      and find the possibilities for beta.
      
      we also set up the following:
      alpha0, beta0.
      
      alpha1 is the [e1,e1] entry of gens[10]
    */
      
    if type eq "SL" then
        betas := AllRoots( c, dim );
        alpha0 := gamma^(-dim+1);
        alpha1 := F!1;
        beta0 := gamma;
    elif type eq "Sp" then
        betas := [ F!1, F!-1 ];
        alpha0 := F!1;
        alpha1 := gamma;
        beta0 := F!-1;
    elif type eq "SU" and IsEven( dim ) then
        betas := AllRoots( c^(1-q), dim );
        alpha0 := gamma^((-q+1)*((dim-2) div 2 ));
        alpha1 := gamma^(q+1);
        beta0 := gamma^(q-1);
    elif type eq "SU" and dim eq 3 then
        betas := AllRoots( c^(1-q), dim );
        beta0:= gamma^(q-1);
        alpha0 := gamma;
        alpha1 := gamma^(q+1);
    elif type eq "SU" and IsOdd( dim ) then
        betas := AllRoots( c^(1-q), dim );
        alpha0 := gamma^(q+((2*(dim div 2))));
        alpha1 := gamma^(q+1);
        beta0 := gamma^(q-1);
    elif type eq "Omega+" then
        betas := [ F!1, F!-1 ];
        alpha0 := (F!-1)^(((dim-2) div 2) mod 2 );
        beta0 := F!-1;
        alpha1 := gamma^2;
    elif type eq "Omega-" then
        betas := [ F!1, F!-1 ];
        alpha00 := ClassicalStandardGenerators( "Omega-", 
                           dim, q )[3][dim-3,dim-3];
        alpha0 := alpha00^((q+1) div 2-((q-1) div 2)*(dim div 2-2));
        beta0 := F!-1;
        alpha1 := alpha00^2;
    elif type eq "Omega" then
        betas := [ F!1 ];
        alpha0 := F!1;
        beta0 := F!1;
        alpha1 := gamma^2;
    end if;
    
    // compute the possibilities for alpha
    
    alphas := [ x*c^-1 : x in betas ];
    
    // we are also looking for a rewriting of g modulo center
    
    foundcentral := false;
    iscentral := func< x | { true } eq { x^z eq x : z in gens } >;
    
    // try all possiblities. we have at most dim.
      
    for i in [1..#alphas] do
        alpha := alphas[i]; beta := betas[i];
        exp1 := Log( beta0, beta );
        if exp1 ne -1 then
            
            // first multiply g with the appropriate power of d
            
            pr := dp^-exp1;
            el := d^-exp1;
            g1 := g*el;
                        
            // then with the appropriate power of gens[10]
              
            exp2 := Log( alpha1, alpha*alpha0^-exp1 );
            pr := pr*B.10^-exp2;
            el := el*gens[10]^-exp2;
            g1 := g1*gens[10]^-exp2;
            
            // now check if we have 1
                            
            if g1 eq One( G ) then
                return pr, el;
            end if;
            
            // if it is central then we save it for later
              
            if not foundcentral and iscentral( g1 ) then
                
                foundcentral := true;
                cpr := pr; cel := el;
                
            end if;
        end if;
    end for;
    
    if foundcentral then
        return cpr, cel;
    else 
        return false, false;
    end if;
    
end function;
        
    
    
