freeze;

/* This file contains an implementation of a set of Gaussian elimination type
   algorithms for elements of classical groups over finite fields. The main
   reference is Elliot Costi's PhD thesis (UL, Queen Mary) and my upcoming 
   paper.
  
   We assume that G is a classical group, SL(d,q), Sp(d,q), SU(d,q), 
   Omega(d,q) (plus or minus if d is even) defined over a 
   finite field. The basis of the underlying vector space is assumed to be
   e_1,...,e_n,f_n,...,f_q[,w_1[,w_2]]. In the comments below we index
   matrix entries using these basis elements. 
  
   In the groups that are different from SL, we use Siegel transformations.
   If vec is a vector [a_2,\ldots,a_d] of length d-1, then the Seigel 
   transformation corresponding to vec is the transformation that maps 
   e_1 |-> [1,a_2,\ldots,a_d]   
   b |-> b+beta_b f_1 if b is another basis vector. 
   The coefficients beta_b are uniquely determined by the fact that the 
   transformation must preserve the form. */                         
                         
import "bbclassical.m":BBStandardGenerators, BBField, BBType, BBDimension,
  BBGenerators, BlackBoxClassicalGroup, Evaluate2, BBGroup;
import "bbclassical.m":B;
import "subgroups.m": SLPToSiegelTrans;   
import "elements.m":SiegelTransformToSLP;


/* the following function produced the matrix of the Siegel transformation
   that corresponds to vec. See above for explanation. No check is
   performed to verify that the output is in fact an element of the group. */

SiegelTrans := function( G, vec );
    
    F := BBField( G );
    d := BBDimension( G );
    type := BBType( G );
    
    wittindex := case< type | "Omega-": Round( d/2-1 ), default: Floor( d/2 )>;
    wittdefect := d-2*wittindex;         

    mat := IdentityMatrix( F, d );
    
    if type eq "SU" then
        p := Characteristic( F );
        e := Round( Log( p, #F ));
        q0 := p^Round(e/2);
    end if;
    
    for i in [1..d-1] do 
        // the first row is [0,vec[1],...,vec[#vec]]
        mat[1,i+1] := vec[i];
        // we have non-zero entries in the last col depending on the type.
        if type eq "Sp" and i lt d/2 then
            mat[d-i,d] := -vec[i];
        elif type eq "Sp" then
            mat[d-i,d] := vec[i];
        elif i lt d-1-wittdefect and type eq "SU" then 
            mat[d-i-wittdefect,d-wittdefect] := -vec[i]^q0;
        elif i lt d-1-wittdefect and type in ["Omega+","Omega","Omega-"] then
            mat[d-i-wittdefect,d-wittdefect] := -vec[i];
        end if;
    end for;
    
    if <type,IsOdd( d )> eq <"SU",true> then
        mat[d,d-1] := -mat[1,d]^q0;
    elif type eq "Omega" then
        mat[d,d-1] := 1/2*mat[1,d];
    elif type eq "Omega-" and IsOdd( #F ) then
        z := PrimitiveElement( F );
        mat[d-1,d-2] := 2*vec[d-2];
        mat[d,d-2] := -2*z*vec[d-1];
    elif type eq "Omega-" then 
        q := #F;
        zz := PrimitiveElement( GF( q^2 ));
        mat[d-1,d-2] := GF(q)!(zz+zz^q)*vec[d-1];
        mat[d,d-2] := GF(q)!(zz+zz^q)*vec[d-2];
    end if;
        
    return mat;
end function;    
    
/* The next functions contain the implementations of the rewriting procedures.
   First we need to deal with the low-dimensional cases. This is done 
   separately for each of the classical types. */
    
    
/* The next function deals with the 4-dimensional case of Sp and SU */    
    
procedure ClassicalElementToSLPSpSUDim4( G, g, ~slp_left, ~slp_right )
        
    /* we need to deal with the dimension 4 case separately
       the matrix g now has all zeros except in the diagonal and in 
       positions (1,1), (1,d), (d,1), (d,d)  */

    F := BBField( G );
    q := #F;
    d := BBDimension( G );
    type := BBType( G );
    gens := BBStandardGenerators( G )^G`ConjugatingElementToInternalForm;

    // make the (1,1) entry non-zero
      
    if g[1,1] eq 0 then
        g := gens[1]^-1*g*gens[1];    
        slp_right := slp_right*B.1;
        slp_left := B.1^-1*slp_left;
    end if;
    
    //make (1,f1) entry non-zero  
          
    if g[1,d] eq 0 then  
        g := g*gens[3];
        slp_right := slp_right*B.3;
    end if;
           
    assert g[1,d] ne 0; // (1,d) entry should be non 0

    if type eq "SU" and IsOdd( q ) then
        z := PrimitiveElement( F );
        p := Characteristic( F );
        e := Round( Log( p, q ));
        q0 :=  p^Round(e/2);
        mult := z^(q0+1);
    else
        mult := 1;
    end if;
    
    vec := [ 0 : x in [1..d-2]] cat 
           [ mult*(1-g[1,1])/g[1,d]]; 
    w := SiegelTransformToSLP( G, vec );
    slp_right := slp_right*B.1^-1*w^-1*B.1;
    h := gens[1]^-1*SiegelTrans( G, vec )*gens[1];
  
    g := g*h^-1; 
    
    vec := [ -g[1,i] : i in [2..d]];
    w := SiegelTransformToSLP( G, vec );
    slp_right := slp_right*w;
    h := SiegelTrans( G, vec );
    g := g*h; 

    g := gens[1]^-1*g*gens[1];  
    slp_right := slp_right*B.1;
    slp_left := B.1^-1*slp_left;
            
    vec := [ -g[1,i] : i in [2..d]];
    w := SiegelTransformToSLP( G, vec );
    slp_right := slp_right*w;
    h := SiegelTrans( G, vec );
    g := g*h; 
        
    assert g eq g^0;  
end procedure;        
    
/* We deal with SU( 3, q ) as the last step of SU( 2n+1, q ). The procedure     
   follows Costi. It is not currently proved to run in polynomial time, 
   but it is conjectured to to so. */
    
procedure ClassicalElementToSLPSUDim3( G, g, ~slp_left, ~slp_right )

    F := BBField( G );
    d := BBDimension( G );
    q := #F;
    p := Characteristic( F );
    e := Round( Log( p, q ));
    q0 := p^Round(e/2);
    type := BBType( G );
    gens := BBStandardGenerators( G )^G`ConjugatingElementToInternalForm;
    
    // this is only for testing
          
    g0 := g;
    
    siegslps := SLPToSiegelTrans( G );
    z := PrimitiveElement( F );
    wr := One( B );

    if g[1,1] eq 0 then 
        g := g*gens[1];
        wr := wr*B.1;
    end if; 

    // clean out the (e1,w) entry
    //vec := [ 0 : x in [1..d-3]] cat [-1/2*a^(q0+1),a];
    vec := [ 0 : x in [1..d-3]] cat [-g[1,d-1]/g[1,1],-g[1,d]/g[1,1]];
    s := SiegelTrans( G, vec );
    wr :=  wr*SiegelTransformToSLP( G, vec );
    g := g*s;      
    
    //assert g0*Evaluate( wr, gens ) eq g;
        
    // Now clear out the (e1,f1)-entry
          
    vec := [ 0 : x in [1..d-3]] cat [ -g[1,d-1]/g[1,1], 0 ];
    s := SiegelTrans( G, vec );
    wr := wr*SiegelTransformToSLP( G, vec );
    g := g*s; 
    
    // now transpose and repeat
    g := gens[1]^-1*g*gens[1];
    wr := wr*B.1;
    wl := B.1^-1;
    
    // clean out the (e1,w) entry
    vec := [ 0 : x in [1..d-3]] cat [-g[1,d-1]/g[1,1],-g[1,d]/g[1,1]];
    s := SiegelTrans( G, vec );
    wr := wr*SiegelTransformToSLP( G, vec );
    g := g*s; 
    
    // Now clear out the (e1,f1)-entry
          
    vec := [ 0 : x in [1..d-3]] cat [ -g[1,d-1]/g[1,1], 0 ];
    s := SiegelTrans( G, vec );
    wr := wr*SiegelTransformToSLP( G, vec );
    g := g*s; 
   
    /* now g is diagonal. We produce the inverse of this 
       diaginal matrix. g is determined by the g[e1,e1] entry. 
       Here we follow Costi on pages 44-45.
         
       the first step is to produce an element y whose [e1,e1] entry
       is the same as xi =g[e1,e1]^-1. */

    P<x> := PolynomialRing( F );  
    xi := g[1,1]^-1;
    phi := case< IsEven( q ) | true: (Trace (z, GF(q0)))^-1 * z,
      false: -1/2, default: false >; 
    // this seems to be the fastest way to construct a subfield  
    F0 := sub< F | F.1^(q0+1)>;
              
    count := 0;
        
    /* the next step is only conjectured to to be completed in 
       polynomial time. More investigation is needed. */
    while true  do
        if IsOdd( q ) then
       	    roots := Roots( -1/4*(xi+x)*(xi^q0+x)-1-x ); 
            roots := [ r[1] : r in roots  | r[1] in GF( q0 ) ];
            if #roots ne 0 then lambda := roots[1]; break; end if;
	else
            roots := Roots( phi^2*(xi+x)^(q0+1)+1+x, F ); 
            roots := [ r[1] : r in roots ]; 
            if #roots ne 0 then lambda := roots[1]; break; end if;
        end if;
        count := count+1;
        g := g*gens[4];
        xi := g[1,1]^-1;
    end while;

    wr :=  wr*B.4^count;

    theta := xi+lambda; 

    a := case< IsOdd( q ) | true: (theta*z^Round((q0+1)/2))^q0, 
      false: phi*theta^(q0+1), default: false >;

    vec := case< IsOdd( q ) |
      true: [0 : x in [1..d-3]] cat [ -phi*theta^(q0+1)*z^(q0+1),a],
      false: [0 : x in [1..d-3]] cat [a,theta^q0], default: false >;

    y := gens[8]*gens[1]^-1*SiegelTrans( G, vec )*gens[1];

    wy := B.8*SiegelTransformToSLP( G, vec )^B.1;
    assert y[1,1] eq xi;
       
    /* new we rewrite y to diagonal form. The first steps are the 
       same as what we do with g at the beginning of this function */
         
    // clean out the (e1,w) entry of y
    a := -y[1,d]/y[1,1];
    vec := [ 0 : x in [1..d-3]] cat [phi*a^(q0+1),a];
    s := SiegelTrans( G, vec );
    wyr := SiegelTransformToSLP( G, vec );
    y := y*s; 

    // Now clear out the (e1,f1)-entry
         
    vec := [ 0 : x in [1..d-3]] cat [ -y[1,d-1]/y[1,1], 0 ];
    s := SiegelTrans( G, vec );
    wyr := wyr*SiegelTransformToSLP( G, vec );
    y := y*s;  

    // clear the (w,e1) entry
          
    a := -y[d,1]/y[1,1];
    aa := case< IsOdd( q ) |
      true: (a*z^Round((q0+1)/2))^q0,
      false: a^q0,
      default: false>;

    vec := [ 0 : x in [1..d-3]] cat [ phi*aa^(q0+1),aa];
    s := gens[1]^-1*SiegelTrans( G, vec )*gens[1];; 
    w := SiegelTransformToSLP( G, vec )^B.1;
    y := s*y; 

    // clear the (f1,e1)-entry

    a := case< IsOdd( q ) |
      true: y[d-1,1]/y[1,1]*z^(q0+1),
      false: y[d-1,1]/y[1,1],
      default: true >;

    vec := [ 0 : x in [1..d-3]] cat [ a, 0]; 
    s := gens[1]^-1*SiegelTrans( G, vec )*gens[1];
    wyl := SiegelTransformToSLP( G, vec )^B.1;
    wyl := wyl*w;
    y := s*y; 
    wyl := wyl*wy*wyr;

    //assert Evaluate( wyl, gens  ) eq y;
    wr := wr*wyl;
            
    slp_left := wl*slp_left;
    slp_right := slp_right*wr;
        
end procedure;            
    
/* the following performs the last step in the case of Omega+.
   the SLP we produce is obtained by writing down an isomorphism between 
   Omega+(4,q) and SL(2,q) Y SL(2,q). 
  
   The isomorphism is given as follows. Suppose that V is the 2-dim vector
   space spanned by <e,f>. Then V tensor V is spanned by ee, ef, -fe, ff.
   The product of two matrices SL(2,q)![a,b,c,d] and SL(2,q)![a',b',c',d']
   goes to SL(4,q)![aa',ab',-ba',bb',
                    ac',ad',-b,c',bd',
                    -ca',-cb',da',-db',
                    cc',cd',-dc',dd']; */
   
procedure ClassicalElementToSLPOmegaPlusDim4( G, g,
        ~slp_left, ~slp_right )

  gens := BBStandardGenerators( G )^G`ConjugatingElementToInternalForm;
  d := BBDimension( G );          
  F := BBField( G ); 
  q := #F;
    
  /* the element g is written as a*b in the central product SL(2,q) Y SL(2,q)
    assuming that a[1,1] eq 1 we recover a and b */
    
  // if g[1,1] is zero fix it
  if g[1,1] eq 0 and g[1,2] ne 0 then
      g := g*gens[5];
      slp_right := slp_right*B.5;
  elif g[1,1] eq 0 and g[1,d-1] ne 0 then
      g := g*gens[5]*gens[1]*gens[5];
      slp_right := slp_right*B.5*B.1*B.5;
  elif g[1,1] eq 0 then
      g := g*gens[1]*gens[5];
      slp_right := slp_right*B.1*B.5;
  end if;

  assert g[1,1] ne 0;
  
  // if g[1,2] is zero fix it
  if g[1,2] eq 0 then
      g := g*gens[6];
      slp_right := slp_right*B.6;
  end if;
  assert g[1,2] ne 0;
  
  // if g[1,d-1] eq o fix it
  if g[1,d-1] eq 0 then
      g := g*gens[7];
      slp_right := slp_right*B.7;
  end if;
  
  b := MatrixAlgebra( F, 2 )![g[1,1],g[1,2],g[2,1],g[2,2]];
  a := MatrixAlgebra(F,2)!
       [1,-g[1,d-1]/b[1,1],-g[d-1,1]/b[1,1],g[d-1,d-1]/b[1,1]];
  
  // we make sure that a is in SL( 2, q )
    
  det := Sqrt( Determinant( a ));
  a := a*det^-1; b := b*det;
  
  assert Determinant( a ) eq 1 and Determinant( b ) eq 1;
  zeros := [ 0 : x in [1..d-3]];
  
  // Now reduce the a part.
  // make a[1,1] eq 1
    
  vec := zeros cat [(1-a[1,1])/a[1,2],0 ];
  s := gens[1]^-1*SiegelTrans( G, vec )*gens[1];  
  g := g*s; 
  w := SiegelTransformToSLP( G, vec );     
  slp_right := slp_right*w^B.1;

  // kill a[1,2]
  vec := zeros cat [a[1,2],0];
  s := SiegelTrans( G, vec  );
  g := g*s;
  slp_right := slp_right*SiegelTransformToSLP( G, vec );
  
  g := gens[1]^-1*g*gens[1]; 
  slp_right := slp_right*B.1;
  slp_left := B.1^-1*slp_left;

  vec := zeros cat [-a[2,1]-a[2,2]*(1-a[1,1])/a[1,2],0];
  s := SiegelTrans( G, vec );
  slp_right := slp_right*SiegelTransformToSLP( G, vec );
  g := g*s; 
  
  // now deal with b
    
  vec := [-(1-b[1,1])/b[1,2],0] cat zeros;
  s := SiegelTrans( G, vec );
  s := gens[5]^-1*s*gens[5]; 
  w := SiegelTransformToSLP( G, vec )^B.5;
  slp_right := slp_right*w;
  g := g*s; 
  
  vec := [-b[1,2],0] cat zeros;
  s := SiegelTrans( G, vec ); 
  slp_right := slp_right*SiegelTransformToSLP( G, vec );
  g := g*s; 
  
  g := gens[5]^-1*g*gens[5];
  slp_left := B.5^-1*slp_left;
  slp_right := slp_right*B.5;
  
  vec := [-g[1,2],0] cat zeros;
  s := SiegelTrans( G, vec );
  slp_right := slp_right*SiegelTransformToSLP( G, vec );
  g := g*s; 
  
end procedure; 


/* The base step of Omega is Omega( 3, q ). We use that Omega( 3, q ) 
   is isomorphic to SL( 2, q ) acting on the space of symmetric tensors. 
   If V=<e,f> then SV=< exe, fxf, 1/2(exf+fxe)>. Under this isomorphism
   the element SL(2,q)![a,b,c,d] corresponds to 
   Omega( 3, q )![ a^2, b^2, 2ab, c^2, d^2, 2cd, ac, bd, ad+bc ]. We use 
   this isomorphism to reduce an element of Omega( 3, q ). */

procedure ClassicalElementToSLPOmegaDim3( G, g, ~slp_left, ~slp_right )

   gens := BBStandardGenerators( G )^G`ConjugatingElementToInternalForm;
   d := BBDimension( G );          
   a := Sqrt( g[1,1] );   
   zeros := [ 0 : i in [1..d-3]];
   
   // make sure that (e1,f1) entry is non-zero
     
   if g[1,d-1] eq 0 then
       g := g*gens[8];
       slp_right := slp_right*B.8;
   end if;
   
   // The matrix g corresponds to a matrix SL(2,q)![a,b,c,d]. Find a and b.
   a := Sqrt( g[1,1] ); b := Sqrt( g[1,d-1] );
     
   assert g[1,d-1] ne 0;
   
   /* produce the element that corresponds to SL(2,q)![1,0,(1-a)/b,1].
      post multiplying with this will make g[1,1] eq 0. */
   vec := zeros cat [((1-a)/b)^2,-2*(1-a)/b];
   s := gens[1]^-1*SiegelTrans( G, vec )*gens[1];
   g1 := g*s;
   
   // if this does not work we try with -a.
   if g1[1,1] eq 1 then
       g := g1;
       w := SiegelTransformToSLP( G, vec )^B.1;
       slp_right := slp_right*w;
   else
       b := -b;
       vec := zeros cat [((1-a)/b)^2,-2*(1-a)/b];
       s := gens[1]^-1*SiegelTrans( G, vec )*gens[1];
       g := g*s;
       slp_right := slp_right*SiegelTransformToSLP( G, vec )^B.1;
    end if;
    
    assert g[1,1] eq 1;
    
   // now clear fist row
   vec := zeros cat [-g[1,d-1]+1/2*g[1,d]^2,-g[1,d]];
   s := SiegelTrans( G, zeros cat [-g[1,d-1]+1/2*g[1,d]^2,-g[1,d]]);
   g := g*s;
   slp_right := slp_right*SiegelTransformToSLP( G, vec );
   
   // "transpose"
   g := gens[1]*g*gens[1];
   slp_left := B.1^-1*slp_left;
   slp_right := slp_right*B.1;
      
   // clear first row again
   vec := zeros cat [-g[1,d-1]+1/2*g[1,d]^2,-g[1,d]];
   s := SiegelTrans( G, zeros cat [-g[1,d-1]+1/2*g[1,d]^2,-g[1,d]]);
   g := g*s;
   slp_right := slp_right*SiegelTransformToSLP( G, vec );
   
   assert g eq g^0;
end procedure;

/* The case of Omega-(4,q) is handled through its isomorphism with SL(2,q^2).
   Suppose that V=<e,f> is the natural module for SL=SL(2,q^2). Then SL acts on
   T=V tensor V by acting with a Frobenius twist in the first factor and 
   naturally on the second. Let W=< ee, ff, ef+fe, alpha(ef-fe)> where
   alpha = omega^((q+1)/2) with omega being a primitive element of GF( q^2 ).
   Then W is q [GF( q )SL]-submodule. 
     
   For a given element of Omega-(4,q) we write this element in the natural 
   basis <ee, ef, fe, ff> of T by transforming a suitable basis transformation.
   Then the matrix SL(2,q^2)![a,b,c,d] can be recovered from the top-left 2x2  
   block requireing that the determinant should be 0. */
     
procedure ClassicalElementToSLPOmegaMinusDim4( G, g, ~slp_left, ~slp_right )

     F := BBField( G );
     d := BBDimension( G );
     q := #F;
     type := BBType( G );
     gens := BBStandardGenerators( G )^G`ConjugatingElementToInternalForm;
     
     // g[1,1] cannot be 0
     if g[1,1] eq 0 then
         g := g*gens[8]^gens[1];
         slp_right := slp_right*B.8^B.1;
     end if;
     
     assert g[1,1] ne 0;
     
     // g[1,d-2] cannot be zero
     // if q is even then d[d-2,1] cannot be zero
         
     if g[1,d-2] eq 0 then 
         g := g*gens[8];
         slp_right := slp_right*B.8;
     end if;
     
     // for even q g[d-2,q] cannot be zero
     if IsEven( q ) and g[d-2,1] eq 0 then
         g := gens[8]*gens[1]*g;
         slp_left := B.8*B.1*slp_left;
         assert g[d-2,1] ne 0;
     end if;
     
     assert g[1,d-2] ne 0;

     // get out the remaining 4x4 matrix from g
     g1 := GL( 4, q^2 )![g[1,1],g[1,d-2],g[1,d-1],g[1,d],
                   g[d-2,1],g[d-2,d-2],g[d-2,d-1],g[d-2,d],
                   g[d-1,1],g[d-1,d-2],g[d-1,d-1],g[d-1,d],
		   g[d,1],g[d,d-2],g[d,d-1],g[d,d]];

     zz := PrimitiveElement( GF( q^2 )); al := zz^Round((q+1)/2);
     z := PrimitiveElement( GF( q ));
     // the basis transdformation matrix
     if IsOdd( q ) then  
         mat := GL( 4, q^2 )![1,0,0,0,0,0,0,1,0,1,1,0,0,al,-al,0];
     else
         mat := GL( 4, q^2 )![1,0,0,0,0,0,0,1,0,1,1,0,0,zz,zz^q,0]; 
     end if;
     
     // we transform g1 into the basis ee, ef, fe, ff; see above
     gtr := mat^-1*g1*mat;
     // take out the upper left 2x2 block from gtr
     y := MatrixAlgebra( GF( q^2 ), 2 )![gtr[1,1],gtr[1,2],gtr[2,1],gtr[2,2]];
     // make y have determinant 1
     detinv := Sqrt( Determinant( y )^-1 );
     y := y*detinv;
     
     /* now we need to emulate multiplication with the matrix
     SL(2,q^2)![1,0,u,1] where u is as below */
     zeros := [ 0 : x in [1..d-4]];
     
     if IsOdd( q ) then
         u := ((1-y[1,1])/y[1,2]);
         vec := zeros cat [ GF(q)!(u^(q+1)), GF(q)!(-1/2*(u+u^q)),
                        GF(q)!(-1/2*z^-1*al*(u-u^q))];
         s := gens[1]^-1*SiegelTrans( G, vec )*gens[1];
         g := g*s; 
         slp_right := slp_right*SiegelTransformToSLP( G, vec )^B.1;     
     else 
         u := ((1-y[1,1])/y[2,1]);
         beta := (u+u^q)/(zz+zz^q);
         alpha := u+beta*zz;
         vec := zeros cat [ GF(q)!(u^(q+1)),GF(q)!alpha,GF(q)!beta];
         s := SiegelTrans( G, vec );
         g := s*g; 
         slp_left := SiegelTransformToSLP( G, vec )*slp_left;
     end if;

     assert g[1,1] eq 1;
     
     // new clear first row
     vec := zeros cat [ g[1,d-2], g[1,d-1], g[1,d]];
     s := SiegelTrans( G, vec );
     g := g*s^-1; 
     slp_right := slp_right*SiegelTransformToSLP( G, vec )^-1;
     
     // transpose
     g := gens[1]^-1*g*gens[1];
     
     slp_left := B.1^-1*slp_left;
     slp_right := slp_right*B.1;
     
     //clear first row again
     vec := zeros cat [ g[1,d-2], g[1,d-1], g[1,d]];
     s := SiegelTrans( G, vec );
     g := g*s^-1; 
     
     assert g eq g^0;
     
     slp_right := slp_right*SiegelTransformToSLP( G, vec )^-1;
 end procedure;     

/* The main function. */    
    
ClassicalElementToSLP := function( G, type, d, q, g : 
                                 CheckResult := false )

    F := BBField( G );
    p := Characteristic( F );
    e := Round( Log( p, q ));
    
    mygens := BBStandardGenerators( G )^G`ConjugatingElementToInternalForm;
    g0 := g;
    g := g^G`ConjugatingElementToInternalForm;

    // keep the original g for debugging
    F := BBField( G );
    
    wittindex := case< type | "SL": d, "Omega-": Round( d/2-1 ), 
                 default: Floor( d/2 )>;
    wittdefect := d-2*wittindex;
    
    siegslps := SLPToSiegelTrans( G );
    
    // we need to initialize slps by putting some frequently 
    // needed elements at the beginning     
      
    slp_right := One( B );
    slp_left := One( B );
        
    v1 := mygens[2]*mygens[5];
    wv1 := B.2*B.5;
      
    // we start the actual slp part with the identity element
      
    up := case< type | "SL": d,
                       "Omega": Round( d/2 )-2, 
                       "Omega-": d/2-2, 
                       "SU": Floor((d-2)/2),
                       "Omega+": d/2-2,
                       default: Round( d/2 )-1 >;

    for i in [1..up] do 
        // find the first nonzero entry in the first row.
        firstpos := 0;
        
        repeat 
            firstpos := firstpos+1;
        until g[1,firstpos] ne 0;

        // make the (1,1) entry non-zero

        if firstpos in [2..(d-wittdefect)/2] then
            g := g*mygens[5]^(v1^(firstpos-2));
            slp_right := slp_right*B.5^(wv1^(firstpos-2));
        elif firstpos in [(d-wittdefect)/2+1..d-1-wittdefect] then 
            g := g*mygens[5]^(v1^(d-firstpos-1-wittdefect))*mygens[1];
            slp_right := slp_right*B.5^(wv1^(d-firstpos-1-wittdefect))*B.1;
            // omega+ needs more changing                        
            if type eq "Omega+" then 
               g := g*mygens[5];
               slp_right := slp_right*B.5;
           end if;
        elif firstpos eq d-wittdefect then
            g := g*mygens[1];
            slp_right := slp_right*B.1;
            // omega+ needs more changing                        
            if type eq "Omega+" then 
               g := g*mygens[5];
               slp_right := slp_right*B.5;
           end if;        
        end if;
                    
        //make (1,2) entry non-zero  

        if g[1,2] eq 0 then
            g := g*mygens[6];
            slp_right := slp_right*B.6;
        end if;

        assert g[1,2] ne 0; // (1,2) entry should be non 0

        // make [e1,e1] entry = 1  
        el := case< type | "SL": (-1+g[1,1])/g[1,2],
                           "Omega+": (-1+g[1,1])/g[1,2],
                           "Omega": (-1+g[1,1])/g[1,2],
                           "Omega-": (-1+g[1,1])/g[1,2],
                           default: (1-g[1,1])/g[1,2] >;

        vec := [ el ] cat [ 0 : x in [1..d-2]]; 
        w := SiegelTransformToSLP( G, vec );
        slp_right := slp_right*w^B.5;
        h := mygens[5]^-1*SiegelTrans( G, vec )*mygens[5];
        g := g*h;

        assert g[1,1] eq 1;
        
        vec := [ g[1,i] : i in [2..d]];  
        w := SiegelTransformToSLP( G, vec );
        slp_right := slp_right*w^-1;
        h := SiegelTrans( G, vec );
        g := g*h^-1; 
        
        // if "SL" then we finished the loop
        if type eq "SL" then 
            g := mygens[2]*g*mygens[2]^-1; 
            slp_right := slp_right*B.2^-1;
            slp_left := B.2*slp_left; 
            continue; 
        end if;
        
        assert g[1,1] ne 0; // (1,1) entry should be non 0
        
        s1 := case< type | "Omega+": mygens[1]*mygens[5],
                           default: mygens[1] >;

        g := s1^-1*g*s1; 
        slp_right := slp_right*B.1;
        slp_left := B.1^-1*slp_left;
                
        if type eq "Omega+" then
           slp_right := slp_right*B.5;
           slp_left := B.5^-1*slp_left; 
        end if;
        
        vec := [ g[1,i] : i in [2..d]];
        w := SiegelTransformToSLP( G, vec );
        slp_right := slp_right*w^-1;
        h := SiegelTrans( G, vec );
        g := g*h^-1; 
        g := mygens[2]*g*mygens[2]^-1; 
        
        slp_right := slp_right*B.2^-1;
        slp_left := B.2*slp_left;
    end for;

    /* the last step needs to be done separately for all groups. */
        
    if type eq "Sp" or <type,IsEven( d )> eq <"SU",true> then
        ClassicalElementToSLPSpSUDim4( G, g, ~slp_left, ~slp_right );
    elif <type,IsOdd( d )> eq <"SU",true> then 
        ClassicalElementToSLPSUDim3( G, g, ~slp_left, ~slp_right );
    elif type eq "Omega+" then
        ClassicalElementToSLPOmegaPlusDim4( G, g, ~slp_left, ~slp_right );
    elif type eq "Omega" then
        ClassicalElementToSLPOmegaDim3( G, g, ~slp_left, ~slp_right );
    elif type eq "Omega-" then
        ClassicalElementToSLPOmegaMinusDim4( G, g, ~slp_left, ~slp_right );
    end if;
          
    slp := slp_left^-1*slp_right^-1; 
    slp := Evaluate( slp, BBGenerators( G ));
    
    bbgroup := BBGroup( G );  
    slp := Evaluate2( slp, [ bbgroup.i : i in [1..#Generators( bbgroup )]]);
                   
    if CheckResult then
        assert Evaluate( slp, mygens ) eq g0;
    end if;
                      
    return slp;
end function;
