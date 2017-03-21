freeze;

import "bbclassical.m":B, BBStandardGenerators, BBType, BBField, BBDimension;
import "subgroups.m":SLPToSiegelTrans, LongRootGroup;
import "elements.m":RootElements, SiegelTransformToSLP;

// the functions in this file implement black box rewriting procedures
// for orthogonal groups.
// the ideas are the same as in Chapter 4 of Kantor and Seress, 
// Black box classical groups.
//  
// If v is a lin. comb of <e_2,...f_1> then t_v denotes the root element
// that has e_1+v in the first row, the corresponding vector in the last 
// column and identity elsewhere. \bar t_v denotes the transpose of such 
// an element.  
  
  
// tests membership in the stabilizer H of <e1>
  
IsInH := function( G, g )

    gens := BBStandardGenerators( G );
    type := BBType( G );
    
    // get the transposes of root elements of the form t_e where
    // e is a basis element in [e_2,...,e_n,w_1,w_2,f_n,...,f_1]  
    
    roots := RootElements( G : Transpose := true );
    
    // we choose two roots
      
    r1 := roots[2]; r2 := roots[3];
    
    for i in roots do
        if (r1^g,i) ne One( G ) or (r2^g,i) ne One( G ) then
            return false;
        end if;
    end for;
    
    return true;
  
end function;
    
// we need to get the long root element 1 xi 0 0 0
//                                      0 1  0 0 0 etc  
// where xi is the primitive root fixed
  
LongRootXi := function( G : stgens := 6 )
    
    F := BBField( G );     
    q := #F; _, p, d := IsPrimePower( q );
    zz := PrimitiveElement( F );  
    type := BBType( G );
    
    pX := case< stgens |
          6 : B.6,
          7 : B.7,
          8 : B.8, 
          default: false >;
    
    if type eq "Omega+" then
        return pX^(B.4^B.2);
    elif type eq "Omega-" then
        return pX^(B.4^B.2);
    end if;
    
    // type is Omega
    
    mat := [];  
    for i in [0..d-1] do
        mat := mat cat Eltseq( zz^(2*i) );
    end for;
    
    mat := GL( d, p )!mat;
    
    v := VectorSpace( GF( p ), d )!Eltseq( zz )*mat^-1;
     
    prog := One( B ); 
    for i in [1..d] do 
        prog := prog*pX^(Integers()!v[i]);
        pX := B.4*pX*B.4^-1;  
    end for;
    
    return prog;
end function;
    
    /* Q is the subgroup of the elements of the form
       t_v where v in <e_2,..,e_n,w_1,w_2,f_n,...,f_1>.
       the function returns an element in Q meet Q^x if exists.
       otherwise returns false. See Lemma 4.15(ii) of Kantor-Seress. 
                                                        
       Optional parameter Transpose can be set. In this case Q is replaced
       by its transposed. */
                                                         
    
QMeet:= function( G, x : Transpose := false )
    
    dim := BBDimension( G ); 
    gens := BBStandardGenerators( G );
    type := BBType( G );
    _, p := IsPrimePower( #BBField( G ));
    
    // define D as a suitable diagonal element
    
    D := gens[4]^gens[2]; 
    
    // S interchanges e_1 with f_1
    
    if type eq "Omega+" then
        S := gens[1]*gens[5];
    elif type eq "Omega-" and IsEven( #BBField( G )) then
        S := gens[1]^2;
    else
        S := gens[1];
    end if;
    
    /* Q is set to be the subgroup of elements t_v where 
       v in <e_2,..,e_n,w_1,w_2,f_n,...,f_1>. If Transpose is true
       then Q is the transpose of this subgroup. 
       isnormq is a function that tests if an element x normalizes Q. 
       roots is set to be { t_e | e ne e_1 } or its transpose when 
       Transpose is true */
         
    if not Transpose then 
        _, Q := SLPToSiegelTrans( G : EvaluateSLPs := true ); 
        Q := sub< Universe( Q ) | Q >;
        isnormQ := func< x | IsInH( G, x^S )>;
        roots := RootElements( G );
    else
        _, Q := SLPToSiegelTrans( G : EvaluateSLPs := true );
        Q := sub< Universe( Q ) | Q >^S;
        isnormQ := func< x | IsInH( G, x )>;
        roots := RootElements( G : Transpose := true );
    end if;
    
    // We set Q1 to be Q^x
    
    Q1 := Q^x; 
    
    // roots[r]^x^-1 will not be in H (normalizer of Q, 
    // stabilizer of <e_2,...,f_1> ). we find this r
    
    if not exists(r){ r : r in [1..dim-2] | not isnormQ( roots[r]^x^-1 ) } then
        return false, 1;
    end if;

    // Z will be the group of elements t_{v} where v = alpha b_r
    // it is the group Z^* in Kantor Seress  
    // x*Z*x^-1 does not normalize Q  

    Z := LongRootGroup( G, r : Transpose := Transpose );    

    // We find another long root group which is different from Z
    // in case of Omega and Omega- we avoid choosing t_w and t_w_i
    // not sure, though, why this is necessary  
    
    ind := [ x : x in [1..dim-2] | x ne r ];
    if type eq "Omega-" then
        ind := [ x : x in ind | not x in [dim-1,dim]];
    elif type eq "Omega" then
        ind := [ x : x in ind | x ne 1 ];
    end if;

    Zst := LongRootGroup( G, ind[1] : Transpose := Transpose );

    // A will be a subgroup of G such that x*A*x^{-1} normalizes Q.
    // If Zst is like this, this is chosen
    // if not then for every generator y of Zst, there is an element u in Z   
    // such that x*yu*x^-1 normalizes Q.
    // we collect the set of such elements.
    
    if isnormQ( Zst.1^x^-1 ) then 
        Agens := {@ x : x in Generators( Zst ) @};
    else 
        Agens := {@ @};
        for y in Generators( Zst ) do
            
            if exists(u){ u : u in Z | isnormQ( (y*u)^x^-1) } then
                Agens := Agens join {@ y*u @}; 
            else
	      return false, 2, Z, y; 
            end if; 
        end for;
    end if;
    
    A := sub< Universe( Agens ) | Agens >;
            
    // find the normalizer N_{Q1}(Q)
    // first find the roots in Q1  
      
    rootsq1 := [ y^x : y in roots ];
    
    // find some root element in rootsq1 that does not normalize Q
         
    if not exists(r){ r : r in [1..dim-2] | not isnormQ( rootsq1[r] ) } then
        return false, 3;
    end if;
    
    // ZZ is a long root group in Q1 that does not normalize Q
    
    ZZ := LongRootGroup( G, r : Transpose := Transpose )^x;  
    zz := ZZ.1;
    
    // we find the generators of the normalizer N_{Q1}(Q)
   
    normgens := {@ @};
    
    // for each root i in rootq1 not in ZZ, find u in ZZ such
    // that iu normalizes Q
      
    for i in rootsq1 do
        if i ne zz then
            if not exists(u){ u : u in ZZ | isnormQ( i*u ) } then
                return false, Q, Q1, ZZ, i, 4;
            end if;
            
            normgens := normgens join {@ i*u @};
        end if;
    end for;
    
    // find h among the generators of Norm such that (h,A.1) ne 1
    // if h does not exists then return Agens  
    
    if not exists( h ){ h : h in normgens | (h,A.1) ne h^0 } then
        return Agens;
    end if; 
    
    return {@ (h,x) : x in Agens @};
    
end function;
    
    /* this function tests if the [e_1,f_1] entry in the preimage of g 
       is zero. Setting the optional parameter pos, it can be 
       used to test if an entry in the [e_1,b] position is zero
       where b is another basis element different from e_1. */
                              
IsZeroEntry := function( G, g : Pos := 0 )
    
    dim := BBDimension( G ); 
    _, _, d := IsPrimePower( #BBField( G ));
    gens := BBStandardGenerators( G ); 
    type := BBType( G );
    
    D := gens[4]; V := gens[2];
    
    if type eq "Omega+" then D := D^V; end if;
        
    if type eq "Omega+" then
        S := gens[1]*gens[5];
    elif type eq "Omega-" and IsEven( #BBField( G )) then
        S := gens[1]^2;
    else
        S := gens[1];
    end if;
        
    // if Pos ne 0, then we need to modify g 
    
    offs := case< type | 
            "Omega+": 1,
            "Omega": 1, 
            "Omega-": 3,
            default: false >;
    
    if Pos in [Floor( dim/2 )+1..dim-1] then
        P := V^(Pos-offs+1);
        g := g*P;
    elif Pos in [1..Floor( dim/2 )] then
        P := V^(-Pos+1)*S;
        g := g*P;
    end if;
    
    z := RootElements( G : Transpose := true )[1];
    if IsInH( G, g*z*g^-1 ) then return true; end if;
    
    Zgens := { z^(D^i) :  i in {0..d-1}};
    
    // modified here. Omega+ had a different definition of Z
    
    Z := sub< Universe( Zgens ) | Zgens >;
    
    r := RootElements( G : Transpose := true )[2];
    
    if not exists(u){ u : u in Z | IsInH( G, g*r*u*g^-1 )} then
        return false;
    end if;
        
    return true;
end function;
    
    // clears the top right entry of g
    
ClearTopRightEntryBB := function( G, g )
    
    gens := BBStandardGenerators( G ); 
    type := BBType( G );
    q := #BBField( G );
    D := gens[4]; X1 := gens[6]; V := gens[2];
    D := D^V; U := gens[5];
    pX2 := LongRootXi( G );
    X2 := Evaluate( pX2, gens );
    
    if IsZeroEntry( G, g  ) then
        return One( B ), One( G );
    end if;
        
    k := 1;
    repeat
        if IsZeroEntry( G, g*X1 ) then 
            return B.6^((B.4^B.2)^(k-1)), X1;
        end if;
        
        // in case of Omega we need to check the other long root element
        
          if type eq "Omega" then
            if IsZeroEntry( G, g*X2 ) then
                return pX2^((B.4^B.2)^(k-1)), X2;
            end if;
            X2 := X2^D;
        end if;
        X1 := X1^D;
        k := k+1;
    until k eq q;
    
    return B.5, U;
end function;
    
    
    // given an element t_v, we write determine
    // the entries of the first row of t_v  
        
EntriesOfRootElementOmegaBB := function( G, g : Offset := 0 )
    
    // set up the usual variables
    
    dim := BBDimension( G ); 
    F := BBField( G ); q := #F;
    gens := BBStandardGenerators( G );
    type := BBType( G );
    z := PrimitiveElement( F );
    
    D := gens[4]; X1 := gens[6]; X2 := gens[7];
    V := gens[2]; U := gens[5];
    
    // set up the element that swaps e1 and f1
    
    if type eq "Omega+" then
        S := gens[1]*gens[5];
    elif type eq "Omega-" and IsEven( #BBField( G )) then
         S := gens[1]^2;
    else
         S := gens[1];
    end if;
    
    // we need a diagonal element
    
    D0 := D^V;
    
    X11 := X1; X21 := X2; 
    pX12 := LongRootXi( G );
    X12 := Evaluate( pX12, gens ); 
    
    // V1 is a cycle that fixes e_1 and f_1
    
    V1 := V*U; 
    vec := [];
    
    prog := One( B );  
    
    X := X11; XX := X12; g0 := g;
    
    roots := RootElements( G : Transpose := true );

    // the first loop determines the entries that correspond to 
    // e_2,..,e_n and builds the first part of the SLP 
   
    for i in [2..case< type | "Omega-": dim/2-1, default: Floor( dim/2 )> ] do
 
        g1 := g0; g2 := g0;
        found := false; j := 0;
        for exp in [0..q-1] do
            if roots[i-1]^(roots[i-1]^g1) eq roots[i-1] then 
                j := exp;
                found := "X";
                break;
            end if;
            
            // if the type is Omega, then the diagonal element has 
            // omega^2 and so a second loop is required  
            
            if type eq "Omega" then
                if  roots[i-1]^(roots[i-1]^g2) eq roots[i-1] then
                    j := exp;
                    found := "XX";
                    break;
                end if;
                XX := XX^D0;
                g2 := g0*XX;
            end if;

            X := X^D0;
            g1 := g0*X;
        end for;  
        if j eq 0 then
           Append( ~vec, F!0 );
           g0 := g1;
       elif type in { "Omega+", "Omega-" } then
           Append( ~vec, -z^(j+Offset));
           g0 := g;
       elif type eq "Omega" and found eq "X" then
           Append( ~vec, -z^(2*j+Offset));
           g0 := g1;
       elif type eq "Omega" and found eq "XX" then
           Append( ~vec, -z^(2*j+1+Offset));
           g0 := g2;
       end if;
              
       D0 := D0^V1;
       X11 := (X11^V1)^-1; X12 := (X12^V1)^-1;
       X := X11; XX := X12;
   end for;

   // second part

   exp := case< type | 
          "Omega-":  Round(dim/2) mod 2,
          default: Round(dim/2) mod 2+1 >;

   X21 := (X2^V1^-1)^(-1)^exp;
   pX22 := LongRootXi( G : stgens := 7 );
   X22 := Evaluate( pX22, gens ); 
   X22 := (X22^V1^-1)^(-1)^exp;
   
   X := X21; XX := X22; 
   
   D0 := case< type | 
         "Omega+": (D^-1)^(V^(-2)),
         default: (D^-1)^(V^(-1)) >;

   // the second cycle determines the entries that correspond to the
   // basis elements f_n,..,f_1 and the corresponding SLP  
    
   for i in [ case< type | "Omega-": dim/2, default: Floor( dim/2 )+1>..
           case< type | "Omega-": dim-2, "Omega": dim-2, 
           default: dim-1 >] do
       g1 := g0; g2 := g0;
       found := false; j := 0;
       for exp in [0..q-1] do
           
           if roots[i-1]^roots[i-1]^g1 eq roots[i-1] then 
               j := exp;
               found := "X";
               break;
           end if;
           
           if type eq "Omega" then
               if roots[i-1]^roots[i-1]^g2 eq roots[i-1]then
                   j := exp;
                   found := "XX";
                   break;
               end if;
               XX := XX^D0;
               g2 := g0*XX;
           end if;
           
           X := X^D0;
           g1 := g0*X;
       end for;
       
       if j eq 0 then
           Append( ~vec, F!0 );
           g0 := g0;
       elif type in {"Omega+","Omega-"} then
           Append( ~vec, -z^(j+Offset));
           g0 := g1;
       elif type eq "Omega" and found eq "X" then
           Append( ~vec, -z^(2*j+Offset));
           g0 := g1;
       else
           Append( ~vec, -z^(2*j+1+Offset));
           g0 := g2;
       end if;
       
       D0 := D0^V1^-1;
       X21 := (X21^V1^-1)^-1; X22 := (X22^V1^-1)^-1;
       X := X21; XX := X22;
   end for;
   
   // getting the w entry for Omega
     
   if type eq "Omega" then
       X := gens[8]; pX := B.8; pXX := LongRootXi( G : stgens := 8 );
       XX := Evaluate( pXX, gens );

       g1 := g0; g2 := g0;
       D0 := D^-1;
       
       found := false; j := 0;
       for exp in [0..q-2] do
           
           if g1 eq One( G )  then 
               j := exp;
               found := "X";
               break;
           end if;
           
           if g2 eq One( G ) then
               j := exp;
               found := "XX";
               break;
           end if;
           X := X^D0;
           g1 := g0*X;
           
           XX := XX^D0;
           g2 := g0*XX;
           
       end for;
       
       if j eq 0 then
           Append( ~vec, 0 );
           g0 := g0;
       elif found eq "X" then
           Append( ~vec, -z^(2*j+Offset));
           g0 := g1;
       else
           Append( ~vec, -z^(2*j+1+Offset));
           g0 := g2;
       end if;
   end if;

   // getting the two entries of Omega- that correspond to w_1 and w_2
     
     if type eq "Omega-" then 
       // we clean out the entries of g that 
       // were computed up to now
       g := g*Evaluate( SiegelTransformToSLP( 
                      G, vec cat [0,0,0]), gens )^-1;
       X1 := One( G ); X2 := One( G );
       
       if IsOdd( q ) then
           D0 := gens[4]^Round((q+1)/2);
       else
           D0 := gens[4]^-(q+1);
       end if;
       
       g1 := g; h := One( G );
       
       for i in [0..q-1] do
           for j in [0..q-1] do
               
               if X1*X2 eq g then
                   
                   if X1 eq One( G ) then
                       v1 := 0;
                   elif IsOdd( q ) then
                       v1 := z^-(j-1);
                   else
                       v1 := z^(2*j-2);  
                   end if;
                   
                   if X2 eq One( G ) then
                       v2 := 0;
                   elif IsOdd( q ) then
                       v2 := z^-(i-1);
                   else
                       v2 := z^(2*i-2);
                   end if;
                   
                   vec := vec cat [ v1, v2 ];
                   break i;
               end if;
               
               if X1 eq One( G ) then
                   X1 := gens[8]; 
               else
                   X1 := X1^D0;
               end if;
               
           end for;
           
           if X2 eq One( G ) then
               X2 := gens[9]; 
           else
               X2 := X2^D0;
           end if;
           
           X1 := One( G );
           
       end for;
   
       vec1 := [ vec[i] : i in [1..dim/2-2]];
       vec1 := vec1 cat [ vec[i] : i in [dim/2-1..dim-4]];
       vec1 := vec1 cat [ vec[#vec-1], vec[#vec]];
       
       vec := vec1; 
   end if;

   return vec;
end function;
    
WriteSimpleRootElementAsSLPOmegaBB := function( G, x, pos )
    
    // only implemensted for pos eq 2
    assert pos eq 2;
        
    if x eq One( G ) then
        return 0;
    end if;
    
    F := BBField( G ); q := #F;
    _, _, d := IsPrimePower( q );
    gens := BBStandardGenerators( G );
    type := BBType( G );
    
    coeff := case< type | 
             "Omega": 2,
             default: 1 >;
    
    _, P := SLPToSiegelTrans( G : EvaluateSLPs := true );
    c := (pos-2)*d+1;
    
    D := gens[4]^(gens[2]^(pos-1));
    R1 := P[c]; R2 := Evaluate( LongRootXi( G : stgens := 6 ), gens );
    count := 0;
     
    for count in [0..q-2] do
        if x eq R1 then
            return PrimitiveElement( F )^(coeff*count);
        elif x eq R2 then
            return PrimitiveElement( F )^(coeff*count+1);
        end if;
        
        R1 := R1^D; R2 := R2^D;
    end for;

    
end function;
    
    // Clears the first row of g
    // returns elements and SLPs that multiply g to an element 
    // that stabilizes <e_1>  
    // FirstCall is optional, it inducates if it is the first call
    // to this function when g[e_1,e_1]=0 is possible                                            
ClearFirstRowOmegaBB := function( G, g : FirstCall := false )
    
    gens := BBStandardGenerators( G ); 
    dim := BBDimension( G );
    type := BBType( G );
    
    // set up the usual generators
    
    X1 := gens[6]; X2 := gens[7]; V := gens[2]; U := gens[5]; 
    
    if type eq "Omega+" then
        S := gens[1]*gens[5];
        S1 := S; 
        prS := B.1*B.5;
        prS1 := prS;
    elif type eq "Omega-" and IsEven( #BBField( G )) then
        S := gens[1]^2;
        S1 := gens[1];
        prS := B.1^2;
        prS1 := B.1;
    else
        S := gens[1];
        S1 := S;
        prS := B.1;
        prS1 := prS;
    end if;
    
    // we need that the (1,1) entry is non-zero
      
    prog := One( B ); el := One( G );   
    if FirstCall then
        V1 := One( G );  
        for i in [1..Round( dim/2 )] do
            if not IsZeroEntry( G, g*S ) then
               el := V1;
               break;
           elif not IsZeroEntry( G, g ) then
               g := g*S1;
               el := V1*S1;
               prog := prog*prS1;
               break;
           end if;
           
           V1 := V1*V; 
           prog := prog*B.2;
           g := g*V;
       end for;
   end if;

   // check also if (1,2)-entry is zero. it should be non-zero
                     
   if IsZeroEntry( G, g*U*S ) then
       g := g*X1; el := el*X1; prog := prog*B.6;
    end if;

    // make (1,n-1) entry non-zero

    if IsZeroEntry( G, g*U ) then
        g := g*X2; el := el*X2; prog := prog*B.7;
    end if;
    
    // make (1,n) entry zero
    
    pz, z := ClearTopRightEntryBB( G, g );
    el := el*z; prog := prog*pz;
    g := g*z; 
    
    // Now find an element w in the intersection of
    // Qt and Qt^g where Qt is the set of elements \bar t_v

    w := QMeet( G, g : Transpose := true )[1];
    
    // next find an element in the intersection of Q and Q^w where
    // Q is the set of elements t_v 
    
    z := QMeet( G, w ); 
    
    // there is some u in <z> such that g*u is in H.
                                                      
    if not exists( u ){  u : u in sub< Universe( z ) | z > 
               | IsInH( G, g*u )} then
        return false, 1;
    end if;
    
    // finally we write this u as SLP in the gens
    
    vec := EntriesOfRootElementOmegaBB( G, u );
    // we need to insert a 0 in the position [e1,f1]
    vec := Insert( vec, dim-
                   case< type | "Omega+": 1, "Omega": 2, "Omega-": 
                   3, default: false >, 0 );
    progz0 := SiegelTransformToSLP( G, vec );

    return One( B ), prog*progz0, One( G ), el*u;
end function;
