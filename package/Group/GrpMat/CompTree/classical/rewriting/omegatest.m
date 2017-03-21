// The following is an implementation of Lemma 4.15(ii) of KS.
// returns generators of q meet q^x
  
QMeet:= function( G, x : Transpose := false )
    
    dim := BBDimension( G ); F := BBField( G ); 
    gens := BBStandardGenerators( G );
    type := BBType( G );

    D := gens[4]; X1 := gens[6]; X2 := gens[7]; V := gens[2];
    D := D^V; U := gens[5];
    S := gens[1]*gens[5];
    
    if not Transpose then 
        Q := PSubgroup( G );
    else
        Q := PSubgroup( G )^S;
    end if;
    
    Q1 := Q^x;
    
    gens := Generators( Q );
    if not exists(z){ z : z in gens | Q1^z ne Q1 } then
        return false;
    end if;
        
    Z := sub< Parent( z ) | z >;
    
    
    // z star in KS
    
    if not exists(zst){ zst : zst in gens | zst ne z } then
        return false;
    end if;
    
    Zst := sub< Parent( zst ) | zst >;
    
    if Q1^zst eq Q1 then 
        A := Zst;
    elif exists(u){ u : u in Z | Q1^(Zst.1*u) eq Q1 } then
        A := sub< Parent( Zst.1*u ) | Zst.1*u >;
    else
        return false;
    end if;
    
    // find the normalizer N_{Q1}(Q)
      
    gensq1 := Generators( Q1 );
    
    if not exists(zz){ zz : zz in gensq1 | Q^zz ne Q } then
        return false;
    end if;
    
    ZZ := sub< Universe( {zz} ) | zz >;  
    
    normgens := {@ @};
    
    for i in gensq1 do
        if i ne zz then
            if not exists(u){ u : u in ZZ | Q^(i*u) eq Q } then
                return false;
            end if;
            normgens := normgens join {@ i*u @};
        end if;
    end for;
    
    if not exists( h ){ h : h in normgens | (h,A.1) ne h^0 } then
        return false;
    end if;
    
    return (h,A.1);
    
end function;
    
ClearFirstRowV1 := function( G, g : FirstCall := false )
    
    gens := BBStandardGenerators( G ); 
    dim := BBDimension( G );
    D := gens[4]; X1 := gens[6]; X2 := gens[7]; V := gens[2];
    D := D^V; U := gens[5]; S := gens[1]*gens[5];
    
    // we need that the (1,1) entry is non-zero
      
    CONJ := V;  el := One( G ); i := 0; prog := One( B );
    while IsZeroEntry( G, g*S ) do
        print "while";
        if i gt dim/2 then
            g := g*V;
            el := el*V;
            prog := prog*B.2;
        else
            g := g*V*S;
            el := el*V*S;
            prog := prog*B.2*B.1*B.5;
        end if;
        i := i+1;
    end while;
    
    assert Evaluate( prog, gens ) eq el;
    
    // check also if (1,2)-entry is zero
    
    if IsZeroEntry( G, g*U*S ) then
        g := g*X1; el := el*X1; prog := prog*B.6;
    end if;
    
    
    pz, z := ClearTopRightEntryBB( G, g );
    
    if Category( z ) eq BoolElt then
        z := U; pz := B.5; 
    end if;
        
    el := el*z; prog := prog*pz;
    g := g*z; 
    
    assert Evaluate( prog, gens ) eq el;
    
    w := QMeet( G, g : Transpose := true );
    z := QMeet( G, w ); Z := sub< Universe( {z} ) | z >;
    
    if not exists(z0){ z0 : z0 in Z | qy^(g*z0) eq qy } then
        return false;
    end if;
    
    progz0 := WriteTransvectionAsSLPOmegaPlusBB( G, z0 );
    
    assert Evaluate( progz0, gens ) eq z0;
    
    return One( B ), prog*progz0, One( G ), el*z0;
end function;


IsInH := function( x )

  g1 := qy.1;
  g2 := qy.2;
  
  for i in Generators( qy ) do
      if (g1^x,i) ne One( g ) or (g2^x,i) ne One( g ) then
          return false;
      end if;
  end for;
  
  return true;
  
end function;
    
IsZeroEntry := function( G, g : Pos := 0 )
    
    dim := BBDimension( G ); F := BBField( G ); 
    gens := BBStandardGenerators( G );
    type := BBType( G );

    D := gens[4]; X1 := gens[6]; X2 := gens[7]; V := gens[2];
    D := D^V; U := gens[5];
    S := gens[1]*gens[5];
    
    if Pos in [dim/2+1..dim-1] then
        P := V^(-dim+Pos);
        g := g*P;
    elif Pos in [1..dim/2] then
        P := V^(-Pos+1)*S;
        g := g*P;
    end if;

    z := qy.1;
    if IsInH( g*z*g^-1 ) then return true; end if;
    
    Z := { z^i : i in {0..4}};
    
    gens := Generators( qy );
    
    if not exists(u){ u : u in Z | IsInH( g*qy.2*u*g^-1 )} then
        return false;
    end if;
        
    return true;
end function;
    
ClearTopRightEntryBB := function( G, g  )
    
    gens := BBStandardGenerators( G ); 
    q := #BBField( G );
    D := gens[4]; X := gens[6]; V := gens[2];
    D := D^V;
    
    if IsZeroEntry( G, g  ) then
        return One( B ), One( G );
    end if;
        
    k := 1;
    repeat
        if IsZeroEntry( G, g*X ) then 
            return B.6^((B.4^B.2)^(k-1)), X;
        end if;
        k := k+1; X := X^D;
    until k eq q;
    
    return false, false;
end function;
    
WriteTransvectionAsSLPOmegaPlusBB := function( G, g )
    
    dim := BBDimension( G ); F := BBField( G ); 
    gens := BBStandardGenerators( G );
    type := BBType( G );
    z := PrimitiveElement( F );

    D := gens[4]; X1 := gens[6]; X2 := gens[7]; V := gens[2];
    U := gens[5];
    S := gens[1]*gens[5];

    
    X := X1; D0 := D^V; D1 := D0;
    X0 := X;
    V1 := V*U; PV1 := B.2*B.5; PD0 := B.4^B.2;
    vec := [];
    
    prog := One( B );  XP := B.6; X2P := B.7;
    
    for i in [2..dim-1] do
        
        // if i eq 3 then return X, D1; end if;
        
        exp := 0; g1 := g;
        while not IsZeroEntry( G, g1 : Pos := i ) do
            X := X^D1;
            g1 := g*X;
            exp := exp+1;
        end while;
        
        if exp eq 0 then
            Append( ~vec, 0 );
        else
            Append( ~vec, -z^exp );
            prog := prog*XP^(PD0^exp);
        end if;
        
        if i eq dim/2 then
            X0 := X2^V1^-1;
            XP := X2P^PV1^-1;
            X := X0;
            D0 := D0^-1; D1 := D0;
            PD0 := PD0^-1;
        elif i in [2..dim/2-1] then
            X0 := (X0^V1)^-1;
            XP := (XP^PV1)^-1;
            X := X0;
            D0 := D0^V1; D1 := D0;
            PD0 := PD0^PV1;
        else
            X0 := (X0^V1^-1)^-1;
            XP := (XP^PV1^-1)^-1;
            X := X0;
            D0 := D0^V1^-1; D1 := D0;
            PD0 := PD0^PV1^-1;
        end if;
    end for;
    
    return prog^-1, vec;
end function;
    
    
ClearFirstRow := function( G, g )
    
    gens := BBStandardGenerators( G ); 
    D := gens[4]; X1 := gens[6]; X2 := gens[7]; V := gens[2];
    D := D^V; U := gens[5]; S := gens[1]*gens[5];
    
    pz, z := ClearTopRightEntryBB( G, g );
    
    if Category( z ) eq BoolElt then
        z := U; pz := B.5;
    end if;
    
    g := g*z; progr := pz*B.2; r := z*V^-1;
    
    return g;
    
    // (1,n) entry is clear, but we need to clear the 
    // (1,n-1) and the (2,n) entries. Having no transvections is a pain.
      
    pz, z := ClearTopRightEntryBB( G, g );
    
    if Category( z ) eq BoolElt then
        z := U; pz := B.5;
    end if; 
    
    g := V^-1*g*z*V; progl := B.2^-1; progr := progr*pz*B.2;
    l := V^-1; r := r*z*V;
    
    // (2,n) and (2,n-1) entries zero.
      
    pz, z := ClearTopRightEntryBB( G, g );
    
    if Category( z ) eq BoolElt then
        z := U; pz := B.5;
    end if; 
    
    g := U*g*z; progr := progr*pz; r := r*z;
    l := U*l; progl := B.2*progl;
    
    XX2 := X2^S; //return XX2, g;
    z := (XX2^(XX2^g));
    X3 := X1;
    i  := 1; 
    
    z := z*XX2^-1;
    return g, z;
    
    roots, prroots := RootElements( G );
    
    while z eq X2 do
        
        print "loop";
        
        g := roots[i]*g;
        progl := prroots[i]*progl;
        l := roots[i]*l;
         _, z := ClearTopRightEntryBB( G, g );
    
         if Category( z ) eq BoolElt then
             z := U; pz := B.5;
         end if; 
         
         g := g*z; progr := progr*pz; r := r*z;
         
         // now (1,n), (1,n-1) and (2,n) entries are zero
           
         XX2 := X2^S;
         z := (XX2^(XX2^g))^S;
         i := i+1;
         
     end while;
     
//     g := g; progl := B.2*progl;

     z := z*XX2^-1;

     return g, z;
     
     pz, vec := WriteTransvectionAsSLPOmegaPlusBB( G, z );
     
     return z;
     
     return progl, progr*pz^-1, Evaluate( progl, gens ), 
            Evaluate( progr, gens );
     
end function;
    
    
    
    
      
    
    
            
        
    
