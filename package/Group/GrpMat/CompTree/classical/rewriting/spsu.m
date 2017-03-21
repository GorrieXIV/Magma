freeze;

// this file contains the common functions to deal with symplectic and unitary
// groups
  
  
import "bbclassical.m":B, Evaluate2, BBType, BBField, BBStandardGenerators, 
  BBDimension;
import "subgroups.m":SLPToSiegelTrans;
import "elements.m": SiegelTransformToSLP;

Transvection := function( G, a )
    
    if a eq 0 then
        return One( B );
    end if;
    
    dim := BBDimension( G ); F := BBField( G ); 
    gens := BBStandardGenerators( G );
    type := BBType( G );
    S := gens[1]; V := gens[2]; T := gens[3]; 
    D := gens[4]; U := gens[5]; 
    X := gens[6]; Y := gens[10];
    z := PrimitiveElement( F );
    q := #F; 
      
    if BBType( G ) eq "SU" and IsOdd( q ) then
        q0 := Floor( Sqrt( q ));
        ex := Log( z^(q0+1), a*z^-Floor( (q0+1)/2 ));
        return B.3^B.4^-ex;
    elif BBType( G ) eq "SU" and IsEven( q ) then
        q0 := Floor( Sqrt( q ));
        ex := Log( z^(q0+1), a );
        return B.3^B.4^-ex;
    end if;
    
    // G is symplectic
    
    ex := exists( ns ){ x : x in [0..(#F-1)/2] | 
                      IsOdd( Log( z, z^0+z^(2*x) ))};
    assert ex;

    T1 := T; T2 :=T^D^-ns*T; 
    WT1 := B.3; WT2 := B.3^B.4^-ns*B.3;
    a1 := 1; a2 := 1+z^(2*ns); exa2 := Log( z, a2 );
    ex := Log( z, a );
    
    if IsEven( ex ) then
        return WT1^B.4^Floor((-ex/2));
    else
        return WT2^B.4^Floor((-ex+exa2)/2);
    end if;
    
end function;
    
        
IsZeroEntry := function( G, g )
  
    gens := BBStandardGenerators( G );
    S := gens[1]; T := gens[3]; 

    Q := T^S;
    
    return Q^(Q^g) eq Q;
end function;
    
Tf1aw := function( G, a )
    
    if a eq 0 then
        return One( B ), 0;
    end if;
    
    F := BBField( G );
    q := #F; q0 := Floor( Sqrt( q ));
    z := PrimitiveElement( GF( q )); 
    z0 := PrimitiveElement( GF( q0 ));
    
    if IsEven( q ) then
        x1e1f1 := (Trace (z, GF(q0)))^-1*z;
        x2wf1 := z^-(q0-1);
    else
        x1e1f1 := -1/2;
        x2wf1 := -z^-(q0-1);
    end if;

      
    V, f := VectorSpace( GF( q ), GF( q0 ));
    a1 := One( GF( q ));        
    a2 := z^(q0-1);
    
    m := Eltseq( a1@f ); m := m cat Eltseq( a2@f );
    m := GL( 2, q0 )!m;
    
    v := (a@f)^(m^-1); 
    
    if v[2] eq 0 then
        return B.8^B.10^Log( z0^-1, v[1] ), 
               x1e1f1*z0^(-2*Log( z0^-1, v[1] ));
    elif v[1] eq 0 then
        return (B.8^B.4^B.2)^B.10^Log( z0^-1, v[2] ),  
               x1e1f1*z0^(-2*Log( z0^-1, v[2] ));
    else
        return B.8^B.10^Log( z0^-1, v[1] )*(B.8^B.4^B.2)^B.10^Log( z0^-1, v[2] ), 
               x1e1f1*z0^(-2*Log( z0^-1, v[1] ))+
               x1e1f1*z0^(-2*Log( z0^-1, v[2] ))+
               z0^-Log( z0^-1, v[1] )*x2wf1*z0^-Log( z0^-1, v[2] );
    end if;
    
end function;
    
        
EntriesOfRootElementBBSpSU := function( G, g : 
                                  GetWE1Entry := false, 
                                  GetLastEntry := false,
                                  OffSet := 0 )
    
    dim := BBDimension( G ); F := BBField( G ); 
    gens := BBStandardGenerators( G );
    type := BBType( G );
    S := gens[1]; V := gens[2]; T := gens[3]; 
    D := gens[4]; U := gens[5]; 
    X := gens[6]; Y := gens[10];
    
    R0 := X^(S^V)*T^-1;
    T0 := T^V;
        
    CONJ := V*U;
    
    z := PrimitiveElement( F ); list := [];
    alpha := z^Floor((Sqrt( #F )+1)/2);
    q := #F; 
    if BBType( G ) eq "SU" then
       q0 := Floor( Sqrt( q ));
   end if; 
    
   if BBType( G ) eq "Sp" then
        DD := D^-1;
    elif BBType( G ) eq "SU" and IsEven( dim ) then
        DD := D^V^-1;
    elif BBType( G ) eq "SU" and IsOdd( dim ) then
        DD := D^-1;
    end if;
    
    R0 := X^(S^V)*T^-1;
    
    for i in [1..(dim-2-( dim mod 2 ))] do
        c := 0; C := ( g, T0 );
        if C ne One( G ) then 
            R := R0;
            repeat
                if c gt q-2 then
                    return false, false;
                end if;
                R := R^DD; c := c+1;
            until C eq R;
            Append( ~list, z^(c+OffSet));
        else
            Append( ~list, F!0 );
        end if;
        
        if i eq Floor( (dim-2)/2 ) then
            CONJ := S^(V^-1);
        elif i eq Floor( (dim-2)/2+1 ) then
            CONJ := (V*U)^-1;
        end if;
        
        R0 := R0^CONJ;
        T0 := T0^CONJ;
        DD := DD^CONJ;
        
    end for;
    
    if BBType( G ) eq "SU" and IsOdd( q ) then
        for i in [Floor((dim-2)/2+1)..dim-2-(dim mod 2 )] do
            list[i] := list[i]*alpha;
        end for;
    end if;
    
    if GetLastEntry then
        
        lambda := 0;
        for i in [1..Floor( dim/2 )-1] do
            if BBType( G ) eq "Sp" then
                lambda := lambda + list[i]*list[dim-1-i];
            elif BBType( G ) eq "SU" then
                lambda := lambda - list[i]*list[dim-1-i-(dim mod 2 )]^q0;
            end if;
        end for;
        
    end if;

    if GetWE1Entry then
        
        X := gens[8];
        X2 := X^(D^V);
        x2 := One( G ); 
        a1 := PrimitiveElement( GF( q0 ))^-1;        
        a2 := z^(q0-1);
        
        found := false;
        
        for i in [1..q0] do

            x1 := One( G );
            for j in [1..q0] do
                
                h := g*x1*x2; 
                if X^h eq X and X2^h eq X2  then
                    if i eq 1 and j eq 1 then
                        aw := 0;
                        found := true;
                        break i;
                    elif i eq 1 then
                        aw := -a1^(j-2);
                        found := true;
                        break i;
                    elif j eq 1 then
                        found := true;
                        aw := -a2*a1^(i-2);
                        break i;
                    else
                        found := true;
                        aw := -a1^(j-2)-a2*a1^(i-2);
                        break i;
                    end if;
                end if;
                
                if j eq 1 then
                    x1 := X;
                else
                    x1 := x1^Y;
                end if;
                
            end for;
            if i eq 1 then
                x2 := X2;
            else
                x2 := x2^Y;
            end if;
            
        end for;
        
        if not found then return false, false; end if;
        
        Append( ~list, aw*z^OffSet );        
        _, b1 := Tf1aw( G, aw*z^OffSet );
        if GetLastEntry then
            lambda := lambda + b1;
        end if;
        
    end if;
    
    if GetLastEntry then 
       list := Insert( list, dim-1-(dim mod 2), lambda );
    end if;

    // we got the entries, now we will get the SLP
    return list;
end function;
    
        
WriteSimpleRootElementAsSLPBBSpSU := function( G, x, pos )
    
    if x eq One( G ) then
        return 0;
    end if;
    
    F := BBField( G ); q := #F;
    _, _, d := IsPrimePower( q );
    gens := BBStandardGenerators( G );
    
    _, P := SLPToSiegelTrans( G : EvaluateSLPs := true );
    c := (pos-2)*d+1;
    
    D := gens[4]^(gens[2]^(pos-1));
    R := P[c];
    count := 0;
    
    while x ne R and count lt q do
        R := R^D;
        count := count + 1;
    end while;
    
    
    if count eq q then
        return 0;
    else
        return PrimitiveElement( F )^count;
    end if;
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
    
    
ClearFirstRowSpSUBB := function( G, g : FirstCall := false )
    
    dim := BBDimension( G ); F := BBField( G ); 
    gens := BBStandardGenerators( G );
    type := BBType( G );
    S := gens[1]; V := gens[2]; T := gens[3]; 
    D := gens[4]; X := gens[6]; Y := gens[10];
    q := #F;
      
    // first we make sure that [1,1] entry non-zero
      
    if FirstCall then  
      
        c := 0;
        CONJ := V;
        
        S1 := One( G ); progS1 := One( B );
        S2 := S; progS2 := B.1;
        for i in [1..Floor( dim/2 )] do
            S1 := S1*S2;
            progS1 := progS1*progS2;
            S2 := S2^V;
            progS2 := progS2^B.2;
        end for;
        
        while IsZeroEntry( G, g*S ) do
            c := c+1;
            if c gt dim-1 then
                return false, false;
            end if;
            if c eq Floor( dim/2 ) then
                CONJ := S1;
            elif c eq Floor( dim/2 )+1 then
                CONJ := V;
            end if;
            g := g*CONJ;
        end while;
    
        if c lt Floor( dim/2 ) then
            progR := B.2^c;
        else
            progR := B.2^-1*progS1*B.2^c;
        end if;
        
    else 
        
        progR := One( B );
        
    end if;
    
    // next we make sure that the [1,dim-1] entry
    // is nonzero
      
    if IsZeroEntry( G, g*V^-1 ) then
        g := g*gens[7];;
        progR := progR*B.7;
    end if;

    prog, z := ClearTopRightEntryBB( G, g );
    if Category( prog ) eq BoolElt then return false, false, 1; end if;
    progR := progR*prog;
    g := g*z;
    
    p1 := X^S;
    p2 := (T^S)^-1;

    Q := (p1^(p2^g)*p1^-1)^S;
    c := 0;
    Q1 := Q;
    
    if BBType( G ) eq "Sp" then 
        DD := D;
    elif BBType( G ) eq "SU" and IsEven( dim ) then
        DD := (D^-1)^(V^-1);
    elif BBType( G ) eq "SU" and IsOdd( dim ) then
        DD := D;
    end if;
    
    while not IsZeroEntry( G, g*Q1*V^-1 ) do
        if c gt q then
            return false, false, 2;
        end if;
        c := c+1;
        Q1 := Q1^DD;
    end while;

    list := EntriesOfRootElementBBSpSU( G, Q : 
                           OffSet := -c, 
			   GetLastEntry := true, 
                           GetWE1Entry := IsOdd( dim ));
    if Category( list ) eq BoolElt then return false, false, 3; end if;
    prog1 := SiegelTransformToSLP( G, list );

    if list[dim-1-dim mod 2] eq 0 then
        pt := One( B );
    elif BBType( G ) eq "Sp" and IsEven( q ) then
        pt := B.3^(B.4^Log( PrimitiveElement( F )^-2, list[dim-1] ));
    else
        pt := Transvection( G, -list[dim-1-(dim mod 2)] );
    end if;
    
    return One( B ), progR*prog1*pt, 
           One( G ), Evaluate2( progR*prog1*pt, gens );
end function;
    
    
    
    

