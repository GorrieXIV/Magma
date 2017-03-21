freeze;

import "../../recog/magma/centre.m" : EstimateCentre;

ConvertType := function (type, result, q)
    if type eq "2D" and result eq <"A", 1, q^2> then return <"2D", 2, q>;
    elif type eq "2D" and result eq <"2A", 2, q> then return <"2D", 3, q>;
    elif type eq "2D" and result eq <"A", 3, q> then return <"D", 3, q>;
    elif type eq "2D" and result eq <"2A", 3, q> then return <"2D", 3, q>;
    elif type eq "D" and result eq <"A", 3, q> then return <"D", 3, q>;
    elif type eq "D" and result eq <"A", 1, q> then return <"D", 1, q>;
    elif type eq "2A" and result eq <"A", 1, q> then return <"2A", 1, q>;
    elif type eq "B" and result eq <"A", 1, q> then return <"B", 1, q>;
    elif type eq "B" and result eq <"A", 3, q> then return <"D", 3, q>;
    elif type eq "B" and result eq <"C", 2, q> then return <"B", 2, q>;
    elif type eq "C" and result eq <"A", 1, q> then return <"C", 1, q>;
    else return result;
    end if;
end function;

MatrixBlocks := function (G, g)
    if Type (G) eq GrpPerm or IsIrreducible (G) then return [g], true; end if;
    CF := G`CompositionFactors;
    COB := G`ChangeOfBasis;
    F := BaseRing (G);
    d := Degree (G);
    e := [* *];
    I := COB * g * COB^-1;
    offset := 0;
    for i in [1..#CF] do
        k := Dimension (CF[i]);
        block := ExtractBlock (I, offset + 1, offset + 1, k, k);
        flag := Determinant(block) eq 0;
        if flag then
	    I := Identity(GL( k, F));
            return [I], false;
        end if;
        e[i] := GL (k, F) ! block;
        offset +:= k;
    end for;
    return e, true;
end function;

// choose smallest section of X having faithful action
// Optional parameter turns off the check that the section has LieType = type.
SmallestFaithful := function (X, type, string : CheckType := true)
    if Type (X) eq GrpPerm then return true, X, 1, [X]; end if;
    d := type[2];
    q := type[3];
    F := GF (q);
    p := Characteristic (F);
    if type eq < "A", d, q> then
        o := Gcd( d + 1, q-1);
    elif type eq <"C", d, q> then
        o := Gcd (2, q - 1);
    elif d in {2, 4, 6} and type eq < "2A", d, q> then 
        o:= Gcd(d + 1, q+1);
    elif type eq <"2A", 3, q> then
        if string eq "Omega-" then
    	    o := 1;
        else
	    o := Gcd(4, q+1);
        end if;
    else
        // o:=1;
        return false, X, 1, [X];
    end if;

    ZX := EstimateCentre( X, o);
    actual_o := #ZX;

    S, cob := Sections (X);
    cob := Generic (X) ! cob;
    Deg := [Degree (s): s in S];
    index := [i: i in [1..#Deg]];
    Sort (~Deg, ~perm);
    index := index^perm;
    for i in index do
        if Degree (S[i]) eq 1 then continue; end if;
        if Degree (S[i]) le 4 and p le 7 then
            prime := LieCharacteristic( S[i] : Verify := false);
            if type eq <"A", 1, 7> then
                good:= prime in {2, 7};
            else
                good:=prime eq p;
            end if;
            if not good then continue; end if;
        end if;
        if CheckType then
            flag, result := LieType (S[i], p);
        else
            flag :=true;
            result := type;
        end if;
        if flag then
            value := ConvertType (type[1], result, q);
            if value eq type then
                if o gt 1 then
                    Z := EstimateCentre (S[i], o);
                else
                    Z := sub< S[i] | >;
                end if;
                // if #Z eq o then
                if #Z eq actual_o then
                    return true, S[i], i, S;
                // else
                //   "bad section";
                end if;
            end if;
        end if;
    end for;
    //  possible that no section is recognised to be faithful
    return false, X, 1, [X];
end function;

GetType := function(string, d, q)
    if string eq "Sp" then
        type := <"C", (d div 2), q>;
    elif string eq "SU" then
        type := <"2A", d - 1, q>;
    elif string eq "SL" then
        type := <"A", d - 1, q>;
    else 
        //string must be Omega/Omega+-
        if IsOdd(d) then 
            //string must be Omega
            hold := (IsOdd(q) and (d gt 5)) select "B" else "C";
            type := <hold, (d-1) div 2, q>;
        else 
            if string eq "Omega-" then
                if d eq 6 then 
                    type := <"2A", 3, q>;
                else 
                    type := <"2D", d div 2, q>;
                end if;
            else
                //string must be Omega+
                if d eq 6 then
                    type := <"A", 3, q>;
                else
                    type := <"D", d div 2, q>;
                end if;
            end if;
        end if;
    end if;
    return type;
end function;

RecogniseSection := function(G, string, d, q: MapsOnly := true, RS := true)
    if Type(G) eq GrpPerm then
        f,a,b,c,d := ClassicalConstructiveRecognition(G,string,d,q);
        return f,a,b,c,d, _, _;
    end if;

    type := GetType(string, d, q);
    f, GG, secnum, sections := SmallestFaithful(G, type, string);

    if string in {"SL", "SU", "Sp"} and f eq false then
       return false, _, _, _, _, _, _; 
    end if;
    
    dim := d;
    GG := f select GG else G;

    //addition for special handling of Sp4
    if RS and string eq "Sp" and d eq 4 then 
       ff,aa,bb,cc,dd, EE, WW := RecogniseSp4 (GG, q);
    else
       ff,aa,bb,cc,dd, EE, WW := ClassicalConstructiveRecognition(GG, string, d, q);
    end if;
    //end of addition

/* 
if string eq "Sp" and d eq 4 then 
JJ := sub<GL(4, q) | [aa (GG.i): i in [1..Ngens (GG)]]>;
o4 := sub< Generic(JJ) | [JJ.i : i in [1..Ngens(JJ)-1]]>;
// "TEST?", LMGCompositionFactors (o4);
"IRRED TEST?", IsIrreducible (o4);
end if;
*/

    if not ff then return false, _, _, _, _, _, _; end if;
    if not f then 
      maps := <aa,bb,cc,dd,EE,WW>;
      G`RecognitionMaps := maps;
      return ff,aa,bb,cc,dd, EE, WW; 
    end if;

    Gens := [G.i : i in [1..Ngens(G)]];
    mb := map< Generic(G) -> Generic(GG) | x :-> MatrixBlocks(G, x)[secnum]>;
    a := map< Generic(G) -> Codomain(aa) | x :->
      ((MatrixBlocks(G, x)[secnum]) @ Function(aa)) >;
    b := map< Domain(bb) -> Generic(G) | x :->
      Evaluate((x @ bb) @ Function(cc), Gens)>;
    c := map< Generic(G) -> Codomain(cc) | x :->
      ((x @ mb) @ Function(cc))>;
    d := map< Domain(dd) -> Generic(G) | w :->
      Evaluate(w, Gens) >;

    if MapsOnly then 
       maps := <a,b,c,d>;
       G`RecognitionMaps := maps;
       return true, a, b, c, d; 
    end if;

    E := ClassicalStandardGenerators (string, dim, q);
    H := sub<Universe (E) | E>;

    if string ne "SL" then tr := TransformForm (H); E := E^tr; end if;
    
    E := [Function (b)(e): e in E];
    W := [Function (c)(e): e in E];
    WG := WordGroup (G);
    W := Evaluate (W, [WG.i: i in [1..Ngens (WG)]]);
    maps := <a,b,c,d,E,W>;
    G`RecognitionMaps := maps;
    return true, a, b, c, d, E, W;
end function;
