freeze;

// verbose modes
declare verbose evenSX, 5;
declare verbose evenSXcpu, 3;
declare verbose evenSXLT, 3;
SetVerbose("evenSX",0);
SetVerbose("evenSXcpu",0);
SetVerbose("evenSXLT",0);


// attributes
AddAttribute(GrpMat,"initialised");
AddAttribute(GrpMat,"type");          //string "SL","SU","O+","O-","Sp"
AddAttribute(GrpMat,"natParams");     //tupel <type,d,q,p>
AddAttribute(GrpMat,"cob");           //mat, for nat rep
AddAttribute(GrpPerm,"initialised"); 
AddAttribute(GrpPerm,"type");         //type of overgroup
AddAttribute(GrpPerm,"natParams");
AddAttribute(GrpPerm,"cob");           //mat, for nat rep


forward SXEIsOmegaPlus4;
forward SXESections;
forward SXERandomWord;
forward SXEWhatPPD;


// some global flags
SXEonlyBlack := false;  //uses only black algorithms, no call of nat-rep code

import "../../../classical.m": ClassicalConstructiveRecognitionNatural;
import "../odd/base-omega.m": IsOmegaPlus4,MyRecogniseOmegaMinus6, MyRecogniseOmegaPlus6;
import "../../../../recog/magma/centre.m":EstimateCentre;
import "../../../../recog/magma/node.m": ERROR_RECOGNITION;
import "../../basics.m": RecognitionError;




/*********************************************************************/
/* returns SLPs (wrt std gens) of images of std gens under graph aut
/***********************************************************************/
SXESp4GraphAutSLPs := function(q)

  //from Derek
   K:=GF(q); 
   w:=PrimitiveElement(K);
   ims:= [ GL(4,q) |
       [ 0,0,1,0,0,0,0,1,1,0,0,0,0,1,0,0 ],
       [ 0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1 ],
       [ 1,0,1,0,0,1,0,0,0,0,1,0,0,1,0,1 ],
       [ w,0,0,0,0,w^-1,0,0,0,0,w^-1,0,0,0,0,w ],
       [ 0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1 ],
       [ 1,0,0,0,0,1,0,0,0,0,1,1,0,0,0,1 ]
   ];   

   gens := ClassicalStandardGenerators("Sp",4,q);
  
   W   := SLPGroup (#gens);
   wrd := [];
   for i in ims do
      flag,w := ClassicalRewriteNatural("Sp",One(GL(4,q)),i);
      if not flag then error "ClassicalRewriteNatural failed"; end if;
      w      := Evaluate (w, [W.i: i in [1..Ngens (W)]]);
     Append(~wrd,w);
   end for;
   return wrd;
end function;



/*********************************************************************/
/* returns SLPs (wrt std gens) of images of std gens under triality
/***********************************************************************/
SXEOp8GraphAutSLPs := function(q)

  //from Derek
   K:=GF(q); 
   w:=PrimitiveElement(K);
   ims := [ GL(8,q) |
      [0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,
      0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,
      0,0,0,0,1,0,0,0,0,0,0,0,0,1],
      [1,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,
      0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,
      0,0,0,0,1,0,0,0,0,0,0,0,0,1],
      [w,0,0,0,0,0,0,0,0,w^-1,0,0,0,0,0,0,0,0,w,0,0,
      0,0,0,0,0,0,w^-1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,
      0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1],
      [1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,
      0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,
      0,0,-1,0,0,0,0,0,0,0,0,-1,0,0],
      [1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,
      0,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,0,0,0,
      0,0,0,0,1,0,0,0,0,0,0,-1,0,1],
      [1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,
      0,0,1,0,0,0,0,0,0,0,0,w,0,0,0,0,0,0,0,0,w^-1,0,0,
      0,0,0,0,0,0,w^-1,0,0,0,0,0,0,0,0,w],
      [1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,
      0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,
      0,0,0,0,1,0,0,0,0,0,0,0,0,1],
      [0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,0,0,0,0,
      0,0,-1,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,
      0,0,0,0,0,1,0,0,0,0,0,0,1,0]
  ];

   gens := ClassicalStandardGenerators("Omega+",8,q);
   wrd  := [**];
   W    := SLPGroup (#gens);
   wrd := [];
   for i in ims do
      flag,w := ClassicalRewriteNatural("Omega+",One(GL(8,q)),i);
      if not flag then error "ClassicalRewriteNatural failed"; end if;
      w      := Evaluate (w, [W.i: i in [1..Ngens (W)]]);
     Append(~wrd,w);
   end for;
   return wrd;

end function;






/*********************************************************************/
/* input: field F and two primitive elts a, b
/* output: power p^i s.t. a^(p^i)=b where p=char(F)
/***********************************************************************/
SXEadjustElts := function(F,a,b)  
   p := Characteristic (F);
   e := Degree (F);
   for i in [0..e - 1] do
       power := p^i;
       x := a^(power);
       if x eq b then return power; end if;
   end for;
   error "SXEadjustElts: Did not fix prim elts";
end function;

/*********************************************************************/
/* input: matrix g and prime p
/* output: is order of g divisible by p
/*********************************************************************/
SXEIspElement := function (x, p)

   MultiplicativeUpperbound := function (x)
      F := BaseRing (Parent (x));
      p := Characteristic (F);
      q := #F;
      m := MinimalPolynomial (x);
      facs := Factorisation (m);
      degs := [Degree (facs[i][1]): i in [1..#facs]];
      alpha := Maximum ([facs[i][2]: i in [1..#facs]]);
      beta := Ceiling (Log (p, alpha));
      bound := LCM ([q^i - 1: i in degs]) * p^beta;
      return bound;
   end function;

   bound := MultiplicativeUpperbound (x);
   /* largest odd divisor of upper bound */
   k := 0; while bound mod p eq 0 do k +:= 1; bound div:= p; end while;
   /* obtain element of p-power order by powering up odd part */
   if k gt 0 then y := x^bound; else y := x^0; end if;
   return IsIdentity (y) eq false;
end function;



/*********************************************************************/
/* input: matrix g and prime p
/* output: is order of g divisible by p 
/*         CAREFUL: returns true if base field larger than 255
/*                  because we in application we 
/*                  suppose elt will be of p-prime order
/*********************************************************************/
SXEPrimeOrderElement := function (x,p : new := true)
   t := Cputime();
   F := BaseRing(Parent(x));
   if #F ge 256 then return false; end if;
   if new then res := SXEIspElement(x,p); else res := PrimeOrderElement(x,p); end if;
   return res,Cputime(t);
end function;


/*********************************************************************/
/* input: g matrix involution
/* output: base change matrix b such that b*g*b^-1 has std form 
/*********************************************************************/
SXEBaseChangeInvolution := function(g)
    F     := BaseRing(Parent(g));   
    MA    := MatrixAlgebra(F,Nrows(g));
    h     := MA ! g + Identity(MA);
    im    := Basis(RowSpace(h));
    preIm := Solution(h,im);
    preIm := [Eltseq(preIm[i]) : i in [#preIm..1 by -1]]; 
    ker   := ExtendBasis(im,Nullspace(h));
    ker   := [Eltseq(ker[i]) : i in [#ker..1 by -1]];   
    B     := preIm cat ker;
return  GL(Nrows(g),F)!B;
end function;


/*********************************************************************/
/* input: group G
/* output: is G initialised  matrix grp in nat rep? 
/*********************************************************************/
SXEIsNatRep := function(G)
    assert G`initialised;
    assert assigned G`natParams;
    nP := G`natParams;
    if nP[1] eq "SU" then
       return Type(G) eq GrpMat and Degree(G) eq nP[2] and #BaseRing(G) eq nP[3]^2;
    elif nP[1] eq "O-" and Degree (G) eq 4 then
    // EOB cater for Omega^-(4, q) having two non-conjugate copies in GL(4, q): 
    // second is absolutely reducible, can be written as 2x2 over GF(q^2) 
       return Type(G) eq GrpMat and ClassicalType (G) cmpeq "Omega-";
    else
       return Type(G) eq GrpMat and Degree(G) eq nP[2] and #BaseRing(G) eq nP[3];
    end if;
end function;


/*********************************************************************/
/* Input:  matrix group G
/* Output: true if group contains SL in natural rep
/*********************************************************************/
SXEIsLinearGroupNatRep := function(G)
   if IsAbsolutelyIrreducible(G) eq false then return false; end if;
   if Degree(G) gt 1 then ;
       t := IsLinearGroup(G); 
       if t cmpeq true then G`type := "SL"; end if;
       return t;
   else return true; 
   end if;
end function;


/*********************************************************************/
/* Input:  matrix group G  
/* Output: true if group contains SU in natural rep
/*********************************************************************/
SXEIsUnitaryGroupNatRep := function(G)
   if IsAbsolutelyIrreducible(G) eq false then return false; end if;
   if Degree(G) eq 1 then 
       G`type := "SU";
       return true; 
   else 
       t := IsUnitaryGroup(G); 
       if t cmpeq true then G`type := "SU"; end if;
       return t;
   end if;
end function;


/*********************************************************************/
/* Input:  matrix group G  
/* Output: true if group contains O+ in natural rep
/*********************************************************************/
SXEIsOmegaPlusGroupNatRep := function(G)
    if IsAbsolutelyIrreducible(G) eq false then return false; end if;
    if Degree(G) eq 1 then return true; end if;
    erg := IsOrthogonalGroup(G);
    if not erg then return false; end if;
    flag, type, form := OrthogonalForm(G);
    if flag and type eq "orth+" then 
        G`type := "O+";
        return true;
    else
        return false;
    end if;
end function;


/*********************************************************************/
/* Input:  matrix group G  
/* Output: true if group contains O+ in natural rep
/*********************************************************************/
SXEIsOmegaMinusGroupNatRep := function(G)
    if IsAbsolutelyIrreducible(G) eq false then return false; end if;
    if Degree(G) eq 1 then return true; end if;
    erg := IsOrthogonalGroup(G);
    if not erg then return false; end if;
    flag, type, form := OrthogonalForm(G);
    if flag and type eq "orth-" then
        G`type := "O-";
        return true;
    else
        return false;
    end if;
end function;


/*********************************************************************/
/* Input:  matrix group G  
/* Output: true if group contains Sp in natural rep
/*********************************************************************/
SXEIsSymplecticGroupNatRep := function(G)
    if IsAbsolutelyIrreducible(G) eq false then return false; end if;
    if Degree(G) eq 1 then return true; end if;
    t := IsSymplecticGroup(G);
    if t cmpeq true then G`type := "Sp"; end if;
    return t;
end function;


/*********************************************************************/
/* Input:  matrix group G
/* Output: type of G if it is SL, SU, Sp, O+ or O-
/*         if G`natParams attached, then return these
/*********************************************************************/
SXELieTypeNatRep := function(G : shouldBe := false)
    vprint evenSX, 4: "start SXELieTypeNatRep";
    rnt := Cputime();
    F := BaseRing(G);
    d := Degree(G);
    p := Characteristic(F);

    if assigned G`natParams then return G`natParams; end if;

    if Degree(G) eq 2 and #F eq 2 and SXEIsLinearGroupNatRep(G) then
        vprint evenSXcpu,3 : "runtime SXELieTypeNatRep is",Cputime(rnt);
        vprint evenSX, 4: "end SXELieTypeNatRep";
        return <"SL",d,#F,p>;
    end if;
    if Degree(G) eq 2 and #F eq 4 and SXEIsUnitaryGroupNatRep(G) then
        vprint evenSXcpu,3 : "runtime SXELieTypeNatRep is",Cputime(rnt);
        vprint evenSX, 4: "end SXELieTypeNatRep";
        return <"SU",d,Isqrt(#F),p>;
    end if;

  //if we expect a certain group then check more thoroughly 
    if not shouldBe cmpeq false then howoften := 3; else howoften := 1; end if;
    res := false;
    for j in [1..howoften] do
       if RecognizeClassical(G) then
           t := ClassicalType(G);
           if t cmpeq false and shouldBe cmpeq false then 
              vprint evenSXcpu,3 : "runtime SXELieTypeNatRep is",Cputime(rnt);
              return false; 
           end if;
           if   t eq "linear"          then G`type := "SL"; res := <"SL",d,#F,p>;
           elif t eq "symplectic"      then G`type := "Sp"; res := <"Sp",d,#F,p>;
           elif t eq "unitary"         then G`type := "SU"; res := <"SU",d,Isqrt(#F),p>;
           elif t eq "orthogonalminus" then G`type := "O-"; res := <"O-",d,#F,p>;
           elif t eq "orthogonalplus"  then G`type := "O+"; res := <"O+",d,#F,p>;
           end if;
           if not t cmpeq false then
              if shouldBe cmpeq false or shouldBe cmpeq res then return res; 
              end if;
           end if; 
       end if;
       if howoften ge 2 then 
          vprint evenSX, 4: "   SXELieTypeNatRep: another try";
       end if;
    end for;
    vprint evenSXcpu,3 : "runtime SXELieTypeNatRep is",Cputime(rnt);
    vprint evenSX, 4: "end SXELieTypeNatRep";
    return false;
end function;



/*********************************************************************/
/* input: a group G
/* output: LieType of G in form <t,d,q,p> where t in "SL","SU", "Sp","O+","O-"
/*         or false
/* 
/* NatRep   = true if group is known to be in nat rep
/* shouldBe = <t,d> if group 'should be' of type t and degree d
/* char     = characteristic of group
/* NatRep   = group is known to be in nat rep
/* q        = field size, for SXEIsOmegaPlus4
/********************************************************************/
 SXELieType := function (GG : char := false, shouldBe := false, NatRep := false, q:=0)


   if assigned GG`natParams then return GG`natParams; end if;
   if NatRep then return SXELieTypeNatRep(GG :shouldBe := shouldBe); end if;  
   if shouldBe cmpeq <"O+",4> then  return SXEIsOmegaPlus4(GG:q:=q); end if;

   if not shouldBe cmpeq false then
      if Type(GG) eq GrpMat then
         if shouldBe eq <"SL",2,4,2> and not LMGOrder(GG) eq 60 then 
            return false; 
         end if;
      else 
        if shouldBe eq <"SL",2,4,2> and not #GG eq 60 then                                                                                    
           return false;                                                           
         end if;
      end if;
   end if; 

   vprint evenSX, 4: "start SXELieType";
   rnt := Cputime();

 //if we have matrix group, first check if all sections are 'identical';
 //if not, then we can dismiss this group immediately
   G := GG;
   if Type(GG) eq GrpMat and not q eq 0 then

     //simple test via ppd structure whether shouldBe can be possible
       if not shouldBe cmpeq false then
           dw := shouldBe[2];
           qw := shouldBe[3];
           tw := shouldBe[1];
           pw := shouldBe[4];
           if tw in ["Sp","O-","SL"] then max := dw; 
           elif tw eq "SU" then max:=2*dw;
           elif tw in ["O+"] then max := dw-2;
           end if;

         //need this in case the group is not what we expected
           myp := pw^Maximum(dw,Degree(GG));

           if tw in ["O+","Sp"] then nr := 20; else nr := 10; end if;
           for i in [1..nr] do
              g := SXERandomWord(GG);
              ppd := SXEWhatPPD(g^myp,qw);
              if ppd gt max then 
                 vprint evenSXcpu,3 : "runtime SXEInitGroup is",Cputime(rnt);
                 vprint evenSX, 3: "end SXEInitGroup";
                 vprint evenSXLT, 1:"runtime LieType (return ppd-check false)",Cputime(rnt);
                 return false; 
              end if; 
           end for;
       end if;

       S    := SXESections(G);
       d    := Degree(G);
       F    := BaseRing(G);
       CF   := G`CompositionFactors;
       COB  := G`ChangeOfBasis;
       COBi := COB^-1;

       getBlocks := function (G, g)
          e := [* *];
          I := COB * g * COBi;
          offset := 0;
          for i in [1..#CF] do
             k := Dimension (CF[i]);
             e[i] := GL (k, F) ! ExtractBlock (I, offset + 1, offset + 1, k, k);
             offset +:= k;
          end for;
       return e;
       end function;

       if not #S eq 1 then
          Limit := 0;
          repeat
             Limit +:= 1;
             g := SXERandomWord(G);
             B := getBlocks (G, g);
             B := [* b : b in B | Degree (b) gt 1 *];
             O := {Order (b): b in B};

             if #B eq 0 or not (Gcd(O) in O) or not IsCentral(G,g^Minimum(O)) then 
                vprint evenSXcpu,3 : "runtime SXEInitGroup is",Cputime(rnt);
                vprint evenSX, 3: "end SXEInitGroup";
                vprint evenSXLT, 1:"runtime LieType (return quick-check false)",Cputime(rnt);
                vprint evenSXLT, 1:"nr of tries until found bad guy",Limit;
                return false; 
             end if;
          until Limit eq 5;
      end if;
      
      f := exists(i){i : i in S | Degree(i) ge 2};
      if not f then error "SXELieType: only degree 1?!"; end if;
      G := i;

   end if;

   if char cmpeq false and not assigned G`natParams then
       error "SXELieType does not know characteristic";
   end if;
   if not char cmpeq false then p := char; else char := G`natParams[4]; end if;
   cnt := 0;
   repeat
       if cnt ge 1 then
           vprint evenSX, 2: "SXELieType verify: had to do a second test";
       end if;
       f, t := LieType(G,p);
       if f eq false then 
           vprint evenSXcpu,3 : "runtime SXELieType is",Cputime(rnt);
           vprint evenSX, 4: "end SXELieType";
           vprint evenSXLT, 1:"runtime LieType (return false)",Cputime(rnt);
           return false; 
       end if;
       if t[1] eq "A" then
           t[1] := "SL"; t[2] := t[2]+1;
       elif t[1] eq "2A" then
           t[1] := "SU"; t[2] := t[2]+1;
       elif t[1] eq "C" then
           t[1] := "Sp"; t[2] := 2*t[2];
       elif t[1] eq "2D" then
           t[1] := "O-"; t[2] := 2*t[2];
       elif t[1] eq "D" then
           t[1] := "O+"; t[2] := 2*t[2];
       end if;
       Append(~t,p);
       if shouldBe cmpeq false then
           vprint evenSXcpu,3 : "runtime SXELieType is",Cputime(rnt);
           vprint evenSX, 4: "end SXELieType";
           vprint evenSXLT, 1:"runtime LieType; found",t,Cputime(rnt);
           return t;
       end if;
       cnt := cnt + 1;
    until (f and t cmpeq shouldBe) or cnt ge 1; ///WHY THIS TEST?!?
    vprint evenSXcpu,3 : "runtime SXELieType is",Cputime(rnt);
    if not (f and t cmpeq shouldBe) then 
        vprint evenSXLT, 1:"runtime LieType; found",t,"but returned false",Cputime(rnt);
        return false; 
    end if;
    vprint evenSX, 4: "end SXELieType";
    vprint evenSXLT, 1:"runtime LieType; found",t,Cputime(rnt);
    return t;
end function;


/*********************************************************************/
/* Input:  matrix group G (black)
/* Output: G with the following flags:
/*         G`UserGenerators
/*         G`SLPGroup      - on U=UserGens
/*         G`cob           - change of base mat, id(G) (nat rep)
/*         G`UserWords     - Ugen[i]=COB*Evaluate(w,OrigGens)*COB^-1
/*                           for w=UserWord[i])
/*         G`RandomProcess - on G`SLPGroup with UserGens(G)
/*         G`type          - type of parent group
/*         G`natParams     - parameters of group in natural rep.
/*                           in form <type,d,q,p>
/*********************************************************************/
SXEInitGroup := procedure(G : UserWords :=[],
                              natParams := false,
                              type      := false)

    vprint evenSX, 3: "start SXEInitGroup";
    rnt := Cputime();
    if not assigned G`cob then G`cob := One(G); end if;
    if not assigned G`UserGenerators then
        U := [Generic(G)!G.i : i in [1..Ngens(G)]];
        G`UserGenerators := U;
        G`SLPGroup := WordGroup (G);
    end if;
    U := UserGenerators(G);
    if not UserWords cmpeq [] then G`UserWords := UserWords; end if;
    if not assigned G`SLPGroup then G`SLPGroup := SLPGroup(#U); end if;
    B := G`SLPGroup;
    if not assigned G`UserWords then
        G`UserWords:=[B.i:i in [1.. #U]];
    end if;
    if not assigned G`RandomProcess then
       G`RandomProcess := RandomProcessWithWords(G:
                                             WordGroup  := G`SLPGroup,
                                             Generators := U);
    end if;
    if not assigned G`natParams and not natParams cmpeq false then
        G`natParams := natParams;
    end if;

    if Type(type) cmpeq Tup then
       
        G`type      := type[1];
        if #type eq 3 then tmp := Factorisation(type[3])[1][1]; else tmp:=type[4]; end if;
        G`natParams := <type[1],type[2],type[3],tmp>;
    elif not assigned G`type and not type cmpeq "no" then 
        if Type(type) eq MonStgElt then
            G`type := type;
        elif assigned G`natParams then
            G`type := G`natParams[1];
        else
            p    := LieCharacteristic(G);
            t := SXELieType(G : char := p);
            if t cmpeq false then  
                error "SXEInitGroup: Cannot determine Lie type of group";
            end if;
            if not t[1] in ["SL","SU","Sp","O+","O-"] then
                error "SXEInitGroup: type of group not determined";
            end if;
            G`natParams := <t[1],t[2],t[3],p>;
            G`type      := t[1];
        end if;
    end if;
    G`initialised := true;
    vprint evenSXcpu,3 : "runtime SXEInitGroup is",Cputime(rnt);
    vprint evenSX, 3: "end SXEInitGroup";
end procedure;


/*********************************************************************/
/* Input:   initialised group G
/* Output:  random g in G and corresponding SLP w in G`SLPGroup
/*********************************************************************/
SXERandomWord := function( G )
    if not assigned G`RandomProcess then SXEInitGroup(G : type := "no"); end if;
    return Random(G`RandomProcess);
end function;


/*********************************************************************/
/* Eamonn's function to detect O+(4) (black)
/*
/* LieTest true: apply LieType to input
/* Perfect true: assume input is perfect
/*********************************************************************/
SXEIsOmegaPlus4 := function (G : p := 2, LieTest := true, Perfect := false, Limit := 10, q:=0)
  
   vprint evenSX, 4: "start SXEIsOmegaPlus4";
   rnt := Cputime();
   if not IsProbablyPerfect (G) then return false; end if;
   res := IsOmegaPlus4(G,GF(q));
   vprint evenSXcpu,3 : "runtime SXEIsOmegaPlus4 is",Cputime(rnt);
   vprint evenSX, 4: "end SXEIsOmegaPlus4";
   if res cmpeq false then return res; else return <"O+",4,q,p>; end if;
end function;


/*********************************************************************/
/* Input:  matrix and list of indices
/* Output: block of matrix corresponding to index
/*********************************************************************/
SXEExtractBlock := function(g, index)
   E := [];
   if Type(index) eq SetEnum then 
      index := Sort(SetToSequence(index)); 
   end if;
   for i in index do 
      for j in index do Append(~E, g[i][j]); end for;
   end for;
   return GL(#index, BaseRing(Parent(g))) ! E;
end function;



/*********************************************************************/
/* Input:  matrix group and list of indices
/* Output: group generated by submatrices of G
/*         determined by index set action
/*********************************************************************/
SXEExtractGroup := function (G, action )
   U   := UserGenerators(G);
   tmp := GL(#action,BaseRing(G));
   U   := [tmp!SXEExtractBlock(U[i], action): i in [1..#U]];
   B   := sub<tmp | U>;
   if assigned G`UserWords then B`UserWords:=G`UserWords; end if;
   if assigned G`type then B`type:=G`type; end if;
   if assigned G`natParams then B`natParams:=G`natParams; end if;
   B`UserGenerators := U;
   SXEInitGroup(G:type:="no");
   return B;
end function;


/*********************************************************************/
/* Input:  initialised matrix group G (black)
/* Output: copy of G with all flags
/*********************************************************************/
SXECopyGroup := function(G : cob := false)
    if not assigned G`initialised then
        if not assigned G`type then
            SXEInitGroup(G : type := "no");
        else
            SXEInitGroup(G);
        end if;
    end if;
    if not cob cmpeq false then 
       cbinv := cob^-1;
       ugens := [Generic(G)!(cob*u*cbinv) : u in UserGenerators(G)];
    else
       ugens := [Generic(G)!u : u in UserGenerators(G)];
    end if;
    H                := sub<Generic(G) | ugens>;
    H`UserGenerators := ugens;
    H`SLPGroup       := G`SLPGroup;
    H`UserWords      := G`UserWords;
    H`initialised    := true;
    if assigned G`natParams then H`natParams := G`natParams; end if;
    if not cob cmpeq false then
       H`cob := cob*G`cob;
    else
       H`cob := G`cob;
    end if;
    if assigned G`type then H`type := G`type; end if;
    if cob cmpeq false then
       H`RandomProcess  := G`RandomProcess; 
    else
       H`RandomProcess := RandomProcessWithWords(H:
                                                 WordGroup  := H`SLPGroup,
                                                 Generators := ugens);
    end if;
    if not assigned G`type then
       SXEInitGroup(H:type:="no");
    else 
       SXEInitGroup(H);
    end if;
    return H;
end function;




/*********************************************************************/
/* New version of "Sections"
/* time blow up possible, but no memory blow up (?)
/*********************************************************************/
SXEMySections := function(G)
    F := BaseRing(G);
    d := Degree(G);
    if assigned G`CompositionFactors then
        CF  := G`CompositionFactors;
        COB := G`ChangeOfBasis;
    else
        CS, CF, COB          := CompositionSeries(GModule(G));
        G`CompositionFactors := CF;
        G`ChangeOfBasis      := Generic(G)!COB;
    end if;
  
    MatrixBlocks := function(g)
        e  := [* *];  I := COB*g*COB^-1;  off := 0;
        for i in [1..#CF] do
            k    := Dimension(CF[i]);
            e[i] := GL(k,F)!ExtractBlock(I,off+1,off+1,k,k);
            off +:= k;
        end for;
    return e;
    end function;

    U := UserGenerators(G);
    E := [* *];
    for j in [1..#U] do 
        E[j] := MatrixBlocks(U[j]);
    end for; 
    section := [* *];
    for i in [1..#CF] do 
        gens       := [E[j][i]: j in [1..#U]];
        section[i] := sub < GL(Dimension(CF[i]), F) | gens>;
        section[i]`UserGenerators := gens;
        section[i]`SLPGroup := G`SLPGroup; //EXPERIMENTAL FIX!!!
    end for;
    return section;
end function;


/*********************************************************************/
/* USE ALWAYS MYSECTIONS?
/* if not, then time blow-up
/* if so, then memory blow-up (?)
/*********************************************************************/
SXESections := function(G) return SXEMySections(G); end function;



/*********************************************************************/
/* g lies in G with SLP w; f is a factor of the char pol of g
/* returns a power of g which acts trivially on the subspace def by f
/*********************************************************************/
SXETrivialActionOnInvBlock := function(G,g,w,f : trivial := true)
   MA  := MatrixAlgebra(BaseRing(G),Degree(G));
   h   := MA!g;
   B   := Basis(Nullspace(Evaluate(f,h)));
   dim := #B;
   Bim := [i*h : i in B];
   B   := Matrix(Degree(G),&cat([Eltseq(u) : u in B])); 
   mat := &cat([Eltseq(u): u in Solution(B,Bim)]);
   mat := GL(dim,BaseRing(G))!mat;
   if trivial then
       o := Order(mat); //: Proof:=false);
   else
       o := ProjectiveOrder(mat : Proof:=false);//: Proof:=false);
     end if;;
   return g^o, w^o, dim, o, mat;
end function;



/***********************************************************************/
/* H is matrix group with two gens g and h
/* of odd order. Let S = Eig(h,1) meet Eig(g,1)
/* and assume that H is irred on supp(g-1)\oplus supp(h-1)
/* Brings H is block diagonal form
/***********************************************************************/
SXEMakePretty := function(H)
    MA  := MatrixAlgebra(BaseRing(H),Degree(H));
    ug := [MA!u : u in UserGenerators(H)];
    S   := [Eltseq(u) : u in Basis(&meet( [Eigenspace(u,1) : u in ug] ) ) ];
    bas := [Eltseq(u) : u in Basis(&+([Rowspace(u-u^0): u in ug]))] cat S;
    bas := Generic(H)!bas;
    return H^(bas^-1),bas; 
end function;



/*********************************************************************/
/* returns largest ppd value of p-reg elt; Neumann & Praeger p 578) (black)
/* g is semisimple; the black version returns i such that i is the maximal
/* value s.t. g lies in maximal torus containing C_(q^i-1) or C_(q^(i/2)+1)
/*********************************************************************/
SXEWhatPPD := function(g,q)
     vprint evenSX, 5: "start SXEWhatPPD";
     rnt := Cputime();    

     if g^(q-1) eq g^0 then return 1; end if;
 
  //
  //Neumann + Praeger p 578: Psi(e,q)=(q^e-1)/(Product of all ppd(e,q) with multiplicity)
  //
  // (not used in code below yet...)
  //
     ComputePsi := function (e, q)
        if q lt 2 then return false; end if;
        psi := 1;
        phi := q^e - 1;
        primes := PrimeBasis (e);
        for c in primes do
           a := Gcd (phi, q^(e div c) - 1);
           while a gt 1 do
              psi *:= a;
              phi div:= a;
              a := Gcd (phi, a);
           end while;
        end for;
        return psi;
     end function;

   //black-box version, cross char, or different underlying field
     pureBlack := function(g,q)
        i := 2;
        l := q-1;
        g := g^(q-1);
        repeat
           l := Lcm([l,q^i-1]) div l;
           g := g^l;
           if g eq g^0 then 
            //"DONE, found",i; 
              vprint evenSXcpu,3 : "runtime SXEWhatPPD is",Cputime(rnt);
              vprint evenSX, 5: "end SXEWhatPPD";
              return i; 
           end if;
        i := i + 1;
        until false;
     end function;
 
  //mtgrp version (same underlying field)
     grey := function(g,q)
        degs := [Divisors(Degree(el[1])): el in Factorisation(CharacteristicPolynomial(g))];
        degs := &cat(degs);
        degs := degs cat [2*i : i in degs];
        degs := {i : i in degs};
        degs := [i : i in degs | i gt 1];
        Sort(~degs);
        elt  := g;
        dwn  := 1;
        olde := 1;
        if degs eq [] then return 1; end if;
        for e in degs do
           tmp  := [q^i-1 : i in [olde..e-1]];
           if tmp eq [] then tmp := 1; else tmp:=Lcm(tmp); end if; 
           dwn  := Lcm(dwn, tmp);
           new  := (q^e-1) div Gcd(dwn,q^e-1);
           elt  := g^dwn;
           h    := elt^new;
           if not elt eq elt^0 and h eq h^0 then 
              vprint evenSXcpu,3 : "runtime SXEWhatPPD is",Cputime(rnt);
              vprint evenSX, 5: "end SXEWhatPPD";
              return e; 
           end if;
           elt  := h;
           olde := e;
        end for;
        return -1;
   end function;


   if not Type(g) eq GrpMatElt or (Type(g) eq GrpMatElt and not q eq #BaseRing(Parent(g))) then
       return pureBlack(g,q);
   elif Type(g) eq GrpMatElt and q eq #BaseRing(Parent(g)) then
       return grey(g,q);
   end if;
   
end function;




/*********************************************************************/
/* Input:  matrix group G in natural rep, type
/* Output: G^B, B such that G^B respects "normal form"
/*********************************************************************/
SXEConjugateToStandardCopy := function(G, type)   
    F := BaseRing (G);
    q := #F;
    d := Degree (G);
    if assigned G`type then type := G`type; end if;
    origType := type;

    StandardSpForm := function (n, q)
         assert IsEven(n);
         A := MatrixAlgebra(GF(q), 2);
         J := A![0,1,1,0];
         m := n div 2;
         return DiagonalJoin([J: i in [1..m]]);
    end function;

    StandardSUForm := function (n, q)
        A := MatrixAlgebra(GF(q^2), 2);
        J := A![0,1,1,0];
        m := n div 2;
        form := DiagonalJoin ([J: i in [1..m]]);
        if IsOdd (n) then
           a := Identity (MatrixAlgebra (GF(q^2), 1));
           form := DiagonalJoin (form, a);
        end if;
        return form;
    end function;
 
    StandardOmegaPlusForm := function (n, q)
        assert IsEven(n);
        A := MatrixAlgebra(GF(q), 2);
        J := A![0,1,0,0];
        m := n div 2;
        return DiagonalJoin([J: i in [1..m]]);
    end function;
     
    StandardOmegaMinusForm := function (n, q)
        elt := ClassicalStandardGenerators("Omega-",n,q);
        f,form := QuadraticForm(sub<GL(n,q)|elt>);                           
        assert f;
        return form;
    end function;

 //StandardOmegaMinusForm := function (n, q)
 //     A      := MatrixAlgebra(GF(q),2);
 //     J      := A![0,1,0,0];
 //     m      := (n div 2) - 1;
 //     form   := DiagonalJoin([J : i in [1..m]]);
 //     gam    := GF(q^2).1;
 //     K      := A![1,gam+gam^q,0,gam^(q+1)];
 //     form   := DiagonalJoin(form,K);
 //     return form;
 // end function;

    if type eq "SU" then 
       flag, form := UnitaryForm(G);
       assert flag;
       standard := StandardSUForm(d, Isqrt (q));
       m        := Id(G);
    elif type eq "Sp" then 
       flag, form := SymplecticForm(G);
       standard   := StandardSpForm(d, q);
       m          := Id(G);
    elif type eq "O+" then
       flag, form, t := QuadraticForm(G);
       assert flag and t eq "orthogonalplus";
       standard      := StandardOmegaPlusForm(d,q); 
    elif type eq "O-" then
       flag, form, t := QuadraticForm(G);
       assert flag and t eq "orthogonalminus";
       standard      := StandardOmegaMinusForm(d,q); 
    else
       error "Type incorrect for ConjugateToStandardCopy";
    end if;
  
    if form eq standard then 
        return G, Identity(G), Identity(G); 
    end if;
 
    if   type eq "SU" then type := "unitary"; 
    elif type eq "Sp" then type := "symplectic"; 
    elif type eq "O+" then type := "orthogonalplus";
    elif type eq "O-" then type := "orthogonalminus";
    end if;
    
    x     := TransformForm(form, type);
    y     := TransformForm(standard, type)^-1;
    cb    := x*y; 
    cbinv := cb^-1;
    K     := SXECopyGroup(G : cob:=cbinv);  
    return K,cbinv,y;
end function;






/*********************************************************************/
/* the function SXEgetElementForSLBlack(G) constructs an   
/* element of G which, in nat rep, has a large 1-eigenspace and usually
/* an order divisible by a certain ppd.
/*********************************************************************/
SXEgetElementForSLBlack := function(G : range := [])
    vprint evenSX, 5: "start SXEgetElementForSLBlack";
    rnt := Cputime();
    d := G`natParams[2];  q := G`natParams[3];  p := G`natParams[4];
    a := Floor(Log(p,q));

    cnt  := 0;
    done := false;
   
    if range cmpeq [] then 
        ess  := [i : i in [1..d] | i ge (2*d/3) and 
                                   i le 5*d/6 and not i mod (d-i) eq 0];
    else
        ess := [u : u in {d-(r div 2) : r in range} | not u mod (d-u) eq 0 ];
    end if;

    if d eq 8 then  ess := [3,6];
    elif d eq 10 then ess := [5,7];
    elif d eq 12 then ess := [5,10];
    elif d eq 16 then ess := [7,9,11];
    elif d in [5,6] then ess := [3];
    end if;

    if q in [2,3] then
       if d eq 20 and q eq 2 then ess := [11]; 
       elif d eq 16 and q eq 2 then ess := [11];
       elif d eq 10 and q eq 3 then ess := [7]; 
       end if;
    end if;

  //make sure that we don't look for ppd of 2^6-1, which does not exist.
    if q eq 2 then ess := [i : i in ess | not d-i eq 6 and not i eq 6]; end if;

    if ess eq [] then error "SXEgetElementForSLBlack: empty list ess"; end if;
    
    myp := p^(1+Ilog(p,2*d));
    repeat
        cnt +:= 1;
        if cnt mod (100*d) eq 0 then "SXEgetElementForSLBlack: nr of constructed elts",cnt; end if;
        if IsOdd(q) then
           repeat g, w := SXERandomWord(G); g := g^myp; w := w^myp; until not g eq g^0 and not SXEPrimeOrderElement(g,p);
        else
           repeat g, w := SXERandomWord(G); g := g^myp; w := w^myp; until not g eq g^0;
        end if;

        i := SXEWhatPPD(g,q);

        if i in ess then 
            ex := q^i-1;

            if    d eq 16 then ex := ((q^i-1)*(q^(12-i)-1));
            elif  d eq 10 and not q eq 3 then  ex := ((q^i-1)*(q^(8-i)-1));
            elif  d eq 10 and q eq 3 then ex := (q^7-1);
            elif  d eq 16 and q eq 2 then ex := &*[q^i-1 : i in [1,11]];
            elif  d eq 20 and q eq 2 then ex := &*[q^i-1 : i in [1,2,3,4,11]];
            end if;

            h  := g^ex;
            wh := w^ex;

            ppd  := SXEWhatPPD(h,q);
            done := ppd eq (d-i);
            dim  := i;

          //special cases; take care that sometimes ppd eq 2 is not possible!
          //in this case just try our luck with any nontrivial elt.
            if d-i eq 2 and IsOdd(q) and IsPrimePower(q+1) then
               done := not h eq h^0;
            end if;

            if d eq 10 then done := ppd eq 2; dim := 8; 
            elif d eq 12 then done := ppd eq 2; dim := 10; 
            elif d eq 8 then done := ppd eq 2; dim := 6; 
            end if;
            if d in [8,10,12] and IsOdd(q) and IsPrimePower(q+1) then
               done := not h eq h^0;
            end if;
            
            if d eq 16 then done := ppd eq 4; dim := 12; 
            elif d eq 20  and q eq 2 then done := ppd eq 5; dim := 15; 
            elif d eq 16  and q eq 2 then done := ppd eq 4; dim := 12; 
            end if;

            if d in [5,6] then
                if d eq 5 then ex := q^3-1;
                elif d eq 6 and not q eq 3 then ex := (q^3-1)*(q-1);
                elif d eq 6 and q eq 3 then ex := q^3-1;
                end if;
                h    := g^ex;
                wh   := w^ex;
                ppd  := SXEWhatPPD(h,q);
                done := (ppd eq 2) or (IsOdd(q) and IsPrimePower(q+1) and not h eq h^0);
                dim  := d - 2;
            end if;
       
            if done then 
                vprint evenSXcpu,3 : "runtime SXEgetElementForSLBlack is",Cputime(rnt);
                vprint evenSX, 5: "end SXEgetElementForSLBlack";
                return h,wh,dim,cnt; 
            end if;
        end if;
    until done;
end function;


/*********************************************************************/
/* FindSmallerSL for degrees 4
/*********************************************************************/
SXEFindSmallerSLDegree4NatRep := function(G)
    vprint evenSX, 2: "start SXEFindSmallerSLDegree4NatRep";

    trivActOnBlock := function(G,g,w,f)
       MA  := MatrixAlgebra(BaseRing(G),Degree(G));
       h   := MA!g;
       B   := Basis(Nullspace(Evaluate(f,h)));
       dim := #B;
       Bim := [i*h : i in B];
       B   := Matrix(Degree(G),&cat([Eltseq(u) : u in B])); 
       mat := &cat([Eltseq(u): u in Solution(B,Bim)]);
       mat := GL(dim,BaseRing(G))!mat;
       o := ProjectiveOrder(mat : Proof:=false);//: Proof:=false);
       return g^o, w^o, dim, o, mat;
   end function;

   getElt := function(G : range := [3], limit := 2000) 
     nmr := 1;
     repeat
        nmr +:= 1;
        g, w := SXERandomWord(G);
        fac  := Factorisation(CharacteristicPolynomial(g));
        deg  := [Degree(f[1]) : f in fac];
        m,i  := Maximum(deg);
        f    := fac[i][1];
        if &+deg eq 4 and m eq 3 then
            x, w, dim := trivActOnBlock(G,g,w,f);
            if not IsDiagonal(x) then return x,w,m; end if;
       end if;
       until nmr gt limit; 
       error "SXEFindSmallerSLDegree4NatRep: could not find elt";       
    end function;

    rnt    := Cputime();
    type   := G`type;
    nP     := G`natParams; d := nP[2]; q := nP[3]; p := nP[4];
    if q eq 2 then error "SL(4,2) has to be done directly"; end if;
  
    want := "SL";
    elt  := []; dim := []; cnt := 0; elt := 0; fls := 0; fst := 0;
    finish := false;
    repeat
        g,gw,rg := getElt(G : range := [3]);
        k,kw,rk := getElt(G : range := [3]);
        l := 1;
        while l le 2 and not finish do
            u, uw := SXERandomWord(G);
            h     := g^u;
            hw    := gw^uw;
            rh    := rg;
            elt +:= 1;
            H     := sub<Generic(G) | h,k>;
            t     := SXELieType(H: char:=p, q:=q);
            finish := t cmpeq <want, 2, q,p>;
            l +:= 1;
        end while;
    until finish;
    H`UserGenerators := [h,k];
    SXEInitGroup(H : UserWords := [hw,kw], type := type, natParams := <type,t[2],q,p>);
    m := t[2];

  //clean up eigenspace:

    gens := [];
    wrds := [];
    t    := false;
    repeat
        g, w := SXERandomWord(H);
        k    := g^(q-1);
        if not k eq k^0 then
            Append(~gens,k);
            Append(~wrds,w^(q-1));
        end if;
        flg := false;
        if #gens gt 0 and IsEven(#gens) then
            K := sub<Generic(H)|gens>;
            K`UserGenerators := gens;
            t := SXELieType(K: char:=p,q:=q);       
        end if;
    until t cmpeq  <want, 2,q,p>;
    SXEInitGroup(K : UserWords := Evaluate(wrds,H`UserWords), type := type, 
                             natParams := H`natParams);
             
    vprint evenSX, 2: "SXEFindSmallerSLDegree4NatRep: found dim",m,"after ",
                      fst,"elts have been constructed";
    vprint evenSXcpu,1: "runtime SXEFindSmallerSLDegree4NatRep is",Cputime(rnt);
    vprint evenSX, 2: "end SXEFindSmallerSLDegree4NatRep";

    return K,m;
end function;



/*********************************************************************/
/* the function SXEgetElementForSUBlack(G) constructs an   
/* element of G which, in nat rep, has a large 1-eigenspace and usually
/* an order divisible by a certain ppd.
/*********************************************************************/
SXEgetElementForSUBlack := function(G : range := [])
    vprint evenSX, 5: "start SXEgetElementForSU";
    rnt := Cputime();
    d := G`natParams[2];  q := G`natParams[3];  p := G`natParams[4];
    a := Floor(Log(p,q));

    cnt  := 0;
    done := false;

    if range cmpeq [] then 
        ess  := [i : i in [1..d] | i ge (2*d/3) and IsOdd(d-i) and 
                                   i le 5*d/6 and not i mod (2*(d-i)) eq 0];
    else
        ess := [u : u in {d-(r div 2) : r in range} | not u mod (d-u) eq 0 and IsOdd(d-u)];
    end if;

  //we only use SXEWhatPPD(g,q^2), so we 
  //only want odd things here so we assume we have a factor q^i+1
  //thus, if for small degree we have some even entry in ess, we have
  //to interpret this correctly.

    if IsOdd(d) then ess := [i-1 : i in ess]; end if;
   
  //special cases
    if d in [5,6] then ess := [3];
    elif d eq 8 then     ess := [5];
    elif d eq 7 then     ess := [5];
    elif d eq 9 then     ess := [7];
    elif d eq 11 then    ess := [4];
    elif d eq 12 then    ess := [4];
    elif d eq 13 then    ess := [5];
    elif d eq 15 then    ess := [11];
    elif d eq 20 then    ess := [13,15,17];
    elif d eq 21 then    ess := [17];
    end if;

    if q eq 2 then
       if d eq 21 then ess := [15];
       elif d eq 15 then ess := [9]; 
       elif d in [12..14] then ess := [7];
       elif d eq 11 then ess := [3]; 
       elif d eq 10 then 
          repeat 
             g, w := SXERandomWord(G); 
          until Order(g) eq 35;
          vprint evenSXcpu,3 : "runtime SXEgetElementForSUBlack is",Cputime(rnt);                            
          vprint evenSX, 5: "end SXEgetElementForSUBlack";                            
          return g^7,w^7,6;  
       elif d eq 9 then
          repeat 
             g, w := SXERandomWord(G); 
          until Order(g) mod 55 eq 0 and not SXEPrimeOrderElement(g,2);
          vprint evenSXcpu,3 : "runtime SXEgetElementForSUBlack is",Cputime(rnt); 
          vprint evenSX, 5: "end SXEgetElementForSUBlack";
          return g^33,w^33,5; 
       elif d eq 8 then
          repeat g, w := SXERandomWord(G); until Order(g) eq 99;
          vprint evenSXcpu,3 : "runtime SXEgetElementForSUBlack is",Cputime(rnt); 
          vprint evenSX, 5: "end SXEgetElementForSUBlack";
          return g^33,w^33,5; 
       end if;
    end if;
   
    if q eq 3 then
       if d eq 9 then ess := [5]; end if;
       if d eq 8 then ess := [5]; end if;
       if d eq 7 then 
           repeat 
              g, w := SXERandomWord(G); 
           until Order(g) mod 35 eq 0 and not SXEPrimeOrderElement(g,3);
           vprint evenSXcpu,3 : "runtime SXEgetElementForSUBlack is",Cputime(rnt); 
           vprint evenSX, 5: "end SXEgetElementForSUBlack";
           return g^80,w^80,4; 
       end if;
    end if;

  //make sure that we don't look for ppd of 2^6-1, which does not exist.
  //if q eq 2 then ess := [i : i in ess | not d-i eq 6 and not i eq 6]; end if;
    if ess eq [] and not d in [] then error "SXEgetElementForSUBlack: empty list";  end if;
  
    myp := p^(1+Ilog(p,d));
    repeat
        cnt +:= 1;
        if cnt mod (30*d) eq 0 then "SXEgetElementForSUBlack: nr of constructed elts",cnt; end if;
        if cnt ge 20000 then error "SXEgetElementsForSUBlack: cannot find suitable elements -- are input parameters correct?"; end if;
        if IsOdd(q) then
           repeat g, w := SXERandomWord(G); until not g eq g^0 and not SXEPrimeOrderElement(g,p);
        else
           repeat g, w := SXERandomWord(G); g := g^myp; w := w^myp; until not g eq g^0;
        end if;
   
        i := SXEWhatPPD(g,q^2); 

        if i in ess then

          //recall that i is odd, unless for some special cases considered below,
          //we suppose this i corresponds to a factor q^i+1
          //now correct that for odd d where we have increased each i in ess by 1
            if IsOdd(d) then ex := (q^i+1)*(q+1); i := i+1; else ex := q^i+1; end if;
          
            if d eq 5  then ex := q^3+1; 
            elif d eq 6 then ex := (q^3+1)*(q+1);
            elif d eq 7  then ex := (q^5+1);
            elif d eq 8  then ex := (q^5+1)*(q+1);
            elif d eq 9  then ex := q^7+1; 
            elif d eq 11 then ex := q^8-1; 
            elif d eq 12 then ex := (q^8-1)*(q+1); 
            elif d eq 13 then ex := q^10-1; 
            end if;

            if q eq 2 then
               if d eq 21  then ex := (q^15+1)*5; end if;
               if d eq 15 then ex := (q^9+1)*(q+1); end if;
               if d eq 14 then ex := (q^7+1)*3^2*11*7; end if;
               if d eq 13 then ex := (q^7+1)*3^2*11*7; end if;
               if d eq 12 then ex := (q^7+1)*7*5*3; end if;
               if d eq 11 then ex := (q^6-1)*7*3; end if;
               if d eq 10 then ex := (q^7+1); end if;
            end if;
            if q eq 3 then
               if d eq 9 then ex := (q^5+1)*(q+1); end if;   
               if d eq 8 then ex := (q^5+1); end if;   
               if d eq 7 then ex := (q^4-1); end if;   
            end if;
            
            h    := g^ex; 
            w    := w^ex;
            ppd  := SXEWhatPPD(h,q^2);

          //note that d-i is odd unless for special cases;
          //in particular, no problem with non-existing ppds
            done := ppd eq (d-i);
            dim  := i;

          //if we look for ppd 1 (2-dim space) then we just try our luck with a
          //nontrivial element
            if    d eq 5 then done := not h eq h^0; dim := 3;
            elif  d eq 6 then done := not h eq h^0; dim := 4;   //ok, must have had (q^3+1)(q+1)(q^2-1)
            elif  d eq 7 then done := not h eq h^0;; dim := 5;
            elif  d eq 8 then done := ppd eq 1 and not h eq h^0; dim := 6; //tricky case!  
            elif  d eq 9 then done := not h eq h^0; dim := 7;
            elif d eq 11 then done := ppd eq 3; dim := 8; 
            elif d eq 12 then done := ppd eq 3; dim := 9; 
            elif d eq 13 then done := ppd eq 3; dim := 10;
            end if;
            
            if q eq 2 then
               if d eq 15 then done := ppd eq 5; dim := 10; end if;
               if d eq 21 then done := not h^2 eq h^0; dim := 15; end if;
               if d eq 14 then done := not h^2 eq h^0; dim := 10; end if;
               if d eq 13 then done := not h^2 eq h^0; dim := 9; end if;
               if d eq 12 then done := not h^2 eq h^0; dim := 7; end if;
               if d eq 11 then done := not h^2 eq h^0; dim := 7; end if;
            end if;
            if q eq 3 then
               if d eq 9 then done := ppd eq 3; dim := 6; end if;
               if d eq 8 then done := ppd eq 3; dim := 5; end if;
               if d eq 7 then done := ppd eq 3; dim := 4; end if;
            end if;
            
            if done then 
                vprint evenSXcpu,3 : "runtime SXEgetElementForSUBlack is",Cputime(rnt); 
                vprint evenSX, 5: "end SXEgetElementForSUBlack";
                return h,w,dim,cnt; 
            end if;
        end if;
    until done;
end function;



/*********************************************************************/
/* the function SXEgetElementForSpBlack(G) construct an   
/* element of G with large 1-eigenspace and order
/* divisible by a certain ppd.
/*********************************************************************/
SXEgetElementForSpBlack := function(G : range := [])
    vprint evenSX, 5: "start SXEgetElementForSpBlack";
    rnt := Cputime();
    d := G`natParams[2] div 2;  
    q := G`natParams[3];  
    p := G`natParams[4];
    a := Floor(Log(p,q));

    cnt  := 0;
    done := false;
    if range cmpeq [] then 
        ess  := [i : i in [1..d] | i ge (2*d/3) and 
                                   i le 5*d/6 and not i mod (2*(d-i)) eq 0];
    else
        ess := [u : u in {d-(r div 4) : r in range} | not u mod (d-u) eq 0 ];
    end if;

    if d eq 20 and q eq 2 then Append(~ess,15); end if;    

    if d eq 3 then ess := [4]; 
    elif d eq 5 then ess := [8];
    elif d eq 6 then ess := [5];
    elif d eq 12 then ess := [9];
    elif d eq 8 then ess := [6]; 
    elif d eq 4 then ess := [3]; 
    end if;
   
    if q eq 2 then 
       if d eq 8  then ess := [12]; 
       elif d eq 10 then ess := [12]; 
       elif d eq 12 then ess := [18]; //16
       end if;
    end if;


   if d eq 8 and q eq 2 then
      repeat g, w := SXERandomWord(G); until Order(g) eq 65;
      vprint evenSXcpu,3 : "runtime SXEgetElementForSpBlack is",Cputime(rnt); 
      vprint evenSX, 5: "end SXEgetElementForSpBlack";
      return g^13,w^13,12;
   elif d eq 6 then
      if  q eq 3 then 
          repeat g, w := SXERandomWord(G); until Order(g) eq 205;
          vprint evenSXcpu,3 : "runtime SXEgetElementForSpBlack is",Cputime(rnt); 
          vprint evenSX, 5: "end SXEgetElementForSpBlack";
          return g^41,w^41,8; 
       elif q eq 2 then
          repeat g, w := SXERandomWord(G); until Order(g) eq 85;
          vprint evenSXcpu,3 : "runtime SXEgetElementForSpBlack is",Cputime(rnt); 
          vprint evenSX, 5: "end SXEgetElementForSpBlack";
          return g^17,w^17,8; 
       end if;
   elif d eq 5 then                               
       if  q in [2,3] then                                                   
          repeat g, w := SXERandomWord(G); until Order(g) eq 35;
          vprint evenSXcpu,3 : "runtime SXEgetElementForSpBlack is",Cputime(rnt);
          vprint evenSX, 5: "end SXEgetElementForSpBlack";
          return g^7,w^7,6;
       elif q eq 7 then
          repeat g, w := SXERandomWord(G); until Order(g) eq 215;
          vprint evenSXcpu,3 : "runtime SXEgetElementForSpBlack is",Cputime(rnt); 
          vprint evenSX, 5: "end SXEgetElementForSpBlack";
          return g^43,w^43,6;   
       end if;
   elif d eq 4 then
       if q eq 2 then
          repeat g, w := SXERandomWord(G); until Order(g) eq 21;                                  
          vprint evenSXcpu,3 : "runtime SXEgetElementForSpBlack is",Cputime(rnt);                       
          vprint evenSX, 5: "end SXEgetElementForSpBlack"; 
          return g^7,w^7,6;        
       elif q eq 3 then 
          repeat g, w := SXERandomWord(G); until Order(g) eq 28;
          vprint evenSXcpu,3 : "runtime SXEgetElementForSpBlack is",Cputime(rnt);                            
          vprint evenSX, 5: "end SXEgetElementForSpBlack"; 
          return g^7,w^7,6;
       end if;
   end if;
 
   //make sure that we don't look for ppd of 2^6-1, which does not exist.
    if q eq 2 then ess := [i : i in ess | not d-i eq 6 and not i eq 6]; end if;

    if ess eq [] then error "getEltSp: empty list ess"; end if;
    
    myp := p^(1+Ilog(p,2*d));
    repeat
        cnt +:= 1;
        if cnt mod (100*d) eq 0 then "SXEgetElementForSpBlack: nr of constructed elts",cnt; end if;
        if cnt ge 10000 then error "SXEgetElementsForSpBlack: cannot find suitable elements -- are input parameters correct?"; end if;
        if IsOdd(q) then
           repeat g, w := SXERandomWord(G); until not g eq g^0 and not SXEPrimeOrderElement(g,p);
        else
           repeat g, w := SXERandomWord(G); g := g^myp; w := w^myp; until not g eq g^0;
        end if;

        ii := SXEWhatPPD(g,q);

        if ii in ess then
            if ii gt d then 
               i := ii div 2;
               ex := q^i+1;
            else 
               i := ii;
               ex := q^i-1;
            end if;

            h := g^ex;        
            w := w^ex;
            ppd  := SXEWhatPPD(h,q);
            done := ppd eq 2*(d-i);
            dim  := 2*i;

            if q eq 2 and d eq 12 then done := ppd eq 3; dim:=18; end if;

          //take care of ppd 2
            if IsOdd(q) and IsPrimePower(q+1) then
               if (d-i) eq 1 or d in [3,4,5] then
                  done := not h eq h^0;
               end if; 
            end if;

            if done then 
                vprint evenSXcpu,3 : "runtime SXEgetElementForSpBlack is",Cputime(rnt); 
                vprint evenSX, 5: "end SXEgetElementForSpBlack";
                return h,w,dim,cnt; 
            end if;
        end if;
    until done;
end function;




/*********************************************************************/
/* the function SXEgetElementForOpBlack(G) construct an    
/* element of G with large 1-eigenspace and order
/* divisible by a certain ppd.
/*********************************************************************/
SXEgetElementForOpBlack := function(G : range := [])
    vprint evenSX, 5: "start SXEgetElementForOpBlack";
    rnt := Cputime();
    d := G`natParams[2] div 2;  
    q := G`natParams[3];  
    p := G`natParams[4];
    a := Floor(Log(p,q));

    cnt  := 0;
    done := false;
    if range cmpeq [] then 
        ess  := [i : i in [1..d] | i ge (2*d/3) and 
                                   i le 5*d/6 and not i mod (2*(d-i)) eq 0];
    else
        ess := [u : u in {d-(r div 4) : r in range} | not u mod (d-u) eq 0 ];
    end if;

  //look for q^i+1, i.e. ppd 2i
    ess := [2*i : i in ess];

    if d eq 3 then ess := [4];
    elif d eq 5  then ess := [4];
    elif d eq 6 then ess := [6];
    elif d eq 12 then ess := [10];
    elif d eq 8 then ess := [10];
    elif d eq 4 then ess := [4]; //prob: q^2+1 or q^4-1
    elif d eq 10 then ess := [7]; 
    end if;

    if q eq 2 then
       if d eq 16 then ess := [22,24,26]; end if;
       if d eq 13 then ess := [18,20]; end if;
    end if;

    if q eq 2 then
       if d eq 6 then
          repeat g, w := SXERandomWord(G); until Order(g) eq 85;
          vprint evenSXcpu,3 : "runtime SXEgetElementForOpBlack is",Cputime(rnt);
          vprint evenSX, 5: "end SXEgetElementForOpBlack";
          return g^17,w^17,8;
       elif d eq 5 then
          repeat g, w := SXERandomWord(G); until Order(g) eq 45;
          vprint evenSXcpu,3 : "runtime SXEgetElementForOpBlack is",Cputime(rnt);
          vprint evenSX, 5: "end SXEgetElementForOpBlack";
          return g^9,w^9,6;
       elif d eq 3 then
          repeat g, w := SXERandomWord(G); until Order(g) eq 15;
          vprint evenSXcpu,3 : "runtime SXEgetElementForOpBlack is",Cputime(rnt);
          vprint evenSX, 5: "end SXEgetElementForOpBlack";
          return g^5,w^5,4;
       end if;
    end if;

    if ess eq [] then error "SXEgetElementForOpBlack: empty list ess"; end if;

    myp := p^(1+Ilog(p,2*d));
    repeat
        cnt +:= 1;
        if cnt mod (100*d) eq 0 then "SXEgetElementForOpBlack: nr of constructed elts",cnt; end if;
        if cnt ge 10000 then error "SXEgetElementsForOpBlack: cannot find suitable elements -- are input parameters correct?"; end if;
       
        if IsOdd(q) then
           repeat g, w := SXERandomWord(G); until not g eq g^0 and not SXEPrimeOrderElement(g,p);
        else
           repeat g, w := SXERandomWord(G); g := g^myp; w := w^myp; until not g eq g^0;
        end if;

        i := SXEWhatPPD(g,q); 

        if i in ess then
            ii := i div 2;
            ex := q^ii+1;

            if d eq 6 then    ex := (q^3+1)*(q-1);
            elif d eq 5 then  ex := (q^2+1)*(q-1);  //see below!
            elif d eq 3 then  ex := (q^2+1);
            elif d eq 12 then ex := (q^10-1);
            elif d eq 8 then  ex := (q^5+1)*(q-1);  
            elif d eq 4 then  ex := (q^2+1)*(q-1);  
            elif d eq 10 then ex := (q^7-1)*(q+1);
            end if;

            //if d=5 then want in torus (q^2+1)(q+1)(q-1)^2, and NOT
            //in torus (q^2+1)(q+1)^3
            if d eq 5 then correct := not g^((q^2+1)*(q+1)) eq g^0; end if;


          //so we kill q^ii+1 and we want to have q^{d-ii}+1
            h := g^ex;        
            w := w^ex;
           
            ppd := SXEWhatPPD(h,q);     
                      
            done := ppd eq 2*(d-ii);
            dim  := 2*ii;

            if d eq 6 then    done := ppd eq 4; dim := 8;
            elif d eq 5 then  done := ppd eq 2 and correct; dim := 8;
            elif d eq 3 then  done := ppd eq 2; dim := 4;
            elif d eq 12 then done := ppd eq 4; dim := 20; 
            elif d eq 8 then  done := ppd eq 4; dim := 12; 
            elif d eq 4 then  
               done := ppd eq 2;
               dim := 6; 
            elif d eq 10 then done := ppd eq 4; dim := 16;
            end if;

            if (d-ii) eq 1 and IsOdd(q) and IsPrimePower(q+1) then
               done := not h eq h^0; 
               dim  := 2*(d-1);
            end if;
            if done then  
                vprint evenSXcpu,3 : "runtime SXEgetElementForOpBlack is",Cputime(rnt); 
                vprint evenSX, 5: "end SXEgetElementForOpBlack";
                return h,w,dim,cnt; 
            end if;
        end if;
    until done;
end function;




/*********************************************************************/
/* the functions getElementForSX(G) construct an     (black)
/* element of G with large 1-eigenspace and order
/* divisible by a certain ppd.
/* modification: just want to find OmegaPlus(d-4/d-6,q) in OmegaMinus(d,q)
/*********************************************************************/
SXEgetElementForOmBlack := function(G : range := [])
    vprint evenSX, 5: "start new version of SXEgetElementForOmBlack";
    rnt := Cputime();
    d := G`natParams[2] div 2; 
    q := G`natParams[3];
    p := G`natParams[4];
    a := Floor(Log(p,q));

    cnt  := 0;
    done := false;
    
  //if d mod 2 eq 0 then ess := [d]; else ess := [d+1]; end if;
    if d mod 2 eq 0 then ess := [d]; else ess := [d+1,d+3]; end if;   

    if q eq 2 then
       if d eq 9 then ess := [10]; 
       elif d eq 8 then ess := [10];
       end if;
      if d eq 6 then
         repeat g, w := SXERandomWord(G); until Order(g) eq 35;
         vprint evenSXcpu,3 : "runtime SXEgetElementForOpBlack is",Cputime(rnt);
         vprint evenSX, 5: "end SXEgetElementForOpBlack";
         return g^7,w^7,8;
      elif d eq 5 then
         repeat g, w := SXERandomWord(G); until Order(g) eq 35;
         vprint evenSXcpu,3 : "runtime SXEgetElementForOpBlack is",Cputime(rnt);
         vprint evenSX, 5: "end SXEgetElementForOpBlack";
         return g^7,w^7,6;
      end if;
    end if;

    if d eq 5 and q in [3,5,7] then
       if q eq 3 then
          repeat g, w := SXERandomWord(G); until Order(g) eq 65;
          vprint evenSXcpu,3 : "runtime SXEgetElementForOpBlack is",Cputime(rnt);
          vprint evenSX, 5: "end SXEgetElementForOpBlack";
          return g^13,w^13,6;
       elif q eq 5 then
          repeat g, w := SXERandomWord(G); until Order(g) eq 403;
          vprint evenSXcpu,3 : "runtime SXEgetElementForOpBlack is",Cputime(rnt);
          vprint evenSX, 5: "end SXEgetElementForOpBlack";
          return g^31,w^31,6;
       elif q eq 7 then
          repeat g, w := SXERandomWord(G); until Order(g) eq 95;
          vprint evenSXcpu,3 : "runtime SXEgetElementForOpBlack is",Cputime(rnt);
          vprint evenSX, 5: "end SXEgetElementForOpBlack";
          return g^19,w^19,6;
       end if;

    end if;

    if d eq 5 then ess := [3]; end if; 
    if d eq 4 then ess := [3]; end if;
    if d eq 3 then ess := [4]; end if; 
    if d eq 11 then ess := [14]; end if;

    myp := p^(1+Ilog(p,2*d));
    repeat
        cnt +:= 1;
        if cnt mod (100*d) eq 0 then "SXEgetElementForOmBlack: nr of constructed elts",cnt; end if;
        if cnt ge 10000 then error "SXEgetElementsForOmBlack: cannot find suitable elements -- are input parameters correct?"; end if;
      
        if IsOdd(q) then
           repeat g, w := SXERandomWord(G); until not g eq g^0 and not SXEPrimeOrderElement(g,p);
        else
           repeat g, w := SXERandomWord(G); g := g^myp; w := w^myp; until not g eq g^0;
        end if;
     
        i := SXEWhatPPD(g,q); 

        if i in ess then

            if q eq 2 and d in [6,8,9] then
               if d eq 9 then ex := (q^5+1)*(q+1); dim := 12; 
               elif d eq 8 then ex := (q^5+1); dim := 10;
               end if;

               h    := g^ex;
               w    := w^ex;
               ppd  := SXEWhatPPD(h,q);
               if d eq 9 then done := ppd eq 3;
               elif d eq 8 then done := ppd eq 3;
               end if;

            elif d eq 5 then

               ex   := (q^3-1)*(q-1);
               h    := g^ex;
               w    := w^ex;
               ppd  := SXEWhatPPD(h,q);
               done := ppd eq 2;
               dim  := 8;
               if IsOdd(q) and IsPrimePower(q+1) then
                  done := not h eq h^0; 
               end if;
 
           elif d eq 4 then
               ex   := q^3-1;
               h    := g^ex;
               w    := w^ex;
               ppd  := SXEWhatPPD(h,q);
               done := ppd eq 2;
               if IsOdd(q) and IsPrimePower(q+1) then done := not h eq h^0; end if;
               dim  := 6;

            elif d eq 3 then
               ex   := q^2+1;
               h    := g^ex;
               w    := w^ex;
               ppd  := SXEWhatPPD(h,q);
               done := not h eq h^0;
               dim  := 4;

            elif d eq 11 then
               ex   := q^7+1;
               h    := g^ex;
               w    := w^ex;
               ppd  := SXEWhatPPD(h,q);
               done := not h eq h^0 and ppd eq 4;
               dim  := 14;

            elif IsEven(d) then

             //note that Gcd(q^i+1, q^(i+1)+1)=1    
             //kill (q^(d/2)+1)(q\pm 1), want q^{d/2-1}+1
               ex   := ( q^((d div 2) ) +1) * (q^2-1);
               h    := g^ex;
               w    := w^ex;
               ppd  := SXEWhatPPD(h,q);
               done := ppd eq (d-2);
               dim  := (d+2);

            elif IsOdd(d) then

               if i eq d+1 then 
                  ex   := ( q^(((d+1) div 2) ) +1)*(q^2-1);  
                  wppd := d-3;
               elif i eq d+3 then
                  ex   := ( q^(((d+3) div 2) ) +1);
                  wppd := ((d-3) div 2);
               end if;
               h    := g^ex;
               w    := w^ex;
               ppd  := SXEWhatPPD(h,q);
               done := ppd eq wppd;
               dim  := d+3;
            end if;

            if done then
                vprint evenSXcpu,3 : "runtime SXEgetElementForOmBlack is",Cputime(rnt); 
                vprint evenSX, 5: "end SXEgetElementForOmBlack";
                   return h,w,dim,cnt;
            end if;
        end if;
    until done;
end function;




/*********************************************************************/
/* FindSmallerSL for degrees 4
/*********************************************************************/
SXEFindSmallerSLDegree4black := function(G)

    getElt := function(G,ps,myp :  limit := 1000)
       cnt := 1;
       nP  := G`natParams; d := nP[2]; q := nP[3]; p := nP[4];

       if q eq 4 then
          repeat
             g,w:=SXERandomWord(G);
             og := Order(g);
          until og mod 21 eq 0 and not og eq 1;
          return g^(og div 3),w^(og div 3),3;
       end if;
          
       repeat
           cnt +:= 1;
           if cnt mod 100 eq 0 then "GetLargeEltSL4: nr of constructed elts",cnt; end if;
                
           if IsOdd(q) then
              repeat g, w := SXERandomWord(G); g:=g^myp; w:=w^myp; 
              until not g eq g^0 and not SXEPrimeOrderElement(g,p);
           else
              repeat g, w := SXERandomWord(G); g := g^myp; w := w^myp; 
              until not g eq g^0;
           end if;

           i := SXEWhatPPD(g,q);

           if i eq 3 then
            //usually h will have a-eigenspace of dimension 3 with a\ne 1
            //we clean this up later
              for s in ps do
                 h := g^((q^3-1) div s); wh := w^((q^3-1) div s);
                 done := not h eq h^0;
                 dim  := 3;
                 if done then return h,wh,dim,cnt; end if;
             end for;
          end if;
       until false;
    end function;


    vprint evenSX, 2: "start SXEFindSmallerSLDegree4black";
    rnt    := Cputime();
    type   := G`type;
    nP     := G`natParams; d := nP[2]; q := nP[3]; p := nP[4];
    elt := 0; 
    finish := false;
    ps  := [i[1]^i[2] : i in Factorisation(q^3-1) | (q-1) mod i[1] eq 0];                                                                                                                    
    myp := p^(1+Ilog(p,2*d));   
    
    cntr := 0;
    repeat
   
        cntr := cntr + 1;
        g,gw,rg := getElt(G,ps,myp); 
        h,hw,rh := getElt(G,ps,myp);

        H       := sub<Generic(G) | g,h>;
        H`UserGenerators := [g,h];
        SXEInitGroup(H : UserWords := [gw,hw], type := "SL", natParams := <"SL",2,q,p>);        

        gens := [];                                                                           
        wrds := [];                 
        t    := false;            
        cnt:=0;
        checked := 0;
        while not finish and cnt le 20 and checked lt 2 do
           cnt := cnt+1;
           g, w := SXERandomWord(H);       
           k    := g^(q-1);                                                                                
           if not k eq k^0 then      
              Append(~gens,k);  
              Append(~wrds,w^(q-1));        
           end if;    
           flg := false;	 

           if #gens gt 0 and #gens mod 5 eq 0 then       
               checked := checked + 1;

               K := sub<Generic(H)|gens>;        
               K`UserGenerators := gens; 
               t := SXELieType(K: char:=p,q:=q, shouldBe:=<"SL",2,q,p>);
               finish := t cmpeq <"SL", 2, q,2>;

           end if;      
       end while;
       if finish then
          SXEInitGroup(K :  UserWords := Evaluate(wrds,H`UserWords), natParams := H`natParams);       
       end if; 
    until finish;

    m := t[2];

    vprint evenSX, 1: "deg",d,"now found dim",m;
    vprint evenSXcpu,1: "runtime SXEFindSmallerSL deg",d," is",Cputime(rnt);
    vprint evenSX, 2: "end SXEFindSmallerSLDegree4black";

    return K,m;
end function;



/*********************************************************************/
/* Constructs a smaller classical subgroup of G (black)
/* generated by two conjugate elements.
/*********************************************************************/
SXESmallerSXBlack := function(G : range:=[])

    rnt  := Cputime();
    type := G`type;
    nP   := G`natParams; d := nP[2]; q := nP[3]; p := nP[4];

    if d eq 4 and G`type eq "SL" then return SXEFindSmallerSLDegree4black(G); end if;
    if d eq 6 and 2 in range then sixToTwo := true; else sixToTwo := false; end if;
    vprint evenSX, 2: "start SXESmallerSXBlack";

    if    (type eq "SU" and q eq 2 and d in [5..8])
       or (type eq "SU" and q eq 3 and d in [5,6]) 
       or (type eq "Sp" and q in [2,3] and d in [6,8])  
       or (type eq "O-" and d eq 8 and q in [2,3,5]) 
       or (type eq "O-" and d eq 6 and q in [2,4,3,5])
       or (type eq "O+" and d eq 8)   
       or (type eq "O+" and d eq 10 and q in [2,3,5,7]) 
       or (type in "O+" and d eq 6 and q in [2,3,5]) then
        error "SXESmallerSXBlack does not work for ",type,"(",d,",",q,").";
    end if;

  //for Sp(8,2) only can return OmegaMinus(4,2) gen by two 3-elts...

    if range eq [] then
        range := [e : e in [1..d] | e ge d/3 and e le 2*d/3 and IsEven(e)]; 
        if d in [10.. 25] then range := [ i: i in [4 .. d-4] | IsEven(i)]; end if;
    end if;
    if not type in ["SL","SU"] then
        range := [e : e in range | e mod 4 eq 0];
    end if;
      

  //avoid certain reduction
    if type eq "SL" then
        if d in [5,6] then range := [4]; end if;
        getElt := SXEgetElementForSLBlack;
        want := "SL";
    elif type eq "SU" then
        if d in [20,21] then Append(~range,6); Append(~range,14); 
        elif d in [5,6] then range := [4]; 
        elif d eq 12 and q eq 2 then Append(~range,10);
        elif d eq 11 and q eq 2 then Append(~range,8);
        elif d eq 10 and q eq 2 then Append(~range,8);
        elif d eq 9 and q eq 3  then range := [6];
        elif d eq 9 and q  eq 2 then range := [8]; 
        elif d eq 8 and q in [2,3] then range := [6];
        elif d eq 7 and q in [2,3] then range := [6]; 
        end if;
        getElt := SXEgetElementForSUBlack;
        want   := "SU"; 
    elif type eq "Sp" then
        if d eq 24 and not q eq 2 then range := [4,8,12]; 
        elif d eq 24 and  q eq 2 then range := [4,8,12,16]; 
        elif d in [6] then range := [4]; 
        elif d eq 16 then range := [8]; 
        elif d eq 12 then range:=[4]; //Append(~range,[4]);
        elif d eq 10 then Append(~range,[8]);
        elif d eq 8 then Append(~range,[6]);
        elif d eq 20 and q eq 2 then  Append(~range,[16]);
        end if;
        getElt := SXEgetElementForSpBlack;
        if IsEven(q) then want   := "O+"; else want := "Sp"; end if;
    elif type eq "O+" then
       //make sure we can power up to nontriv elts in getSecondSX
        if not d eq 14 and ((2*d-4) mod 3 eq 0) then 
            range := [ i : i in range | not i eq ((2*d-4) div 3)]; 
        end if;
        if d eq 24 then range := [4,8,12]; 
        elif d eq 20 then range := [8]; 
        elif d eq 6 then range := [4]; 
        elif d eq 32 and q eq 2 then range := [20,12,16];
        elif d eq 26 and q eq 2 then range := [12,16]; 
        elif d eq 12 then range := [4,8];
        elif d eq 10 then range := [4];
        elif d eq 8 then range := [4,6];
        end if;
        getElt := SXEgetElementForOpBlack;
        want   := "O+";
    elif type eq "O-" then //just get large OmegaPlus
        if d mod 4 eq 0 then range := [d-4]; end if;
        if d mod 4 eq 2 then range := [d-6]; end if;
        if d eq 12 then range := [4,8]; 
        elif d eq 10 then range := [4,8]; 
        elif d eq 6 then range := [4];
        end if;
        getElt := SXEgetElementForOmBlack;
        want   := "O+";
    end if;

    if #range eq 0 then error "nothing left in range!"; end if;

    elt  := []; dim := []; cnt := 0; elt := 0; fls := 0; fst := 0;
    finish := false;
    repeat
        repeat
            fst +:= 1;
            g,gw,rg := getElt(G : range := range);
            if fst mod 2 eq 0 then 
                vprint evenSX,4 : "SXESmallerSXBlack: constructed",fst,"elts"; 
            end if;
        until 2*(d-rg) in range;
        l := 1;
        while l le 2 and not finish do
            u, uw  := SXERandomWord(G);
            h      := g^u;
            elt   +:= 1;
            H      := sub<Generic(G) | g,h>;
            if want eq "O+" and 2*(d-rg) eq 4 then
                t := SXEIsOmegaPlus4(H:p:=p,q:=q);
                finish :=  t cmpeq <"O+",4,q,p>;
            else
                t := SXELieType(H: char:=p,q:=q, shouldBe := <want,2*(d-rg),q,p>);  //// added shouldBe here!
                if t cmpeq <"Sp",4,7,7> and #H le 276595199 then t := false; end if;
                if not t cmpeq false then 
                    finish := t eq <want, 2*(d-rg), q,p>;
                end if;          
            end if;
            if not t cmpeq false and not t[2] eq 2*(d-rg) then 
             //"got wrong dimension, so quit";
               l := 2; 
            end if;
            l := l + 1;
        end while;
    until finish;
    hw := gw^uw;
    H`UserGenerators := [g,h];
    SXEInitGroup(H : UserWords := [gw,hw], type := want, natParams := <want,t[2],q,p>);
    m  := t[2]; 

  //reduce SL6 further to SL2:
    if type eq "SL" and d eq 6 and sixToTwo then
        vprint evenSX, 2: "SXESSmallerSXBlack: found dim",4,"in deg",6,"now reduce to deg 2";
        H2,m         := SXEFindSmallerSLDegree4black(H);
        H2`UserWords := Evaluate(H2`UserWords, H`UserWords); 
        assert m eq 2;
        H            := SXECopyGroup(H2);
    end if;

    vprint evenSX, 2: "SXESmallerSXBlack: found dim",m,"in deg",d;     
    vprint evenSXcpu,1: "runtime SXESmallerSXBlack deg",d," is",Cputime(rnt);
    vprint evenSX, 2: "end SXESmallerSXBlack, SLP lengths",#gw,#hw;
   
    return H,m;
end function;


/*********************************************************************/
/* the function SXEgetElementNatRep(G) constructs an    
/* element of G with large 1-eigenspace 
/*********************************************************************/
SXEgetElementNatRep := function(G : range := [], Limit := 10000)
    vprint evenSX, 4: "start SXEElementNatRep";
    rnt := Cputime();
    d := G`natParams[2];  q := G`natParams[3];  p := G`natParams[4];
    a := Floor(Log(p,q));
    cnt  := 0;
    done := false;

 //consider two polynomials or a special range?
   special    := false;

  //get eigenspace dimensions we want to have
  //in general, this is the degree of largest factor of char pol
    if range cmpeq [] then 
        ess  := [i : i in [1..d] | i ge (2*d/3) and i le 5*d/6];  //and not i mod (d-i) eq 0];   
    else
        ess := [u : u in {d-(r div 2) : r in range}];
    end if;
 
   if G`type in ["SL","SU"] then
      if d eq 8 and q in [2,3] then ess := [3]; wd := 6; special := true; end if;
      if d eq 5 then ess := [3]; wd := 3; special := true; end if;
   end if;

   if G`type eq "SU" then
      if d eq 8 then ess := [3]; wd := 6;  special := true; 
      elif d eq 7 then ess := [3]; wd := 5;  special := true; 
      elif d eq 6 then ess := [2]; wd := 4;  special := true; 
      end if;
      if d le 14 and q eq 2 then
         special := true;
         if d eq 14 then ess := [5]; wd := 10; 
         elif d eq 13 then ess := [5]; wd := 10; 
         elif d in [11..12] then ess := [4]; wd := 8; 
         elif d in [10] then ess := [7]; wd := 7; 
         elif d in [8..9] then ess := [3]; wd := 6; 
         elif d in [7] then ess := [3]; wd := 5;
         elif d in [5] then ess := [1]; wd := 3;
         elif d in [6] then ess := [1]; wd := 4; 
         end if;
      end if;
   end if;

   if G`type in ["O+","O-"] and d in [6,8,10]  then
      if d eq 10 and q in [3, 5] then ess := [4]; wd := 8; special :=true; end if;
      if d eq 8 and q in [3,5] then ess := [2]; wd := 6;  special := true; end if;
      if d eq 6 and q in [4] then wd := 4;  special := true; end if; 
      if d eq 6 and q in [3,5] then ess := [1]; wd := 4;  special := true; end if;
      if d eq 6 and q in [2] then ess := [2]; wd := 4;  special := true; end if;
 
      if d eq 10 and q in [2,3] then ess := [3]; wd := 6; special :=true; end if; 
      if d eq 8 and q eq 4 then ess := [4]; wd := 6;  special := true; end if;
      if d eq 8 and q eq 2 then ess := [2]; wd := 6;  special := true; end if;
      if d eq 6 and q eq 2 then ess := [2]; wd := 4;  special := true; end if;
   end if;

   if G`type eq "O-" then
      if d eq 16 and q eq 2 then ess := [10..14]; end if;
      if d eq 14 and q in [2,3] then ess := [8..12]; end if; 
      if d eq 12 and q eq 2 then special := true; ess := [4]; wd := 8; end if;
      if d eq 10 and q in [4] then ess := [3]; wd := 6; special :=true; end if;
      if d eq 6 and q eq 4 then ess := [1]; wd := 4;  special := true; end if; 
   end if;

   if G`type eq "Sp" and d in [6,8,10] and q eq 2  then
      if d eq 10  then ess := [3]; wd := 6; special :=true; end if;
      if d eq 8 then ess := [2]; wd := 6;  special := true; end if;
      if d eq 6 then ess := [1]; wd := 4;  special := true; end if; 
   end if;

   if q in [2,3,5] or special then Limit := 10000; end if;
   if ess cmpeq [] then error "SXEgetElementNatRep: empty list ess"; end if;
    
   if d le 10 then Limit := 20000; end if;

   cnt := 1;
   repeat
      if cnt mod (500*d) eq 0 then "SXEgetElementNatRep: nr of constructed elts",cnt; end if;
      if cnt ge 20000 then error "SXEgetElementsNatRep: cannot find suitable elements -- are input parameters correct?"; end if;
      repeat
         cnt +:= 1;
         g, w := SXERandomWord(G);
         fac  := Factorisation(CharacteristicPolynomial(g));
         deg  := [Degree(f[1]) : f in fac];
         m,i  := Maximum(deg);
         f    := fac[i][1];

         if not special and &+deg eq d and m in ess then
            x, w, dim := SXETrivialActionOnInvBlock(G,g,w,f);
            if not IsDiagonal(x) then
                vprint evenSXcpu,3 : "runtime SXEgetElementNatRep is",Cputime(rnt);    
                vprint evenSX,5: "end SXEgetElementNatRep";
                return x,w,m;
            end if;
         elif special and ess[1] in deg then 
             f := &*[i[1] : i in fac | Degree(i[1]) eq ess[1]];
             x, w, dim := SXETrivialActionOnInvBlock(G,g,w,f);
             if not IsDiagonal(x) and Dimension(Eigenspace(x,1)) eq wd then
                vprint evenSXcpu,3 : "runtime SXEgetElementNatRep is",Cputime(rnt);    
                vprint evenSX,5: "end SXEgetElementNatRep";
                return x,w,wd;
             end if;
         end if;
      until cnt gt Limit; 
      error  "SXEgetElementNatRep: couldn't find element";
   until false;
end function;



/*********************************************************************/
/* Constructs a smaller classical subgroup of G (NatRep)
/* generated by two conjugate elements.
/*********************************************************************/
SXESmallerSXNatRep := function(G : range:=[], Limit := 1000, inv:=false)

   vprint evenSX, 2: "start SXESmallerSXNatRep";
   rnt  := Cputime();
   type := G`type;
   nP   := G`natParams; d := nP[2]; q := nP[3]; p := nP[4];
   F    := BaseRing(G);

   if G`type in ["O+","Sp","O-"] and q eq 2 and d in [6,8] then
      error "sorry, but O/Sp(d,2) with d=6,8 cannot be done right now";
   end if;

 //what to construct  
   getElt := SXEgetElementNatRep;
   if   type eq "SL" then want := "SL";
   elif type eq "SU" then want := "SU";
   elif type eq "O+" then want := "O+";
   elif type eq "Sp" then 
      if p eq 2 then want := "O+"; else want := "Sp"; end if;
   elif type eq "O-" then want := "O+";
   end if;

 //adjust range
   if range eq [] then
      range := [e : e in [1..d] | e ge d/3 and e le 2*d/3 and IsEven(e)]; 
      if not type in ["SL","SU"] then
         range := [e : e in range | e mod 4 eq 0];
      end if;
   
      if d in [5,6] then range := [4]; end if;   
     
      if G`type in ["O+","O-"] and d eq 10 and q in [2,3] then range := [8]; end if;
      if G`type eq "Sp" and d eq 10 and q in [2] then range := [8]; end if;
      if G`type eq "O-" and d eq 16 and q eq 2 then range := [4..12]; end if;
      if G`type eq "O-" and d eq 14 and q in [2,3] then range := [4..12]; end if;  
      if G`type eq "O-" and d eq 12 and q in [2] then range := [4..10]; end if;   
      if G`type eq "O-" and d eq 10 and q eq 4 then range := [4..10]; end if;    
      if G`type eq "Sp" and d in [12] then range := [4]; end if;
   end if;
   if #range eq 0 then error "nothing left in range!"; end if;

   if type in ["SL"] and d eq 4 then
      H,m := SXEFindSmallerSLDegree4NatRep(G);
   else

      elt  := []; dim := []; cnt := 0; elt := 0; fls := 0; fst := 0;
      finish := false;
      repeat
         repeat
            fst +:= 1;
            g,gw,rg := getElt(G : range := range);
            if fst mod 4 eq 0 then 
               vprint evenSX,4 : "SXESmallerSXNatRep: constructed",fst,"elts";
            end if;
        until 2*(d-rg) in range;
        exp := 2*(d-rg);
        l := 1;
        while l le 3 and not finish do         
          //not generated by two conjugate elts?
            if (q in [2,3] and  G`type in ["Sp","O+","O-"] and 2*(d-rg) in [4,6,8]) then 
               h,hw,rh := getElt(G : range := range);
               exp     := 2*d-rg-rh;
               gens := [g,h];
               wrds := [gw,hw];             
               elt   +:= 1;
            else
               u, uw  := SXERandomWord(G);
               h      := g^u;
               hw     := gw^uw;
               gens := [g,h];
               wrds := [gw,hw];   
               elt   +:= 1;
            end if;
            H      := sub<Generic(G) | gens>;
            S      := SXESections(H);
            if exists(x){x:x in S|Degree(x) eq exp 
                                   and SXELieTypeNatRep(x) cmpeq <want,exp,q,p>} then  
              finish := true; 
            end if;          
            l := l + 1;
       end while;
       if not finish and fst ge 2000 then error "couldn't find smaller groups"; end if;
       until finish;
       H`UserGenerators := gens;
       SXEInitGroup(H : UserWords := wrds, type := want, natParams := <want,exp,q,p>);
       m  := exp;

   end if;
 
 //now make it pretty and get COB
   S    := SXESections(H);
   degs  := [Degree(S[i]): i in [1..#S]];
   index := Position (degs, m);
   other := Rep([x : x in [1..#S] | x ne index]);
   MA    := MatrixAlgebra (F, d);
   V     := VectorSpace (F, d);
   E     := [* *]; 
   U     := [* *];
   for i in [1..Ngens(H)] do
       alpha := UserGenerators(S[other])[i][1][1];
       E[i]  := Eigenspace (H.i, alpha);
       U[i]  := (H.i -  ScalarMatrix(d, alpha));
   end for; 
 //Basis of intersection of Eigenspaces
   BE := Basis(&meet([x : x in E]));
   Y  := &cat[[U[j][i] : i in [1..d]]: j in [1..#U]];
   B  := Basis(sub < V | Y >); 
   T  := [B[i] : i in [1..#B]] cat [BE[i] : i in [1..#BE]];
   CB := MA ! &cat [Eltseq (t): t in T]; 
   H`cob := CB;
   
 //reduce SL6 further to SL2:
   if type in ["SL"] and d eq 6 and 2 in range then

      F   := BaseRing(H);
      HH  := SXEExtractGroup(SXECopyGroup(H:cob:=H`cob),[1..4]);   

      HH`UserWords := H`UserWords;
      HH`natParams := H`natParams;
      HH`type      := G`type;
      SXEInitGroup(HH);
   
      vprint evenSX, 2: "SXESSmallerSXNatRep: found dim",4,"in deg",6,"now reduce to deg 2";
     
      H2,m  := $$(HH);
      H2`UserWords := Evaluate(H2`UserWords,H`UserWords);

      CB := H2`cob;
      CB := DiagonalJoin(CB,Id(GL(2,F)))*H`cob;;
      oldcb := H`cob;
      ug    := [oldcb^-1*j*oldcb : j in [Generic(G)!DiagonalJoin(h,Id(GL(2,F))) : h in UserGenerators(H2)]];
      ug    := [Generic(G)!i : i in ug];

      H  := sub<Generic(G) | [oldcb^-1*j*oldcb : j in 
            [Generic(G)!DiagonalJoin(h,Id(GL(2,F))) : h in UserGenerators(H2)]]>;
      H`UserGenerators := ug;
      H`UserWords := H2`UserWords;
      H`cob := CB;
      H`natParams := <G`type,2,q,2>;
      H`type      := type;
      SXEInitGroup(H);
    //now CB*H*CB^-1 is pretty
   end if;

   CB := H`cob;
   vprint evenSX, 2: "SXESmallerSXNatRep: found dim",m,"in deg",d;     
   vprint evenSXcpu,1: "runtime SXESmallerSXNatRep deg",d," is",Cputime(rnt);
   vprint evenSX, 2: "end SXSmallerSXNatRep, SLP lengths",[#i : i in H`UserWords];
   return H,m;
end function;



/*********************************************************************/
/* Constructs a smaller classical subgroup of G (NatRep)
/* generated by two conjugate elements.
/*********************************************************************/
intrinsic  SmallerClassicalGroup(G :: Grp :  range:=[], type:=false, onlyBlack := SXEonlyBlack, silent:=true) -> Grp, RngIntElt
{  G is isomorphic to a classical group SX(d,q) where SX is one of 
   "SL","SU","Sp","OmegaPlus","OmegaMinus. The output is a subgroup
   H of G which is isomorphic to SX(m,q) for some m<d. In the natural
   representation, H can be naturally embedded as a subgroup of block
   diagonal matrices with block sizes m and d-m; the base change matrix is attached
   as variable 'cob'. The type of H is the same as the type of G with the following 
   exceptions: If q is even and G is symplectic, then H is of type OmegaPlus. If G is 
   OmegaMinus, then H is of type OmegaPlus. The parameter type is of the form <SX,d,q> 
   where SX is one of  "SL", "Sp", "SU", "O-", "O+". 
}
   if not assigned G`initialised then SXEInitGroup(G : type := type); end if;
   if G`type in ["SL","SU"] and G`natParams[2] in [6] then range := [2,4]; end if;
   if SXEIsNatRep(G) and not onlyBlack then
      return SXESmallerSXNatRep(G:range:=range);
   else
      if SXEIsNatRep(G) and not silent then "SmallerClassicalGroup: COULD USE SMALLER NAT REP BUT DON'T"; end if;
      return SXESmallerSXBlack(G:range:=range);
   end if;
end intrinsic;

/*********************************************************************/
/* Input:   initialised mgrp G, elt g with SLP w (black)
/* Output:  centraliser of g with SLPs (Monte Carlo, Bray's Algorithms)
/*********************************************************************/
SXECentraliserOfInvolution := function(G,g,w: nrg:=0, F:=0)
    vprint evenSX, 3: "start SXECentraliserOfInvolution";
    t := Cputime();
    
    if F cmpeq 0 then F := GF(G`natParams[3]); end if;

    if nrg eq 0 then
       nrg := 25;
       if  #F eq 2 then nrg := 100;
       elif #F eq 4 then nrg := 61;
       elif #F eq 8 then nrg := 30;
       end if;
   end if;

  //completion check for CentraliserOfInvolution
    isCent := function(H,Ccand,inv,Cw) return #UserGenerators(Ccand) ge nrg; end function;
    C,Cw := CentraliserOfInvolution(G, g, w :
                                    Randomiser      := G`RandomProcess,
                                    CompletionCheck := isCent, 
                                    NumberRandom    := 2*nrg);
  
    SXEInitGroup(C : UserWords := Cw, type := "no");
    return C,Cw;
end function;


/*********************************************************************/
/* Input:   initialised matrix group G
/* Output:  derived subgroup of G with SLPs (Monte Carlo)
/* Comment: only needed in Degree4Involution and SolveSLSU5
/*********************************************************************/
SXEDerivedSubgroupWithWords := function(G : NumberOfElements := 10)  
    gens  := []; 
    words := [];
    U     := UserGenerators(G);
    Limit := Minimum(2*#U, #U + 10);  
    nmr   := 0;
    repeat
       nmr +:= 1;
       x, w := SXERandomWord(G);
       for i in [1..#U] do 
           c := (Generic(G)!U[i], x);
           if not (c in gens) and c ne Id(G) then 
               Append(~gens, c);
               Append(~words, (G`SLPGroup.i, w));
           end if;
        end for;
    until nmr ge NumberOfElements and #gens ge Limit;
    D                := sub<Generic(G) | gens>;
    D`UserGenerators := gens;
    words            := Evaluate(words, G`UserWords);
    if assigned G`type then D`type := G`type; end if;
    if assigned G`cob then D`cob := G`cob; end if;
    SXEInitGroup(D : UserWords :=  words); 
    return D;
end function;


/*********************************************************************/                                     
/* Input:   group G and (list of) elements elts in G
/* Output:  (list of) words writing elts as SLPs in UserGens of G   
/*          (used in  SXE_int_testKernel)
/*********************************************************************/      
SXECompositionTreeElementInUserGens := function(G,H,elts)
   vprint evenSX, 3: "start SXECompositionTreeElementInUserGens";  
   if not Type(elts) eq SeqEnum then todo := [elts]; else todo := elts; end if;
   ug := [Generic(G)!u : u in UserGenerators(G)];
   w  := [**];
   for e in todo do
      flg, we := CompositionTreeElementToWord(H,e);
      assert flg;
      Append(~w,we);
   end for;
   map := CompositionTreeNiceToUser(H);
   w   := [Image(map,i) : i in w];
   pos := [Position(ug,H.i) : i in [1..Ngens(H)]]; 
   w   := Evaluate(w,[G`SLPGroup.i : i in pos]);

   vprint evenSX, 3: "end SXECompositionTreeElementInUserGens";   
   if Type(elts) eq SeqEnum then return w; else return w[1]; end if;
end function;


/*********************************************************************/
/* Input:   group G and (list of) elements elts in G
/* Output:  (list of) words writing elts as SLPs in UserGens of G
/*********************************************************************/
SXEapplyMap := function(G,H,elts,map)
   vprint evenSX, 3: "start SXEapplyMap";
   if not Type(elts) eq SeqEnum then todo := [elts]; else todo := elts; end if;
   ug := [Generic(G)!u : u in UserGenerators(G)];
   w  := [*map(e) : e in todo*];
   
   pos := [Position(ug,H.i) : i in [1..Ngens(H)]];
   w   := [*Evaluate(ww,[G`SLPGroup.i : i in pos]) : ww in w*];

   vprint evenSX, 3: "end SXEapplyMap";
   if Type(elts) eq SeqEnum then return w; else return w[1]; end if;
end function;



/*********************************************************************/
/* Input:  matrix group with attached natParams
/* Output: section which has the same type as group
/*********************************************************************/
SXEReduceToSection := function(G)
 
  //return G,false,_,_;

    rnt  := Cputime();
    if SXEIsNatRep(G) or not Type(G) eq GrpMat then return G,false,_,_; end if;
    vprint evenSX, 2: "start SXEReduceToSection";
    S    := SXESections(G);
    COB  := G`ChangeOfBasis;
    d    := G`natParams[2];
    q    := G`natParams[3];
    p    := G`natParams[4];
    type := G`natParams[1];

    valid := [*[*type,d,q*]*];
    if type eq "O-" and d eq 4 then Append(~valid,[*"SL",2,q^2*]); end if;
    if type eq "O-" and d eq 6 then Append(~valid,[*"SU",4,q*]); end if;
    if type eq "O+" and d eq 6 then Append(~valid,[*"SL",4,q*]); end if;
    validd := [[*i[2],i[3]*] : i in valid];

    degs := [Degree(i) : i in S];
    perm := 0;
    Sort(~degs,~perm);
    cand := [i^perm : i in [1..#S]];	
    cand := [i : i in cand | Degree(S[i]) gt 1];

    if #S eq 1 or #cand eq 0 then 
        vprint evenSX, 2: "end SXEReduceToSection (no reduction)";
        return G,false,_,_; 
    end if;
    done := false;
    i    := 1;

    repeat
        K  := S[cand[i]];
        if type eq "O+" and d eq 4 then shouldBe:=<"O+",4>; else shouldBe:=false; end if;
        t  := SXELieType(K:char:=p,shouldBe:=shouldBe,q:=q);
        if not shouldBe cmpeq false and t cmpeq false then
           t := SXEIsOmegaPlus4(S[cand[i]]:q:=q);      
           if not t cmpeq false then done := true; end if;
        end if;
        if not done and not t cmpeq false then done := exists(a){a : a in valid | a eq [*t[1],t[2],t[3]*]};  end if;
        i   +:=1;
    until done or i gt #cand;
    if not done then 
        vprint evenSXcpu, 2: "runtime SXEReduceToSection is", Cputime(rnt); 
        vprint evenSX, 2: "end SXEReduceToSection (no reduction)";  
        return G,false,_,_; 
    end if;

  //"EXPERIMENTAL";
  //K`SLPGroup  := G`SLPGroup;

    K`UserWords := G`UserWords;
    K`natParams := G`natParams;
    K`type      := G`type;
    SXEInitGroup(K);

  //now construct projection onto that block
    nr := cand[i-1];
    if nr gt 1 then offset := &+[Degree(S[j]) : j in [1..nr-1]]; else offset := 0; end if;

    toBlock := function(g) 
        return SXEExtractBlock(COB*g*COB^-1,[offset+1..offset+Degree(S[nr])]); 
    end function;

    vprint evenSXcpu, 2: "runtime SXEReduceToSection from",Degree(G),"to",d,"is", Cputime(rnt);
    vprint evenSX, 2: "end SXEReduceToSection, reduced from",Degree(G),"to",d;
    return K,true,toBlock,COB;
end function;





/***************************************************************************/
/* SXEgetSection: input Centraliser of involution and compatible fixed point
/*                free element fpf with SLP wfpf; all in G of nat rep degree d
/*                and characteristic p; want to extract SX(k,q) of type twant
/*
/* to avoid powering: CLG e-mail from August 16 2013
/*
/**************************************************************************/
SXEgetSection := function(C,fpf,wfpf,G,d,p,k,twant : justPower := false, 
                          nrGA := 30, nrGT := 10, cb := false)

    vprint evenSX, 2: "start SXEgetSection for finding",twant,k;

    q := G`natParams[3];
    F := GF(q);
    if twant eq  "SU" then F := GF(q^2); end if;

  //correct what we are looking for (small degree cases)
    oldk := k;
    if twant eq "O+" and k eq 6 then twant := "SL"; k := 4; end if;
    if twant eq "O-" and k eq 4 then twant := "SL"; k := 2; q:=q^2; end if;
    if twant eq "O-" and k eq 6 then twant := "SU"; k:=4; end if;
    if twant eq "SU" and k eq 2 then twant := "SL";  F:= GF(q); end if;
    vprint evenSX, 2: "   actually, want to find",twant,k;
    rnt := Cputime();

 //for powering up (exp) and to identify what prime orders to avoid (av)
   if twant eq "SL" then   exp := #SL(k,q);         av := q-1;
   elif twant eq "SU" then exp := #SU(k,q);         av := q+1;
   elif twant eq "O+" then exp := #OmegaPlus(k,q);  av := 1;
   elif twant eq "Sp" then exp := #Sp(k,q)        ; av := 1;
   elif twant eq "O-" then exp := #OmegaMinus(k,q); av := 1;
   end if;

 //brutefore: if (d-k)/2 < k then directly power up; if equal, then power up brutefore

   bruteforce := false;
   if (d-oldk) eq 2*k or 
      (twant in ["Sp","O+","O-"] and d in [3*k+2,3*k+4]) or
      (twant in ["O+"] and ((d-oldk) div 2)-k in [-2,2]) or
      (G`type eq "O-" and twant in ["SL"] and d eq 12 )  then 
      bruteforce := true;  
    //problem here: all sections are the same! 
   end if;     

   if (d-k) gt 2*k  and not bruteforce then
      gensA := [Generic(C)|];
      wrdA  := [**];
      for i in [1..nrGA] do
         repeat 
            g,w := SXERandomWord(C); 
            g := g^exp; 
         until not g eq g^0 and not av mod Order(g) eq 0 and not g in gensA;
         Append(~gensA,g);
         Append(~wrdA,w^exp);
      end for;
      bruteforce := false;
  
   elif (d-k) lt 2*k and not bruteforce then
      gensA := [];
      bruteforce := false;
   end if;


 //try it 50 times if bruteforce
   for nrbf in [1..200] do

      nextbf  := false;
      flgfail := 1;
      if bruteforce then 
         vprint evenSX, 3: "SXEgetSection: start bruteforce extraction nr",nrbf; 
      end if;
      
    //try to generate A if all sections are of equal size
      if bruteforce then
   
         repeat repeat g,w := SXERandomWord(C); until not g eq g^0;
            fac := [i : i in Factorisation(Order(g)) | not i[1] eq p and not av mod i[1] eq 0]; 
         until #fac ge 1;
         r   := Random(fac)[1];                                     
         ord := Order(g) div r;                                    
         g   := g^ord; 
         gensA := [*g*];

         for i in [1..20] do Append(~gensA,g^SXERandomWord(C)); end for;
  
      end if;
     
      gensT := [**];
      wrdT  := [];
      gens  := [Generic(G)|];
      wrds  := [];
      ofp   := Order(fpf);
      done  := false; 
      tmp   := (d-k) div 2;
      if twant eq "SL" then pow := #GL(tmp,F);
         elif twant eq "SU" then pow :=  #GU(tmp,q);
         elif twant in ["O+","Sp","O-"] and IsEven(tmp) then pow := #Sp(tmp,F);
         elif twant in ["O+","Sp","O-"] and IsOdd(tmp) then pow := #SL(tmp,F);
      end if;

      repeat

         if #gensA gt 0 then
            repeat repeat g,w := SXERandomWord(C); until not g eq g^0;
               fac := [i : i in Factorisation(Order(g)) | not i[1] eq p and not av mod i[1] eq 0]; 
            until #fac ge 1;  
            r   := Random(fac)[1];
            ord := Order(g) div r;
            g   := g^ord; 
         
            flg := forall(e){e : e in gensA | (e,g) eq g^0 or IsPrimePower(Order((e,g)))};
         
            if flg then w := w^ord; end if;

         else
             
          //"power directly into smaller section";
            nrdir := 0;
            repeat 
               g,w := SXERandomWord(C); 
               g   := g^pow;
               nrdir := nrdir +1;
               if nrdir mod 10000 eq 0 then error "SXEgetSection: stuck in direct powering"; end if;
            until not g eq g^0; 
            w   := w^pow;
            flg := true;

         end if;

         if not flg then flgfail := flgfail + 1; end if;
         if bruteforce and flgfail gt 10 then 
            nextbf := true; 
         end if;   

         if flg and not g in gens then      
           w := Evaluate(w,C`UserWords);
           Append(~gensT,g); 
           Append(~wrdT,w);
           Append(~gens,((fpf*(g)*(fpf*fpf^(g))^((ofp-1) div 2)) )^2); 
           Append(~wrds,((wfpf*(w)*(wfpf*wfpf^(w))^((ofp-1) div 2)))^2);

           if #gens gt 1 and #gens mod 5 eq 0 then
               if #gens ge 100 then
                  if not bruteforce then 
                     if twant eq "Sp" then return false; end if;
                     return false;
                  else
                     nextbf := true;
                  end if;
               end if;              
               K := sub<Generic(C) | gens>;
               K`UserGenerators := gens;
               K`UserWords      := wrds;
               SXEInitGroup(K:UserWords:=wrds, type := "no");
               
               t := false;
               if twant eq "O+" and k eq 4 then
                  t := SXELieType(K:char:=2,shouldBe:=<"O+",4>,q:=q);
               else
                  t := SXELieType(K:char:=2,q:=q,shouldBe:=<twant,k,q,p>); 
               end if; 

               if t cmpeq <twant,k,q,p> then 
                  done :=true;
               end if;    
            end if;
       end if;

     until done or nextbf; 

     if done then
          vprint evenSXcpu,1: "runtime SXEgetSection for finding",twant,k," is",Cputime(rnt);
          vprint evenSX, 2: "end SXEgetSection for finding",twant,k;
          K`natParams := t;
          K`type := t[1];
          return K;
       end if;
   end for;
   if twant eq "Sp" then return false; end if;
   return false;
end function;


/***************************************************************************/
/* check whether elts satisfy presentation of classical group of type type d,q
/* (elts should be ClassicalStandardGenerators)
/***************************************************************************/
SXEcheckPresentation := function(type,elts,d,q : justCheck:=false)
    vprint evenSX, 2: "SXEcheckPresentation:",type,d,q;
    	  
    if type in ["Sp","SU"] and d eq 2 then
        "need d>2 for checking pres";
        return true;
    end if;
    if type eq "O+" then type := "Omega+"; elif type eq "O-" then type := "Omega-"; end if;
    Q,R := ClassicalStandardPresentation (type, d,q);
    allok :=  #Set (Evaluate (R, elts)) eq 1;
    if not allok then 
        if justCheck then return false; else error "PRESENTATION WRONG for",type,d,q; end if;
    end if;
    vprint evenSX, 2: "SXEcheckPresentation: tested",type,d,q;
    return true;
end function;


/***************************************************************************/                  
/* provides std gens which are to construct;; plus good involution and fpf elt   
/* first elts are ClassicalStandardGens, inv and fpf is elt 10 and 11  
/***************************************************************************/    
SXEElementsToConstruct := function(type,d,q : std := false)

   if type eq "O-" then type := "Omega-"; elif type eq "O+" then type := "Omega+"; end if;
   elts := ClassicalStandardGenerators(type,d,q);
   for i in [#elts+1..9] do Append(~elts,elts[1]^0); end for;
   
 //now construct involution and fpf elt
   if type eq "SL" then
      if IsEven(d) then
         inv := GL(2,GF(q))![1,1,0,1];
         f   := elts[4][1][1];
         fpf := GL(2,GF(q))![f,0,0,f^-1]; 
         for i in [1..(d div 2)-1] do 
            inv := DiagonalJoin(inv,GL(2,GF(q))![1,1,0,1]); 
            fpf := DiagonalJoin(fpf,GL(2,GF(q))![f,0,0,f^-1]);
         end for;
         inv := GL(d,q)!inv;
         fpf := GL(d,q)!fpf;
      else 
         inv := One(GL(d,q));
         fpf := One(GL(d,q));
      end if;
      Append(~elts,inv); 
      Append(~elts,fpf);
   elif type eq "SU" then 
      F   := GF(q^2);
      bl  :=  GL(2,F)![1,1,0,1];
      inv := bl;
      for i in [1..(d div 2)-1] do inv := DiagonalJoin(inv,bl); end for;
      if d eq 2 then inv := bl; end if;
      if IsOdd(d) then inv := DiagonalJoin(inv,Id(GL(1,F))); end if;
      inv := GL(d,F)!inv;
      Append(~elts,inv);
      if IsEven(d) then
         gam      := elts[4][1][1];
         bl       := GL(2,F)![gam,0,0,gam^-1];
         fpf      := bl;
         for i in [1..(d div 2)-1] do fpf := DiagonalJoin(fpf,bl); end for;
         if d eq 2 then fpf := bl; end if;
         fpf := GL(d,F)!fpf;
         Append(~elts,fpf);
      else
         Append(~elts,elts[1]^0);
      end if;
      if std then 
         if d eq 2 then elts := [GL(2,q)!e : e in elts]; end if;
         return elts; 
      end if;

    //adjust elements to form
      bl := GL(2,F)![0,1,1,0];  
      f2 := bl;
      for i in [1..(d div 2) -1] do f2 := DiagonalJoin(f2,bl); end for;
      if IsOdd(d) then f2 := DiagonalJoin(f2,Id(GL(1,F))); end if;
      cob := TransformForm(f2,"unitary");
      elts := [cob^-1*i*cob : i in elts];
 
   //write SU(2,q) as SL(2,q)
      if d eq 2 then
        elts := [GL(2,q)!e : e in elts];
      end if;

   elif type eq "Sp" then

      inv := GL(2,GF(q))![1,1,0,1];
      f   := elts[4][1][1];
      fpf := GL(2,GF(q))![f,0,0,f^-1]; 
      for i in [1..(d div 2)-1] do 
         inv := DiagonalJoin(inv,GL(2,GF(q))![1,1,0,1]); 
         fpf := DiagonalJoin(fpf,GL(2,GF(q))![f,0,0,f^-1]);
      end for;
      inv := GL(d,q)!inv;
      fpf := GL(d,q)!fpf;
      Append(~elts,inv); 
      Append(~elts,fpf);

      if std then return elts; end if;

    //adjust elements to form
      bl := GL(2,q)![0,1,1,0];  
      f2 := bl;
      for i in [1..(d div 2) -1] do f2 := DiagonalJoin(f2,bl); end for;
      cob := TransformForm(f2,"symplectic");
      elts := [cob^-1*i*cob : i in elts];

   elif type eq "Omega+" then

   //add good involution and fpf element
      F := GF(q);
      if d mod 4 eq 0 then
         m   := d div 4;
         el1 := GL(4,F)![1,0,0,1, 0,1,0,0, 0,1,1,0, 0,0,0,1];
         el2 := GL(4,F)![F.1,0,0,0, 0,F.1^-1,0,0, 0,0,F.1^-1,0,0,0,0,F.1];
         inv := el1;
         fpf := el2;
         for i in [1..m-1] do
            inv := DiagonalJoin(inv,el1);
            fpf := DiagonalJoin(fpf,el2);
         end for;
     else
         inv := Id(GL(d,F));
         fpf := Id(GL(d,F));
     end if;
    Append(~elts,inv);
    Append(~elts,fpf);

    if std then return elts; end if;

   //adjust elements to form
    bl := MatrixAlgebra(GF(q),2)![0,1,0,0];
    f2 := bl;
    for i in [1..(d div 2) -1] do f2 := DiagonalJoin(f2,bl); end for;
    cob := TransformForm(f2,"orthogonalplus");
    elts := [cob^-1*i*cob : i in elts];
     
   elif type eq "Omega-" then
      w := elts[3][d-3][d-3];
      gamma := PrimitiveElement(GF(q^2));
      for i in [1..q - 1] do
         if (gamma^i)^(q + 1) eq w then pow := i; break i; end if;
      end for;
      gamma := gamma^pow;
      assert gamma^(q + 1) eq w;

      elts[6] := GL(d,q)!DiagonalJoin(GL(2,q)![w,0,0,w^-1],Id(GL(d-2,q)));
    //fpf elt for glue, which is compatible with base change of involution...
      x := gamma+gamma^q;
      fpf4glue := GL(4,q)![0,1,0,0, 1,0,0,0, 0,0,1,0, 0,0,x,1];
      if d gt 4 then fpf4glue := DiagonalJoin(Id(GL(d-4,q)),fpf4glue); end if;
      elts[7] := fpf4glue;

      if std then return elts; end if;

   //adjust elements to form
      bl := MatrixAlgebra(GF(q),2)![0,1,0,0];
      f2 := bl;
      for i in [1..(d div 2)-2] do f2 := DiagonalJoin(f2,bl); end for;
      f2 := DiagonalJoin(f2,GL(2,q)![1,gamma+gamma^q,0,gamma^(q+1)]);

    //t, f3 := QuadraticForm(sub<GL(d,q)|elts>);
    //assert f2 eq f3; 

      cob := TransformForm(f2,"orthogonalminus");
      elts := [cob^-1*i*cob : i in elts];
   end if;
  
   return elts;
end function;



/***************************************************************************/
/* an internal function to check whether red to section was isom.
/***************************************************************************/
SXE_int_testKernel := function(K,Kred,Kc,toBlock:map:=false)
   eltorg := [ Random(K) : i in [1..3]];
   eltim  := [ toBlock(k) : k in eltorg];
   if  map cmpeq false then
      vprint evenSX, 2:"SXE_int_testKernel: using CT and evaluate";
      wrds   := [ SXECompositionTreeElementInUserGens(Kred,Kc,k) : k in eltim];
   else
      vprint evenSX, 2:"SXE_int_testKernel: using map and evaluate";
      m4     := Function(map);
      wrds   := [SXEapplyMap(Kred,Kc,k,m4) : k in eltim];
   end if;
   newelt :=  Evaluate(wrds,UserGenerators(K));
   if not newelt eq eltorg then
      vprint evenSX, 2:"SXE_int_testKernel: end  with FALSE";
      return false;
   end if;
   vprint evenSX, 2:"SXE_int_testKernel: end with TRUE";
   return true;
end function;


/***************************************************************************/                  
/* glue in SL (black)
/***************************************************************************/    
SXEGlueSL := function(G,eltA,wA,eltB,wB,m)

    nP  := G`natParams; d := nP[2]; q := nP[3]; p:=nP[4];
    F   := GF(q);
    rnt := Cputime(); 
    vprint evenSX, 2: "start SXEGlueSL for gluing",m,d-m;

  //find involution
    c1     := eltA[2]^-2;
    c1w    := wA[2]^-2;
    i      := ((m-2) div 2) -1;
    i1     := eltA[3];
    w1     := wA[3];
    for j in [1..i] do  
        i1   := i1*eltA[3]^(c1^(j)); 
        w1   := w1*wA[3]^(c1w^(j)); 
    end for;

    c2     := eltB[2]^-2;
    c2w    := wB[2]^-2;
    if IsEven(d-m) then
        i      := ((d-m-2) div 2) -1;
        i2     := eltB[3]^(c2);
        w2     := wB[3]^(c2w);
        for j in [1..i] do 
            i2   := i2*eltB[3]^(c2^(j+1)); 
            w2   := w2*wB[3]^(c2w^(j+1));
        end for;
    elif IsOdd(d-m) and (d-m gt 3) then
        i      := ((d-m-3) div 2) -1;
        i2     := eltB[3]^(c2);
        w2     := wB[3]^(c2w);
        for j in [1..i] do
            i2   := i2*eltB[3]^(c2^(j+1));
            w2   := w2*wB[3]^(c2w^(j+1));
        end for;
    elif d-m eq 3 then
       i2 := eltB[1]^0;
       w2 := wB[1]^0;
    end if;
   
    inv    := i1*i2;
    winv   := w1*w2;

  //find gens for two SL2s
    sl1    := [Generic(G) | eltA[i]^(eltA[2]^2) : i in [1,3,4]];
    sl1w   := [wA[i]^(wA[2]^2) : i in [1,3,4]];
    sl2    := [Generic(G) | eltB[i]  : i in [1,3,4]];
    sl2w   := [wB[i] : i in [1,3,4]];

  //find fpf element
    if m gt 4 then
        fp1  := &*[eltA[4]^(eltA[2]^(-2*j)) : j in [0..((m-2) div 2)-1]];
        wfp1 := &*[wA[4]^(wA[2]^(-2*j)) : j in [0..((m-2) div 2)-1]];
    else 
        fp1  := eltA[4]; wfp1 := wA[4];
    end if;
    if d-m eq 4 then
        fp2  := eltB[4]^(eltB[2]^-2); wfp2 := wB[4]^(wB[2]^-2);
    elif IsEven(d-m) then
        fp2  := &*[eltB[4]^(eltB[2]^(-2*j)) : j in [1..((d-m-2) div 2)]];
        wfp2 := &*[wB[4]^(wB[2]^(-2*j)) : j in [1..((d-m-2) div 2)]];
    elif IsOdd(d-m) and (d-m) gt 3 then
        fp2  := &*[eltB[4]^(eltB[2]^(-2*j)) : j in [1..((d-m-3) div 2)]];
        wfp2 := &*[wB[4]^(wB[2]^(-2*j)) : j in [1..((d-m-3) div 2)]];
    elif d-m eq 3 then 
        fp2 := fp1^0; wfp2 := wfp1^0;
    end if;
    fp  := fp1*fp2;
    wfp := wfp1*wfp2;

    if d eq 6 and m eq 2 then
        inv  := i2;  winv := w2; fp   := fp2; wfp  := wfp2;
    elif d eq 7 then
        inv := i1; winv := w1; fp := fp1; wfp := wfp1;
    end if;


  //now extract SL4 and SL5 respectively
    C, Cw := SXECentraliserOfInvolution(G, inv, winv);
    if IsEven(d) then k:=4; else k:=5; end if;
   
  //test to get correct section; relevant for d=12,15, for example
    nrgetSec := 1;  
    goodSection := true;
    repeat
       goodSection := true;
       if nrgetSec gt 1 then 
           vprint evenSX, 3: "----- have to extract section another time, nr",nrgetSec; 
       end if;
       K := SXEgetSection(C,fp,wfp,G,d,p,k,"SL"); 

       if K cmpeq false then error "error in SXEgetSection"; end if;

       K`natParams := <"SL",k,q,2>;
       K`type      := "SL";

       Kred, red, toBlock := SXEReduceToSection(K);
 
       Kred`UserWords := K`UserWords;    
       Kc := SXECopyGroup(Kred);
       Kc`UserWords := Kred`UserWords;
       ug := [Generic(Kred)!u : u in UserGenerators(Kred)];  //UserGenerators(Kred);

       vprint evenSX, 2: "start CT in glue for SL",k;
   
       CT  := CompositionTree(Kc);

       if CT cmpeq [] then assert false; end if;
       CTO := CompositionTreeOrder(Kc);
       if not CTO eq #SL(k,q) then goodSection := false; end if;

     //check kernel of red
       if goodSection and red then
          goodSection := SXE_int_testKernel(K,Kred,Kc,toBlock);
       end if;

     //HD: have to do it so that SLPGroup is correct in black context
      pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
      Kc`UserWords := [Kred`UserWords[i] : i in pos];

      nrgetSec := nrgetSec + 1;
    until goodSection;

  //reduce to section; shouldn't have to worry about orig copy since we have to evaluate anyway
  //make sure to also reduce the elements in sl1 and sl2 to sections
    SXEInitGroup(Kc : type:=Kred`type, natParams:=Kred`natParams);
    if red then
        sl1 := [Generic(Kc)| toBlock(i) : i in sl1];
        sl2 := [Generic(Kc)| toBlock(i) : i in sl2];
    end if;

    if SXEIsNatRep(Kc) then
      slk    := Kc;
      sl1ims := sl1;
      sl2ims := sl2;
    else
        _,m2,m3,m4  := CompositionTreeSeries(Kc);
       vprint evenSX, 3: "done, now apply maps";
       nr     := [i : i in [1..#m4] | Type(Domain(m4[i])) eq GrpMat and
                                           Degree(Domain(m4[i])) eq k];
       if #nr eq 0 then error "couldn't find correct SU"; end if;
       
       nr     := nr[1];
       slk    := Codomain(m2[nr]);
       m2     := Function(m2[nr]);
       m3     := Function(m3[nr]);
       m4     := Function(m4[nr]);
       sl1ims := [Generic(slk)|m2(j) : j in sl1];
       sl2ims := [Generic(slk)|m2(j) : j in sl2];
   end if;

    if k eq 4 then
        want := Generic(slk)![1,0,0,0, 0,0,1,0, 0,1,0,0, 0,0,0,1];
    else
        want := Generic(slk)![1,0,0,0,0, 0,0,1,0,0, 0,1,0,0,0, 0,0,0,1,0, 0,0,0,0,1];
    end if;

    MM  := MatrixAlgebra(GF(q),k);
    tmp := MM!sl1ims[2];
    v2 := Basis(Image(tmp-tmp^0));
    assert #v2 eq 1;
    v2 := v2[1];
    v1 := v2*sl1ims[1];
    tmp := MM!sl2ims[2];
    v4 := Basis(Image(tmp-tmp^0));
    assert #v4 eq 1;
    v4 := v4[1];
    v3 := v4*sl2ims[1];
    
  //try this here, which also works for q=2
    if k eq 5 then 
        V5   := Eigenspace(sl1ims[1]*sl1ims[2],1) meet Eigenspace(sl2ims[1]*sl2ims[2],1);
        v5   := Basis(V5)[1];
        cob  := Generic(slk)!Eltseq([Eltseq(j) : j in [v1,v2,v3,v4,v5]]);
    else
        cob  := Generic(slk)!Eltseq([Eltseq(j) : j in [v1,v2,v3,v4]]);
    end if;
 
    want   := cob^-1*want*cob;
    want   := Generic(slk)!want;
   
   if SXEIsNatRep(Kc) then 
      f,wantw := LMGIsIn(Kc,want);
      pos     := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
      nslp    := [K`SLPGroup.i : i in pos]; 
      wantw   := Evaluate(wantw,nslp);
      wantw   := Evaluate(wantw,K`UserWords);
      want    := Evaluate(wantw,UserGenerators(G));   
   else
       Knice  := CompositionTreeNiceGroup(Kc);
       rew,wr := CompositionTreeNiceToUser(Kc);
       wantw  := m4(want); 
       wantw  := Evaluate(wantw,wr);
       pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
       nslp   := [K`SLPGroup.i : i in pos]; 
       wantw  := Evaluate(wantw,nslp);
       wantw  := Evaluate(wantw,K`UserWords);
       want   := Evaluate(wantw,UserGenerators(G));
   end if;     

    eltA[2]  := eltA[2]*want*eltB[2];
    wA[2]    := wA[2]*wantw*wB[2];
    
    eltA[10] := eltA[10]*eltB[10];
    wA[10]   := wA[10]*wB[10];
    eltA[11] := eltA[11]*eltB[11];
    wA[11]   := wA[11]*wB[11];  

    vprint evenSXcpu,1: "runtime SXEGlueSL in deg",d," is",Cputime(rnt);
    vprint evenSX, 2: "end SXEGlueSX in degree",d;
    return eltA, wA;

end function;



/****************************************************************************/
/* glue cycles to obtain standard generators (black)
/****************************************************************************/
SXEGlueSU := function(G,eltA,wA,eltB,wB,m)
    nP  := G`natParams; d := nP[2]; q := nP[3]; p:=nP[4];
    F   := GF(q^2);
    rnt := Cputime();

    if IsEven(d) then
       c := eltA[2]^2; cw := wA[2]^2;
       for i in [6,7] do eltA[i] := eltA[i]^c; wA[i] := wA[i]^cw; end for;
    end if;

  //find Involution
    c1     := eltA[2];
    c1w    := wA[2];
    i      := ((m-2) div 2) -1;
    i1     := eltA[3];
    w1     := wA[3];
    for j in [1..i] do 
        i1   := i1*eltA[3]^(c1^(j)); 
        w1   := w1*wA[3]^(c1w^(j)); 
    end for;

    c2     := eltB[2];
    c2w    := wB[2];
    if IsEven(d-m) then
        i      := ((d-m-2) div 2) -1;
        i2     := eltB[3]^(c2);
        w2     := wB[3]^(c2w);
        for j in [1..i] do 
            i2   := i2*eltB[3]^(c2^(j+1)); 
            w2   := w2*wB[3]^(c2w^(j+1));
        end for;
    else
        i      := ((d-m-3) div 2) -1;
        i2     := eltB[3]^(c2);
        w2     := wB[3]^(c2w);
        for j in [1..i] do
            i2   := i2*eltB[3]^(c2^(j+1));
            w2   := w2*wB[3]^(c2w^(j+1));
        end for;
    end if;
      
    inv    := i1*i2;
    winv   := w1*w2;

  //find gens for two SL2s
    sl1    := [Generic(G) | eltA[i]^(eltA[2]^-1) : i in [1,3,4]];
    sl1w   := [wA[i]^(wA[2]^2) : i in [1,3,4]];
    sl2    := [Generic(G) | eltB[i]  : i in [1,3,4]];
    sl2w   := [wB[i] : i in [1,3,4]];
  
  //find fpf element
    if m gt 4 then
        fp1  := &*[eltA[4]^(eltA[2]^(j)) : j in [0..((m-2) div 2)-1]];
        wfp1 := &*[wA[4]^(wA[2]^(j)) : j in [0..((m-2) div 2)-1]];
    else 
        fp1  := eltA[4]; wfp1 := wA[4];
    end if;
    if d-m in [2,4] then // case 2 just to define fp2; won't need this elt
        fp2  := eltB[4]^(eltB[2]); wfp2 := wB[4]^(wB[2]);
    elif IsEven(d-m) then
        fp2  := &*[eltB[4]^(eltB[2]^(j)) : j in [1..((d-m-2) div 2)]];
        wfp2 := &*[wB[4]^(wB[2]^(j)) : j in [1..((d-m-2) div 2)]];
    elif IsOdd(d-m) and (d-m) gt 3 then
        fp2  := &*[eltB[4]^(eltB[2]^(j)) : j in [1..((d-m-3) div 2)]];
        wfp2 := &*[wB[4]^(wB[2]^(j)) : j in [1..((d-m-3) div 2)]];
    elif d-m eq 3 then 
        fp2 := fp1^0; wfp2 := wfp1^0;
    end if;
    fp  := fp1*fp2;
    wfp := wfp1*wfp2;

    if d eq 6 and m eq 2 then
        inv  := i2;  winv := w2; fp   := fp2; wfp  := wfp2;
    elif d eq 6 and m eq 4 then
        inv := i1; winv := w1; fp := fp1; wfp := wfp1;
    elif d eq 7 then
        inv := i1; winv := w1; fp := fp1; wfp := wfp1;
    end if;

  //now extract SU4 and SU5 respectively
    C, Cw := SXECentraliserOfInvolution(G, inv, winv);    
    if IsEven(d) then k:=4; else k:=5; end if;
  
    nrgetSec := 1;  
    goodSection := true;
    repeat
       goodSection := true;
       if nrgetSec gt 1 then 
           vprint evenSX, 3: "----- have to extract section another time, nr",nrgetSec; 
       end if;

       K := SXEgetSection(C,fp,wfp,G,d,p,k,"SU"); 

       if K cmpeq false then error "error in SXEgetSection"; end if; 

       K`natParams := <"SU",k,q,2>;
       K`type      := "SU";

       Kred, red, toBlock, COB := SXEReduceToSection(K); 
       Kred`UserWords := K`UserWords;    
       Kc := SXECopyGroup(Kred);
       Kc`UserWords := Kred`UserWords;
       ug := [Generic(Kred)!u : u in UserGenerators(Kred)]; //UserGenerators(Kred);
 
     //vprint evenSX, 2: "start composition tree in glue for SU",k;
     //CT  := CompositionTree(Kc);
     //CTO := CompositionTreeOrder(Kc);
     //if not CTO eq #SU(k,q) then goodSection := false; end if;

       recsu4 := false;
       if k eq 5 or (Degree(Kc) eq k) then
      
          vprint evenSX, 2: "start composition tree in glue for SU",k;
          CT  := CompositionTree(Kc);
          CTO := CompositionTreeOrder(Kc);
          if not CTO eq #SU(k,q) then goodSection := false; end if;

     //for k=4 do not use CT/CTSeries, but RecSU4
     //because CTSeries (later) does not always
     //give SU(4,q) as std copy

       elif k eq 4 then

          vprint evenSX,2:" start RecSU4 in GlueSU with",Kc`natParams;
          recsu4 := true;
          ff,m2,m3,m4  := RecogniseSU4(Kc,q);
          if not ff then goodSection := false; end if;

       end if;


       nrgetSec := nrgetSec + 1;

     //check kernel of red
    // if goodSection and red then
    //    goodSection := SXE_int_testKernel(K,Kred,Kc,toBlock);
    // end if;

      if goodSection and red then
          if recsu4 then 
             goodSection := SXE_int_testKernel(K,Kred,Kc,toBlock:map:=m4); 
          else
             goodSection := SXE_int_testKernel(K,Kred,Kc,toBlock);
          end if;
       end if;


     //"NOW RESET GROUP"; 
     //HD: have to do it so that SLPGroup is correct in black context
      pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
      Kc`UserWords := [Kred`UserWords[i] : i in pos];
      
    until goodSection;

  //reduce to section; shouldn't have to worry about orig copy since we have to evaluate anyway
  //make sure to also reduce the elements in sl1 and sl2 to sections
    SXEInitGroup(Kc : type:=Kred`type, natParams:=Kred`natParams);

    if red then
        sl1 := [Generic(Kc)| toBlock(i) : i in sl1];
        sl2 := [Generic(Kc)| toBlock(i) : i in sl2];
    end if;


   if SXEIsNatRep(Kc)  then 
       slk := Kc;
       sl1ims := sl1;
       sl2ims := sl2;
   elif k eq 5 then
       _,m2,m3,m4  := CompositionTreeSeries(Kc);
       vprint evenSX, 3: "done, now apply maps";
       nr     := [i : i in [1..#m4] | Type(Domain(m4[i])) eq GrpMat and
                                           Degree(Domain(m4[i])) eq k];
       if #nr eq 0 then 
           error "couldn't find correct SU"; 
       end if;
       
       nr     := nr[1];
       slk    := Codomain(m2[nr]);
       m2     := Function(m2[nr]);
       m3     := Function(m3[nr]);
       m4     := Function(m4[nr]);
       sl1ims := [Generic(slk)|m2(j) : j in sl1];
       sl2ims := [Generic(slk)|m2(j) : j in sl2];
    elif k eq 4 then
     //have maps from above!
       vprint evenSX, 3: "done, now apply maps";
       slk    := m2(Kc);
       m3     := Function(m3);
       m2     := Function(m2);
       m4     := Function(m4);
       sl1ims := [Generic(slk)|m2(j) : j in sl1];
       sl2ims := [Generic(slk)|m2(j) : j in sl2];
    end if;
 
  //also working for q=2
    MM  := MatrixAlgebra(F,k);
    tmp := MM!sl1ims[2];
    v2 := Basis(Image(tmp-tmp^0));
    assert #v2 eq 1;
    v2 := v2[1];
    v1 := v2*sl1ims[1];
    tmp := MM!sl2ims[2];
    v4 := Basis(Image(tmp-tmp^0));
    assert #v4 eq 1;
    v4 := v4[1];
    v3 := v4*sl2ims[1];
 
  //try this here, which also works for q=2
    if k eq 5 then 
        V5   := Eigenspace(sl1ims[1]*sl1ims[2],1) meet Eigenspace(sl2ims[1]*sl2ims[2],1);
        v5   := Basis(V5)[1];
        cob  := Generic(slk)!Eltseq([Eltseq(j) : j in [v1,v2,v3,v4,v5]]);
    else
        cob  := Generic(slk)!Eltseq([Eltseq(j) : j in [v1,v2,v3,v4]]);
    end if;

    f,form := UnitaryForm(sub<Generic(slk)|[cob*i*cob^-1: i in UserGenerators(slk)]>);
    assert f;
    s      := form[3][4];
    x      := Root(s^-1,q+1);
    y      := x^-1;

  //form is diag( (01/10), (0s,/s0), (t) )
  //want to find glue in form (00x0;000x;x^-1000;0x^-100) so that it preseves form:
    if k eq 4 then
        want := Generic(slk)![0,0,x,0, 0,0,0,x, y,0,0,0, 0,y,0,0];
    else
        want := Generic(slk)![0,0,x,0,0, 0,0,0,x,0, y,0,0,0,0, 0,y,0,0,0, 0,0,0,0,1];
    end if;

    want   := cob^-1*want*cob;
    want   := Generic(slk)!want;
  
   if SXEIsNatRep(Kc) then   
      f,wantw := LMGIsIn(Kc,want);
      if not f then error "LMGIsIn returned false in SXEGlueSU"; end if;
      pos     := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
      nslp    := [K`SLPGroup.i : i in pos]; 
      wantw   := Evaluate(wantw,nslp);
      wantw   := Evaluate(wantw,K`UserWords);
      want    := Evaluate(wantw,UserGenerators(G));      
   elif k eq 5 then  
    
       Knice  := CompositionTreeNiceGroup(Kc);
       rew,wr := CompositionTreeNiceToUser(Kc);
       wantw  := m4(want); 
       wantw  := Evaluate(wantw,wr);
       pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
       nslp   := [K`SLPGroup.i : i in pos]; 
       wantw  := Evaluate(wantw,nslp);
       wantw  := Evaluate(wantw,K`UserWords);
       want   := Evaluate(wantw,UserGenerators(G));
   elif k eq 4 then
       want   := m3(want);
       wantw  := m4(want);
       pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
       nslp   := [K`SLPGroup.i : i in pos];
       wantw  := Evaluate(wantw,nslp);
       wantw  := Evaluate(wantw,K`UserWords);
       want   := Evaluate(wantw,UserGenerators(G));
   end if;

  //now glue and put gens together
    eltA[2] := eltB[2]*want*eltA[2];
    wA[2]   := wB[2]*wantw*wA[2];

  //take gens of second copy; does not word for d=7
    if k eq 5 then
        c  := eltA[2]^(-(m div 2));
        wc := wA[2]^(-(m div 2));
        for i in [1,3,4,5] do 
            eltA[i] := eltB[i]^c;
            wA[i]   := wB[i]^wc;
        end for;
    end if;
  
    eltA[10] := eltA[10]*eltB[10];
    wA[10]   := wA[10]*wB[10];
    eltA[11] := eltA[11]*eltB[11];
    wA[11]   := wA[11]*wB[11];  
  
    if IsOdd(d) then
        eltA[6] := eltB[6]; wA[6] := wB[6];
        eltA[7] := eltB[7]; wA[7] := wB[7];
    end if;

    if IsEven(d) then
       c := eltA[2]^-2; cw := wA[2]^-2;
       for i in [6,7] do eltA[i] := eltA[i]^c; wA[i] := wA[i]^cw; end for;
    end if;

    vprint evenSXcpu,1: "runtime SXEGlueSU in deg",d," is",Cputime(rnt);
    vprint evenSX, 2: "end SXEGlueSU in degree",d;
    return eltA, wA;

end function;


/****************************************************************************/
/* recognising SL4 as OmegaPlus6
/****************************************************************************/
RecogniseSLAlternatingSquare := function(G)

//     flag, H   := RecogniseAlternatingSquare(G);
     flag, H := RecogniseSmallDegree (G, "SL", 4, #BaseRing (G));
     if not flag then return false,_,_; end if;
     // iso       := func<g | AlternatingSquarePreimage(G, g)>;
     iso       := func<g | x where _, x := SmallDegreePreimage(G, g)>;
     M         := GModule(ExteriorSquare(H));
     flag, cbm := IsIsomorphic(GModule(G), M);
     if not flag then error "module not isom in RecogniseSLAlternatingSquare"; end if;
     cbm := Generic(G)!cbm;
     inv := func<g | Generic(G) ! (cbm * ExteriorSquare(g) * cbm^(-1))>;
     return true, iso, inv;
end function;


/****************************************************************************/
/* glue cycles to obtain standard generators (black)
/****************************************************************************/
SXEGlueOp := function(G,eltA,wA,eltB,wB,m)
    nP  := G`natParams; d := nP[2]; q := nP[3]; p := nP[4];
    F   := GF(q^2);
    rnt := Cputime();

    vprint evenSX, 2: "start SXEGlueOp in degree",d;
 
  //find Involution
    c1     := eltA[8]^2;
    c1w    := wA[8]^2;
    i      := ((m-4) div 4) -1;
    i1     := eltA[2];
    w1     := wA[2];
    for j in [1..i] do
        i1   := i1*eltA[2]^(c1^(j));
        w1   := w1*wA[2]^(c1w^(j));
    end for;

    c2     := eltB[8]^2;
    c2w    := wB[8]^2;
    if (d-m) mod 4 eq 0 then
        i      := ((d-m-4) div 4) -1;
        i2     := eltB[2]^(c2);
        w2     := wB[2]^(c2w);
        for j in [1..i] do
            i2   := i2*eltB[2]^(c2^(j+1));
            w2   := w2*wB[2]^(c2w^(j+1));
        end for;
    else
        i2     := eltB[2]^eltB[8];
        w2     := wB[2]^wB[8];
        i      := ((d-m-6) div 4);
        for j in [1..i] do
            i2   := i2*eltB[2]^(eltB[8]*c2^j);
            w2   := w2*wB[2]^(wB[8]*c2w^j);
        end for;

    end if;

    inv  := i2;
    winv := w2;
    if m gt 4 then inv := i1*inv;  winv := w1*winv; end if;
    if d-m eq 4 then inv := i1; winv := w1; end if;

 //find gens for first Omega4s
    sl1    := [Generic(G) | eltA[i]^(eltA[8]^-2) : i in [5,2,6,3,4,1,4]];
    sl1w   := [wA[i]^(wA[8]^-2) : i in [5,2,6,3,4,1,4]];

  //find gens for second subgroup (Omega4 if (d-m) divisible by 4
    if (d-m) mod 4 eq 0 then
        sl2    := [Generic(G) | eltB[i]  : i in [5,2,6,3,4,1,4]];
        sl2w   := [wB[i] : i in [5,2,6,3,4,1,4]];
    else
        sl2    := [Generic(G) | eltB[6]*eltB[3]]; 
        sl2w   := [wB[6]*wB[3]];
    end if;


  //find fpf element
    if m gt 4 then
        fp1  := &*[eltA[6]^(eltA[8]^(2*j)) : j in [0..((m-4) div 4)-1]];
        wfp1 := &*[wA[6]^(wA[8]^(2*j)) : j in [0..((m-4) div 4)-1]];
    else
        fp1  := eltA[6]; wfp1 := wA[6];
    end if;
    if d-m eq 4 then
        fp2  := eltB[6]^(eltB[8]^2); wfp2 := wB[6]^(wB[8]^2);
    elif (d-m) mod 4 eq 0 then
        fp2  := &*[eltB[6]^(eltB[8]^(2*j)) : j in [1..((d-m-4) div 4)]];
        wfp2 := &*[wB[6]^(wB[8]^(2*j)) : j in [1..((d-m-4) div 4)]];
    else 
      //fpf that commutes with inv; not necessary though
        tmp  := (eltB[6]*eltB[3])^(eltB[8]);
        wtmp := (wB[6]*wB[3])^wB[8];
        tmp  := tmp^-1*tmp^eltB[8];
        wtmp := wtmp^-1*wtmp^wB[8];
        fp2  := &*[tmp^(eltB[8]^(2*j)) : j in [0..((d-m-4) div 4)]];
        wfp2 := &*[wtmp^(wB[8]^(2*j)) : j in [0..((d-m-4) div 4)]];
    end if;

    fp  := fp2;
    wfp := wfp2;
    if m gt 4 then fp:=fp1*fp2; wfp := wfp1*wfp; end if;
    if d-m eq 4 then fp:=fp1; wfp := wfp1; end if;


  //"IN GLUE!!";
  //assert (inv,fp) eq inv^0;
  //"commute";
  //XXXXX
  //this is not necessary in general, but here we use it to avoid the following:
  //   SXEtestStdGens([14..30 by 2],[8],10,"O+":seed:=[1084230313,20275234]);   
  // problem is: old fpf did NOT commute with inv  
  // this does not cause problems if we apply to correct elts in middle block (1,u,1)
  // because we will still get (1,u^2,1)
  // BUT, it  will EXTEND the top left block if applied to wrong elts like (u,1,u)!
  // this had the consequence that K=getSection was NOT in C anymore!!!
  // and this had the consequence that the top block changed from
  // sth containing Sp to SL(4,q), which we detected as OmegaPlus(6)
  //

  //now extract OmegaPlus8 / OmegaPlus6
    C, Cw := SXECentraliserOfInvolution(G, inv, winv);

    if (d-m) mod 4 eq 0 then k:=8; else k:=6; end if;
 
    nrgetSec := 1;  
    goodSection := true;
    repeat

       goodSection := true;
       if nrgetSec gt 1 then 
           vprint evenSX, 3: "----- have to extract section another time, nr",nrgetSec; 
       end if;
       K := SXEgetSection(C,fp,wfp,G,d,p,k,"O+"); 

       if K cmpeq false and not 8 in [m,d-m] then 
          error "error in SXEgetSection"; 
       elif K cmpeq false and 8 in [m,d-m] then
          return false,false,false;
       end if;

       K`natParams := <"O+",k,q,2>;
       K`type      := "O+";

       Kred, red, toBlock,COB := SXEReduceToSection(K); 

       Kred`UserWords := K`UserWords;    
       Kc := SXECopyGroup(Kred);
       Kc`UserWords := Kred`UserWords;
       ug :=  [Generic(Kred)!u : u in UserGenerators(Kred)]; //UserGenerators(Kred);
       
       vprint evenSX, 2: "start CT in glue for O+",k;
       CT  := CompositionTree(Kc);
       CTO := CompositionTreeOrder(Kc);
     
       if not CTO eq #OmegaPlus(k,q) then goodSection := false; end if;
       nrgetSec := nrgetSec + 1;

     //check kernel of red
       if goodSection and red then
          goodSection := SXE_int_testKernel(K,Kred,Kc,toBlock);
       end if;

       if 8 in [m,d-m] and nrgetSec gt 3 then 
	//"STOP SXEGLUEOP because of OmegaPlus8... try again";
          return false,false,false;
       end if;

     //"NOW RESET GROUP"; 
     //HD: have to do it so that SLPGroup is correct in black context
      pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
      Kc`UserWords := [Kred`UserWords[i] : i in pos];
      
    until goodSection;

  //reduce to section; shouldn't have to worry about orig copy since we have to evaluate anyway
  //make sure to also reduce the elements in sl1 and sl2 to sections
    SXEInitGroup(Kc : type:=Kred`type, natParams:=Kred`natParams);
    if red then
        sl1 := [Generic(Kc)| toBlock(i) : i in sl1];
        sl2 := [Generic(Kc)| toBlock(i) : i in sl2];
    end if;

   sl4 := false;
   if SXEIsNatRep(Kc) then 
      slk := Kc;
      sl1ims := sl1;
      sl2ims := sl2;
    else
       _,m2,m3,m4  := CompositionTreeSeries(Kc);
       vprint evenSX, 3: "done, now apply maps";
       nr     := [i : i in [1..#m4] | Type(Domain(m4[i])) eq GrpMat and
                                           Degree(Domain(m4[i])) eq k];
     
       if #nr eq 0 then
          nr     := [i : i in [1..#m4] | Type(Domain(m4[i])) eq GrpMat and
                                            Degree(Domain(m4[i])) eq 4];
          if #nr eq 0 then error "couldn't find OmegaPlus6 or SL4"; end if;
          sl4 := true;
       end if;
       nr     := nr[1];
       slk    := Codomain(m2[nr]);
       m2     := Function(m2[nr]);
       m3     := Function(m3[nr]);
       m4     := Function(m4[nr]);
       sl1ims := [Generic(slk)|m2(j) : j in sl1];
       sl2ims := [Generic(slk)|m2(j) : j in sl2];
     //translate to OmegaPlus6 if CT did wrong
       if sl4 then 
          slk         := ExteriorSquare(slk);
          f, sl4iso, sl4inv := RecogniseSLAlternatingSquare(slk);
          sl1ims := [sl4inv(i) : i in sl1ims];
          sl2ims := [sl4inv(i) : i in sl2ims];
       end if;
    end if;

    cntg := 0;
    if k eq 8 and not (Dimension(&meet([Eigenspace(i,1):i in sl1ims])) eq 4 and 
                    Dimension(&meet([Eigenspace(i,1):i in sl2ims])) eq 4) then
     
       vprint evenSX, 4: "GlueO+8: eigenspaces wrong, need to apply triality";

       elK,wrK := Internal_ClassicalSolveEven(slk,"Omega+",8,q);
       slp:=SXEOp8GraphAutSLPs(q);

       myaut := function(slk,elK,q,el)
          f,w := ClassicalRewrite(slk,elK,"Omega+",8,q,el);
          w := Evaluate(w,slp);
          w := Evaluate(w,elK);
          return w;
       end function;
       
       cntg := 0;
       repeat
          sl1ims := [Generic(slk)|myaut(slk,elK,q,i) : i in sl1ims];
          sl2ims := [Generic(slk)|myaut(slk,elK,q,i): i in sl2ims];    
          cntg    := cntg + 1; 
          if cntg eq 5 then error "sth wrong here..."; end if;
      until  Dimension(&meet([Eigenspace(i,1):i in sl1ims])) eq 4 and 
                    Dimension(&meet([Eigenspace(i,1):i in sl2ims])) eq 4;

      vprint evenSX, 4: "GlueO+8: done!";
   end if;


    //line up bases in nat Omega8
    if (d-m) mod 4 eq 0 then

       cob := [];
       for slim in [sl1ims,sl2ims] do
          ev1 := [u[1] : u in Eigenvalues(slim[3]) | not u[1] eq 1];
          tmp := Eigenspace(slim[2],1) meet Eigenspace(slim[1],1);
          flg := exists(omin){omin : omin in ev1 | Dimension(tmp meet Eigenspace(slim[3],omin)) eq 1};
          if not flg then return false,false,false; end if;
          V2  := tmp meet Eigenspace(slim[3],omin);
          if not Dimension(V2) eq 1 then return false,false,false; end if;
          v2  := Basis(V2)[1];
          v3  := v2*slim[6];
          v1  := v3*slim[5];
          v4  := v1*slim[6];
          Append(~cob, Eltseq(&cat([Eltseq(j) : j in [v1,v2,v3,v4]])));
       end for;
       cob := GL(8,q)!&cat(cob);
       newgr  := sub<Generic(slk)|[cob*i*cob^-1: i in UserGenerators(slk)]>;
       f,form := QuadraticForm(newgr);

       if m eq 4 then
         //usually cannot use small std gens of Omega+(4) embedded in Omega+(d) because
         //the semisimple elts might be not conjugate (different primitive elt)!
         //fix this here!!!
           std1   := [cob*i*cob^-1: i in sl1ims];
           i := SXEadjustElts(GF(q),std1[3][1][1],std1[4][1][1]);
           if not i eq 1 then
              eltA[6] := eltA[6]^i;
              wA[6]   := wA[6]^i;
           end if;
        end if;
        s := form[5][6];
        x := Root(s,q-3);
        y := x^-1;
        want    := Generic(slk)![1,0,0,0, 0,0,0,0,
                                0,1,0,0, 0,0,0,0,
                                0,0,0,0, x,0,0,0,
                                0,0,0,0, 0,x,0,0,
                                0,0,y,0, 0,0,0,0,
                                0,0,0,y, 0,0,0,0,
                                0,0,0,0, 0,0,1,0,
                                0,0,0,0, 0,0,0,1];
 //now case (d-m) mod 4 eq 2
    elif (d-m) mod 4 eq 2 then 

       cob := [];
       ev1 := [u[1] : u in Eigenvalues(sl1ims[3]) | not u[1] eq 1];
       tmp := Eigenspace(sl1ims[2],1) meet Eigenspace(sl1ims[1],1);
       flg := exists(omin){omin : omin in ev1 | Dimension(tmp meet Eigenspace(sl1ims[3],omin)) eq 1};
       V2  := tmp meet Eigenspace(sl1ims[3],omin);
       v2  := Basis(V2)[1];
       v3  := v2*sl1ims[6];
       v1  := v3*sl1ims[5];
       v4  := v1*sl1ims[6];
       Append(~cob, Eltseq(&cat([Eltseq(j) : j in [v1,v2,v3,v4]])));
       om  := [u[1] : u in Eigenvalues(sl2ims[1]) | not u[1] eq 1];
       v5  := Basis(Eigenspace(sl2ims[1],om[1]))[1];       
       v6  := Basis(Eigenspace(sl2ims[1],om[2]))[1];

      //the elts look the same wrt e1f1e2f2e3f3 AND e1f1e2f2f3e3! 
      //so what order to choose? have to try both...
      //atm just test one case which always seems to work :)
      //"there are two possibilites for glueing in OmegaPlus6, here just test one";

       Append(~cob, Eltseq(&cat([Eltseq(j) : j in [v5,v6]])));

       cob := GL(6,q)!&cat(cob);
       newgr  := sub<Generic(slk)|[cob*i*cob^-1: i in UserGenerators(slk)]>;
       f,form := QuadraticForm(newgr);

       if m eq 4 then
         //usually cannot use small std gens of Omega+(4) embedded in Omega+(d) because
         //the semisimple elts might be not conjugate (different primitive elt)!
         //fix this here!!!
           std1   := [cob*i*cob^-1: i in sl1ims];
           i := SXEadjustElts(GF(q),std1[3][1][1],std1[4][1][1]);

           if not i eq 1 then
              eltA[6] := eltA[6]^i;
              wA[6]   := wA[6]^i;
           end if;
        end if;
        s := form[5][6];
        x := Root(s,q-3);

        y := x^-1;
        want    := Generic(slk)![1,0,0,0, 0,0,
                                 0,1,0,0, 0,0,
                                 0,0,0,0, x,0,
                                 0,0,0,0, 0,x,
                                 0,0,y,0, 0,0,
                                 0,0,0,y, 0,0];

        
    end if;

    want   := cob^-1*want*cob;
    want   := Generic(slk)!want;

    if k eq 8 and cntg gt 0 then
       for i in [1..2*cntg] do want := myaut(slk,elK,q,want); end for;
    end if;

  //translate back to SL4
    if sl4 then want := sl4iso(want); end if;

   if SXEIsNatRep(Kc)  then 
     f,wantw := LMGIsIn(Kc,want);
     pos     := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
     nslp    := [K`SLPGroup.i : i in pos]; 
     wantw   := Evaluate(wantw,nslp);
     wantw   := Evaluate(wantw,K`UserWords);
     want    := Evaluate(wantw,UserGenerators(G));      
   else
       Knice  := CompositionTreeNiceGroup(Kc);
       rew,wr := CompositionTreeNiceToUser(Kc);
       wantw  := m4(want); 
       wantw  := Evaluate(wantw,wr);
       pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
       nslp   := [K`SLPGroup.i : i in pos]; 
       wantw  := Evaluate(wantw,nslp);
       wantw  := Evaluate(wantw,K`UserWords);
       want   := Evaluate(wantw,UserGenerators(G));
   end if;

  //now glue and put gens together
    eltA[10] := eltA[10]*eltB[10];
    wA[10]   := wA[10]*wB[10];
    eltA[11] := eltA[11]*eltB[11];
    wA[11]   := wA[11]*wB[11];

    eltA[8] := eltB[8]*want*eltA[8];
    wA[8]   := wB[8]*wantw*wA[8];
 
    vprint evenSXcpu,1: "runtime SXEGlueOp in deg",d," is",Cputime(rnt);
    vprint evenSX, 2: "end SXEGlueOp in degree",d;
    return eltA, wA;

end function; 




/****************************************************************************/
/* glue cycles to obtain standard generators (black)
/****************************************************************************/
SXEGlueSp := function(G,eltA,wA,eltB,wB,m)
    nP  := G`natParams; d := nP[2]; q := nP[3]; p := nP[4];
    F   := GF(q^2);
    rnt := Cputime();
 
    vprint evenSX, 2: "start SXEGlueSp in degree",d;

  //find Involution
    c1     := eltA[8]^2;
    c1w    := wA[8]^2;
    i      := ((m-4) div 4) -1;
    i1     := eltA[2];
    w1     := wA[2];
    for j in [1..i] do
        i1   := i1*eltA[2]^(c1^(j));
        w1   := w1*wA[2]^(c1w^(j));
    end for;

    c2     := eltB[2];
    c2w    := wB[2];
    i      := ((d-m-2) div 2) -1;
    i2     := eltB[3]^(c2);
    w2     := wB[3]^(c2w);
    for j in [1..i] do
        i2   := i2*eltB[3]^(c2^(j+1));
        w2   := w2*wB[3]^(c2w^(j+1));
    end for;

    inv  := i2;
    winv := w2;
    if m gt 4 then inv := i1*inv;  winv := w1*winv; end if;
 
 //find gens for first Omega4s
    sl1    := [Generic(G) | eltA[i]^(eltA[8]^-2) : i in [5,2,6,3,4,1,4]];
    sl1w   := [wA[i]^(wA[8]^-2) : i in [5,2,6,3,4,1,4]];
  //find gens for second subgroup (Omega4 if (d-m) divisible by 4
    sl2    := [Generic(G) | eltB[i] : i in [1,3,4]];
    sl2w   := [wB[i] : i in [1,3,4]];

  
  //find fpf element
    if m gt 4 then
        fp1  := &*[eltA[6]^(eltA[8]^(2*j)) : j in [0..((m-4) div 4)-1]];
        wfp1 := &*[wA[6]^(wA[8]^(2*j)) : j in [0..((m-4) div 4)-1]];
    else
        fp1  := eltA[6]; wfp1 := wA[6];
    end if;
    fp2  := &*[eltB[4]^(eltB[2]^(j)) : j in [1..((d-m-2) div 2)]];
    wfp2 := &*[wB[4]^(wB[2]^(j)) : j in [1..((d-m-2) div 2)]];
    fp  := fp2;
    wfp := wfp2;
    if m gt 4 then fp:=fp1*fp2; wfp := wfp1*wfp; end if;

  //now extract OmegaPlus8 / OmegaPlus6
    C, Cw := SXECentraliserOfInvolution(G, inv, winv);
    k     := 6;

  //"got these sections",[*SXELieType(i:char:=2) : i in Sections(C)*];
    
    nrgetSec := 1;  
    goodSection := true;
    repeat
       goodSection := true;
       if nrgetSec gt 1 then 
           vprint evenSX, 3: "----- have to extract section another time, nr",nrgetSec; 
       end if;
       K := SXEgetSection(C,fp,wfp,G,d,p,k,"Sp");  //XXX

     //to catch Sp4 aut prob
       if K cmpeq false then 
          return false, false; 
       end if;

       K`natParams := <"Sp",k,q,2>;
       K`type      := "Sp";

       Kred, red, toBlock := SXEReduceToSection(K); 
       Kred`UserWords := K`UserWords;    
       Kc := SXECopyGroup(Kred);
       Kc`UserWords := Kred`UserWords;
       ug := [Generic(Kred)!u : u in UserGenerators(Kred)]; //UserGenerators(Kred);
     //if Degree(Kc) lt Degree(K) then "reduced from",Degree(K),"to",Degree(Kc); end if;
   
       vprint evenSX, 2: "start CT in glue for Sp",k;

       CT  := CompositionTree(Kc);
       CTO := CompositionTreeOrder(Kc);
    
       if not CTO eq #Sp(k,q) then goodSection := false; end if;
     
       if goodSection and red then
          goodSection := SXE_int_testKernel(K,Kred,Kc,toBlock);
       end if;

       if m eq 8 and nrgetSec gt 3 then
        //"STOP SXEGLUEOP because of OmegaPlus8... try again";
          return false,false,false;
       end if;


    //"NOW RESET GROUP"; 
     //HD: have to do it so that SLPGroup is correct in black context
      pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
      Kc`UserWords := [Kred`UserWords[i] : i in pos];

       nrgetSec := nrgetSec + 1;
    until goodSection;

    vprint evenSX, 2: "... done, now continue";;

   //reduce to section; shouldn't have to worry about orig copy since we have to evaluate anyway
   //make sure to also reduce the elements in sl1 and sl2 to sections
    SXEInitGroup(Kc : type:=Kred`type, natParams:=Kred`natParams);
    if red then
        sl1 := [Generic(Kc)| toBlock(i) : i in sl1];
        sl2 := [Generic(Kc)| toBlock(i) : i in sl2];
    end if;
    if SXEIsNatRep(Kc)  then 
      
      slk := Kc;
      sl1ims := sl1;
      sl2ims := sl2;
    else

       _,m2,m3,m4  := CompositionTreeSeries(Kc);
       vprint evenSX, 3: "done, now apply maps";
       nr     := [i : i in [1..#m4] | Type(Domain(m4[i])) eq GrpMat and
                                           Degree(Domain(m4[i])) eq k];
       if not #nr eq 1 then error "good section ... this shouldn't have happenend!"; end if;

       nr     := nr[1];
       slk    := Codomain(m2[nr]);
       m2     := Function(m2[nr]);
       m3     := Function(m3[nr]); 
       m4     := Function(m4[nr]);
       sl1ims := [Generic(slk)|m2(j) : j in sl1];
       sl2ims := [Generic(slk)|m2(j) : j in sl2];

    end if;


  //this here works also for q=2 
    cob := [];
    V2 := Eigenspace(sl1ims[2],1) meet Eigenspace(sl1ims[1],1) meet Eigenspace(sl2ims[1]*sl2ims[2],1);
    if not Dimension(V2) eq 1 then return false,false,false; end if;
    V2 := Basis(V2)[1];
    V3 := V2*sl1ims[6];
    V4 := V2*sl1ims[5];
    V1 := V3*sl1ims[5];
    MM  := MatrixAlgebra(GF(q),k);
    tmp := MM!sl2ims[2];
    V6 := Basis(Image(tmp-tmp^0))[1];
    V5 := V6*sl2ims[1];
    
    Append(~cob, Eltseq(&cat([Eltseq(j) : j in [*V1,V2,V3,V4,V5,V6*]])));

    cob := GL(6,q)!&cat(cob);
    newgr  := sub<Generic(slk)|[cob*i*cob^-1: i in UserGenerators(slk)]>;
    f,form := SymplecticForm(newgr);
 
  //this has no impact later?! eltA[3] is not used!
    if m eq 4 then
      //usually cannot use small std gens of Omega+(4) embedded in Omega+(d) because
      //the semisimple elts might be not conjugate (different primitive elt)!
      //fix this here!!! O^+(4,q) = SL(2,q)\times SL(2,q), each has its own field automorphis!
        std1   := [cob*i*cob^-1: i in sl1ims];
        i := SXEadjustElts(GF(q),std1[3][1][1],std1[4][1][1]);
        if not i eq 1 then
           eltA[6] := eltA[6]^i;
           wA[6]   := wA[6]^i;
        end if;
     end if;

     s := form[5][6];
     x := Root(s,q-3);

     y := x^-1;
     want    := Generic(slk)![1,0,0,0, 0,0,
                              0,1,0,0, 0,0,
                              0,0,0,0, x,0,
                              0,0,0,0, 0,x,
                              0,0,y,0, 0,0,
                              0,0,0,y, 0,0];


    want   := cob^-1*want*cob;
    want   := Generic(slk)!want;

   vprint evenSX, 2: "   apply maps to find glue";
    
   if SXEIsNatRep(Kc) then 
      f,wantw := LMGIsIn(Kc,want);
      pos     := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
      nslp    := [K`SLPGroup.i : i in pos]; 
      wantw   := Evaluate(wantw,nslp);
      wantw   := Evaluate(wantw,K`UserWords);
      ttt := Cputime();
      want    := Evaluate(wantw,UserGenerators(G));      
   else
      Knice  := CompositionTreeNiceGroup(Kc);
      rew,wr := CompositionTreeNiceToUser(Kc);
      wantw  := m4(want);
      wantw  := Evaluate(wantw,wr);
      pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
      nslp   := [K`SLPGroup.i : i in pos]; 
      wantw  := Evaluate(wantw,nslp);
      wantw  := Evaluate(wantw,K`UserWords);
      want   := Evaluate(wantw,UserGenerators(G));
   end if;

  //now glue and put gens together
    eltB[10] := eltA[10]*eltB[10];
    wB[10]   := wA[10]*wB[10];
    eltB[11] := eltA[11]*eltB[11];
    wB[11]   := wA[11]*wB[11];
    eltB[2] := eltB[2]*want*eltA[8];
    wB[2]   := wB[2]*wantw*wA[8];

    cc := eltB[2]^(-(m div 2)); wcc := wB[2]^(- (m div 2));
    for i in [1,3,4,5] do eltB[i] := eltB[i]^cc; wB[i] := wB[i]^wcc; end for;

    vprint evenSXcpu,1: "runtime SXEGlueSp in deg",d," is",Cputime(rnt);
    vprint evenSX, 2: "end SXEGlueSp in degree",d;
    return eltB, wB;

end function;



/****************************************************************************/
/* glue cycles to obtain standard generators (black)
/****************************************************************************/
SXEGlueOm := function(G,eltA,wA,eltB,wB,m)
    nP  := G`natParams; d := nP[2]; q := nP[3]; p := nP[4];
    rnt := Cputime();

    vprint evenSX, 2: "start SXEGlueOm in degree",d;

  //find Involution
    c1     := eltA[8]^2;
    c1w    := wA[8]^2;
    i      := ((m-4) div 4) -1;
    i1     := eltA[2];
    w1     := wA[2];
    for j in [1..i] do
        i1   := i1*eltA[2]^(c1^(j));
        w1   := w1*wA[2]^(c1w^(j));
    end for;
    
    inv  := i1;
    winv := w1;

 //find gens for first Omega4s
    sl1    := [Generic(G) | eltA[i]^(eltA[8]^-2) : i in [5,2,6,3,4,1,4]];
    sl1w   := [wA[i]^(wA[8]^-2) : i in [5,2,6,3,4,1,4]];

  //find gens for second subgroup (OmegaMinus(4) if m=d-4, OmegaMinus(6) otherwise
    sl2    := eltB;
    sl2w   := wB;

  //find fpf element
    if m gt 4 then
        fp1  := &*[eltA[6]^(eltA[8]^(2*j)) : j in [0..((m-4) div 4)-1]];
        wfp1 := &*[wA[6]^(wA[8]^(2*j)) : j in [0..((m-4) div 4)-1]];
    else
        fp1  := eltA[6]; wfp1 := wA[6];
    end if;

    fp  := fp1;
    wfp := wfp1;

  //now extract OmegaPlus8 / OmegaPlus6
    C, Cw := SXECentraliserOfInvolution(G, inv, winv);
    if (d-m) eq 4 then k := 8; else k := 10; end if;
   
    nrgetSec := 1;  
    goodSection := true;
    repeat
       goodSection := true;
       if nrgetSec gt 1 then 
           vprint evenSX, 3: "----- have to extract section another time, nr",nrgetSec; 
       end if;
       K := SXEgetSection(C,fp,wfp,G,d,p,k,"O-"); 
 
      if K cmpeq false and not m eq 8 then 
          error "error in SXEgetSection"; 
       elif K cmpeq false and m eq 8 then
          return false,false,false;
       end if;
      

       K`natParams := <"O-",k,q,2>;
       K`type      := "O-";

       Kred, red, toBlock := SXEReduceToSection(K); 
       Kred`UserWords := K`UserWords;    
       Kc := SXECopyGroup(Kred);
       Kc`UserWords := Kred`UserWords;
       ug := [Generic(Kred)!u : u in UserGenerators(Kred)]; //UserGenerators(Kred);
       vprint evenSX, 2: "start CT in glue for SU",k;
       CT  := CompositionTree(Kc);
       CTO := CompositionTreeOrder(Kc);


       if not CTO eq #OmegaMinus(k,q) then goodSection := false; end if;
    
     //check kernel of red
       if goodSection and red then
          goodSection := SXE_int_testKernel(K,Kred,Kc,toBlock);
       end if;
 
       if m eq 8 and nrgetSec gt 3 then
        //"STOP SXEGLUEOP because of OmegaPlus8... try again";
          return false,false,false;
       end if;

    
     //"NOW RESET GROUP"; 
     //HD: have to do it so that SLPGroup is correct in black context
      pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
      Kc`UserWords := [Kred`UserWords[i] : i in pos];
      nrgetSec := nrgetSec + 1;
       
    until goodSection;

 //reduce to section; shouldn't have to worry about orig copy since we have to evaluate anyway
  //make sure to also reduce the elements in sl1 and sl2 to sections
    SXEInitGroup(Kc : type:=Kred`type, natParams:=Kred`natParams);
    if red then
        sl1 := [Generic(Kc)| toBlock(i) : i in sl1];
        sl2 := [Generic(Kc)| toBlock(i) : i in sl2];
    end if;

    if SXEIsNatRep(Kc)   then
     
      slk := Kc;
      sl1ims := sl1;
      sl2ims := sl2;
    else

       _,m2,m3,m4  := CompositionTreeSeries(Kc);
       vprint evenSX, 3: "done, now apply maps";
       nr     := [i : i in [1..#m4] | Type(Domain(m4[i])) eq GrpMat and
                                           Degree(Domain(m4[i])) eq k];
       if not #nr eq 1 then error "good section ... this shouldn't have happenend!"; end if;

       nr     := nr[1];
       slk    := Codomain(m2[nr]);
       m2     := Function(m2[nr]);
       m3     := Function(m3[nr]); 
       m4     := Function(m4[nr]);
       sl1ims := [Generic(slk)|m2(j) : j in sl1];
       sl2ims := [Generic(slk)|m2(j) : j in sl2];

    end if;

    if (d-m) eq 4 then
       //line up bases in nat Omega8
       cob := [];
       ev1 := [u[1] : u in Eigenvalues(sl1ims[3]) | not u[1] eq 1];
       tmp := Eigenspace(sl1ims[2],1) meet Eigenspace(sl1ims[1],1);
       flg := exists(omin){omin : omin in ev1 | Dimension(tmp meet Eigenspace(sl1ims[3],omin)) eq 1};
       if not flg then return false,false,false; end if;
      
       V2  := tmp meet Eigenspace(sl1ims[3],omin);
       if not Dimension(V2) eq 1 then return false, false, false; end if;
       v2  := Basis(V2)[1];
       v3  := v2*sl1ims[6];
       v1  := v3*sl1ims[5];
       v4  := v1*sl1ims[6];
       Append(~cob, Eltseq(&cat([Eltseq(j) : j in [v1,v2,v3,v4]])));
    
       ev1 := [u[1] : u in Eigenvalues(sl2ims[3]) | not u[1] eq 1];
       flg := exists(om){om : om in ev1 | Dimension(Eigenspace(sl2ims[2],1) meet Eigenspace(sl2ims[3],om)) eq 1};
       if not flg then return false,false,false; end if;
       V1  := Eigenspace(sl2ims[2],1) meet Eigenspace(sl2ims[3],om);
       if not Dimension(V1) eq 1 then return false, false, false; end if;
       v1  := Basis(V1)[1];
       v2  := v1*sl2ims[7];
       ominv := [i : i in ev1 | not i eq om][1];
       v3 := v1*sl2ims[1]-v1-v2;
       v4  := v3*sl2ims[3]-v3;
       q   := G`natParams[3];
       gam := GF(q^2).1;
       gam := (gam^-1+gam^(-q))^-1;
       v4  := gam*v4;
       Append(~cob, Eltseq(&cat([Eltseq(j) : j in [v1,v2,v3,v4]])));
       cob := &cat(cob);
       t:=MatrixAlgebra(GF(q),8)!cob;
       cob := GL(8,q)!cob;
       newgr  := sub<Generic(slk)|[cob*i*cob^-1: i in UserGenerators(slk)]>;
       f,form := QuadraticForm(newgr);

       if m eq 4 then
         //usually cannot use small std gens of Omega+(4) embedded in Omega+(d) because
         //the semisimple elts might be not conjugate (different primitive elt)!
         //fix this here!!!
           std1   := [cob*i*cob^-1: i in sl1ims];

           i := SXEadjustElts(GF(q),std1[3][1][1],std1[4][1][1]);
           if not i eq 1 then
              eltA[6] := eltA[6]^i;
              wA[6]   := wA[6]^i;
           end if;
        end if;
        s := form[5][6];
        x := Root(s,q-3);
        y := x^-1;
        want    := Generic(slk)![1,0,0,0, 0,0,0,0,
                                  0,1,0,0, 0,0,0,0,
                                  0,0,0,0, x,0,0,0,
                                  0,0,0,0, 0,x,0,0,
                                  0,0,y,0, 0,0,0,0,
                                  0,0,0,y, 0,0,0,0,
                                  0,0,0,0, 0,0,1,0,
                                  0,0,0,0, 0,0,0,1];
      
       
     elif (d-m) eq 6 then
       //line up bases in nat Omega10
     
       cob := [];
       ev1 := [u[1] : u in Eigenvalues(sl1ims[3]) | not u[1] eq 1];
       tmp := Eigenspace(sl1ims[2],1) meet Eigenspace(sl1ims[1],1);
       flg := exists(omin){omin : omin in ev1 | Dimension(tmp meet Eigenspace(sl1ims[3],omin)) eq 1};
       if not flg then error "GlueOm: cannot find correct eigenvalues"; end if;
       V2  := tmp meet Eigenspace(sl1ims[3],omin);
       v2  := Basis(V2)[1];
       v3  := v2*sl1ims[6];
       v1  := v3*sl1ims[5];
       v4  := v1*sl1ims[6];
       Append(~cob, Eltseq(&cat([Eltseq(j) : j in [v1,v2,v3,v4]])));

       ev1 := [u[1] : u in Eigenvalues(sl2ims[3]) | not u[1] eq 1];
       flg := exists(om){om : om in ev1 | Dimension(Eigenspace(sl2ims[2],1) meet Eigenspace(sl2ims[3],om)) eq 1};
       if not flg then error "GlueOm: cannot find correct eigenvalues"; end if;
       V1  := Eigenspace(sl2ims[2],1) meet Eigenspace(sl2ims[3],om);
       v1  := Basis(V1)[1];
       v2  := v1*sl2ims[7];
       ominv := [i : i in ev1 | not i eq om][1];
       v3 := v1*sl2ims[1]-v1-v2;
       v4  := v3*sl2ims[3]-v3;
       q   := G`natParams[3];
       gam := GF(q^2).1;
       gam := (gam^-1+gam^(-q))^-1;
       v4  := gam*v4;
       v11 := v1*sl2ims[5];
       v22 := v2*sl2ims[5];
       Append(~cob, Eltseq(&cat([Eltseq(j) : j in [v11,v22,v1,v2,v3,v4]])));
       cob := &cat(cob);
       t:=MatrixAlgebra(GF(q),10)!cob;
       cob := GL(10,q)!cob;
       newgr  := sub<Generic(slk)|[cob*i*cob^-1: i in UserGenerators(slk)]>;
       f,form := QuadraticForm(newgr);
       if m eq 4 then
         //usually cannot use small std gens of Omega+(4) embedded in Omega+(d) because
         //the semisimple elts might be not conjugate (different primitive elt)!
         //fix this here!!!
           std1   := [cob*i*cob^-1: i in sl1ims];
           i := SXEadjustElts(GF(q),std1[3][1][1],std1[4][1][1]);
           if not i eq 1 then
              eltA[6] := eltA[6]^i;
              wA[6]   := wA[6]^i;
           end if;
        end if;
        s := form[5][6];
        x := Root(s,q-3);
  
        y := x^-1;
         want    := Generic(slk)![1,0,0,0, 0,0,0,0, 0,0,
                                  0,1,0,0, 0,0,0,0, 0,0,
                                  0,0,0,0, x,0,0,0, 0,0,
                                  0,0,0,0, 0,x,0,0, 0,0,
                                  0,0,y,0, 0,0,0,0, 0,0,
                                  0,0,0,y, 0,0,0,0, 0,0,
                                  0,0,0,0, 0,0,1,0, 0,0,
                                  0,0,0,0, 0,0,0,1, 0,0,
                                  0,0,0,0, 0,0,0,0, 1,0,
                                  0,0,0,0, 0,0,0,0, 0,1];
    end if;


    want   := cob^-1*want*cob;
    want   := Generic(slk)!want; 

   if SXEIsNatRep(Kc)  then

      f,wantw := LMGIsIn(Kc,want);

      pos     := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
      nslp    := [K`SLPGroup.i : i in pos]; 
      wantw   := Evaluate(wantw,nslp);
      wantw   := Evaluate(wantw,K`UserWords);
      want    := Evaluate(wantw,UserGenerators(G));      

    else

       Knice  := CompositionTreeNiceGroup(Kc);
       rew,wr := CompositionTreeNiceToUser(Kc);
       wantw  := m4(want); 
       wantw  := Evaluate(wantw,wr);
       pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
       nslp   := [K`SLPGroup.i : i in pos]; 
       wantw  := Evaluate(wantw,nslp);
       wantw  := Evaluate(wantw,K`UserWords);

       want   := Evaluate(wantw,UserGenerators(G));

   end if;

  //now glue and put gens together
    eltB[5] := eltB[5]*want*eltA[8];
    wB[5]   := wB[5]*wantw*wA[8];

    eltB[4] := eltA[4];
    wB[4]   := wA[4];

    vprint evenSXcpu,1: "runtime SXEGlueOm in deg",d," is",Cputime(rnt);
    vprint evenSX, 2: "end SXEGlueOm in degree",d;
    return eltB, wB;

end function;







/****************************************************************************/
/* Base Case Std gens (black); usually input is already reduced-to-section
/****************************************************************************/
SXEBaseCaseBlack := function(H :lv:=1)

    rnt := Cputime();
    nP  := H`natParams;
    d   := nP[2];  q := nP[3];  p := nP[4];
    type := nP[1];


  //use ClassicalConstructiveRecognition for certain base cases
    if (type eq "SL" and d in [2,3,4,5]) or
       (type eq "SU" and d in [2,3,4,5,7]) or
       (type eq "O+" and d in [4,6,8]) or
       (type eq "O-" and d in [4,6,8,10]) or
       (type eq "Sp" and d in [2,4,6]) then

       vprint evenSX, 2:"SXEBaseCaseBlack: call MyCR for BASE CASE",H`natParams;
       vprint ClassicalRecognition, 2:"SXEBaseCaseBlack: call MyCCR for BASE CASE",H`natParams;
        
       ttype := type;
       if type eq "O+" then ttype:="Omega+"; end if;
       if type eq "O-" then ttype:="Omega-"; end if;

       Hc  := SXECopyGroup(H);
       gHc := [Generic(Hc)!Hc.i : i in [1..Ngens(Hc)]];
       ugH := [Generic(H)!u : u in UserGenerators(H)];

       
       flag := false; 
       fcnt := 1;    
       while not flag and fcnt lt 4 do
          flag,_,_,_,_,elts,wrds := ClassicalConstructiveRecognition(Hc,ttype,d,q);             
          fcnt := fcnt + 1;    
       end while;  

       if not flag then error "ClassicalConstructiveRecognition failed for ",Hc`natParams; end if;

       pos    := [Position(ugH,g) : g in  gHc];
       nslp   := [H`SLPGroup.i : i in pos];
       wrds   := Evaluate(wrds,nslp);
     
       while #elts lt 9 do Append(~elts,elts[1]^0); Append(~wrds,wrds[1]^0); end while;

     //add additional elements (inv and fpf) for recursion
     //for SU5 and SU7 this would not be necessary though since this group is in corner
       if type eq "SL" then
          k  := elts[2]; wk  := wrds[2];
          if type eq "SL" then k := k^-2; wk := wk^-2; end if;
          kk := k;          wkk := wk;
          inv := elts[3]; winv := wrds[3];
          fpf := elts[4]; wfpf := wrds[4];  
          for i in [2..(d div 2)] do
             inv := inv*elts[3]^kk; winv := winv*wrds[3]^wkk;
             fpf := fpf*elts[4]^kk; wfpf := wfpf*wrds[4]^wkk;
             kk   := kk*k; wkk := wkk*wk;
          end for;
       elif type in ["SU","Sp"] then
          k  := elts[2]; wk  := wrds[2];
          if type eq "SL" then k := k^-2; wk := wk^-2; end if;
          kk := k;          wkk := wk;
          inv := elts[3]; winv := wrds[3];
          fpf := elts[4]; wfpf := wrds[4];  
          for i in [2..(d div 2)] do
             inv := inv*elts[3]^kk; winv := winv*wrds[3]^wkk;
             fpf := fpf*elts[4]^kk; wfpf := wfpf*wrds[4]^wkk;
             kk   := kk*k; wkk := wkk*wk;
          end for;

       elif type eq "O+" then
          k  := elts[8]^2; wk  := wrds[8]^2;
          kk := k;          wkk := wk;
          inv := elts[2]; winv := wrds[2];
          fpf := elts[6]; wfpf := wrds[6];  
          for i in [2..(d div 4)] do
             inv := inv*elts[2]^kk; winv := winv*wrds[2]^wkk;
             fpf := fpf*elts[6]^kk; wfpf := wfpf*wrds[6]^wkk;
             kk   := kk*k; wkk := wkk*wk;
          end for;
       elif type eq "O-" then
           elts[6] := elts[3]^(q+1); wrds[6] := wrds[3]^(q+1); //fpf for glue
           elts[7] := elts[1]*(elts[1]*elts[2])^2; wrds[7] := wrds[1]*(wrds[1]*wrds[2])^2;
       end if;
       if not type eq "O-" then
          Append(~elts,inv);  Append(~elts,fpf);
          Append(~wrds,winv); Append(~wrds,wfpf);
       end if;
 
     //add two gens for glue in SL5
       if type eq "SL" and d eq 4 then
          Append(~elts,elts[2]^-1); Append(~elts,elts[2]^2);
          Append(~wrds,wrds[2]^-1); Append(~wrds,wrds[2]^2);
       end if;
      vprint evenSX, 2: "SXEBaseCaseBlack: completed call to MyCR for BASE CASE",H`natParams;
      return elts,wrds,elts[1]^0;
   end if;


end function;


/***************************************************************************/
/* extracts middle SU2 from involution centraliser C in SU6
/***************************************************************************/
 SXEgetSU2 := function(C,fpf,wfpf,G : cb := false)

   np := G`natParams;
   q  := np[3];
   p  := np[4];
   ofp := Order(fpf);
   rnt := Cputime();

  //make formula elt; input is random word + wrd in C
   makeElt := function(gg,ww) 
      w := Evaluate(ww,C`UserWords);
      g := ((fpf*(gg)*(fpf*fpf^(gg))^((ofp-1) div 2)) )^2;
      w := ((wfpf*(w)*(wfpf*wfpf^(w))^((ofp-1) div 2)))^2;
      return g,w;
   end function;


  //try it 50 times if bruteforce
   for nrbf in [1..50] do
      nextbf  := false;
      flgfail := 1;
      done    := false; 
      vprint evenSX, 3: "SXEgetSection: start bruteforce extraction nr",nrbf; 
     
      repeat repeat g,w := SXERandomWord(C); until not g eq g^0;
         fac := [i : i in Factorisation(Order(g)) | not i[1] eq p and not (q+1) mod i[1] eq 0]; 
      until #fac ge 1;
      r   := Random(fac)[1];                                     
      ord := Order(g) div r;                                    
      gg   := g^ord;
      ww   := w^ord; 

      gens := [Generic(C)|];
      wrds := [];
      for i in [1..20] do
         h, wh := SXERandomWord(C);
         g, w := makeElt(gg^h,ww^wh);
         Append(~gens,g);
         Append(~wrds,w);
      end for;

      K := sub<Generic(C) | gens>;
      K`UserGenerators := gens;
      K`UserWords      := wrds;
      SXEInitGroup(K:UserWords:=wrds, type := "no");
      t := SXELieType(K:char:=2,q:=q); 
      if t cmpeq <"SL",2,q,p> then 
          done :=true; 
      end if;
      if not t cmpeq false then 
         if Type(K) eq GrpMat then 
            done := LMGOrder(K) eq #SL(2,q); 
        else
           done := #K eq #SL(2,q);
        end if;
     end if;
 
     if done then
          vprint evenSXcpu,1: "runtime SXEgetSU2 is",Cputime(rnt);
          vprint evenSX, 2: "end SXEgetSU2";
          K`natParams := t;
          K`type := t[1];
          return K;
       end if;
   end for;
   error "SXEgetSU2: cannot extract section...";  
end function;




/***************************************************************************/    
/* instead of rec to main function, use ClassicalCR; have to add additional elts:
/* first elts are ClassicalStandardGens, inv and fpf is elt 10 and 11                                                         
/***************************************************************************/
MyCCRwithElts := function(A,m,q)                                                                                 
   Hc  := SXECopyGroup(A);                                                                                    
   gHc := [Generic(Hc)!Hc.i : i in [1..Ngens(Hc)]];                                                                     
   ugH := [Generic(A)!u : u in UserGenerators(A)];                                                
   ttype := A`type;                                                                            
   if A`type eq "O+" then ttype := "Omega+"; end if;                                
   if A`type eq "O-" then ttype := "Omega-"; end if;                                              
                                                           
   vprint evenSX, 2: "evenSXblack: start mccr instead of recursion to main alg with",A`natParams;        
   f,_,_,_,_,elts,wrds := ClassicalConstructiveRecognition(Hc,ttype,m,q);                         

 //assert elts eq Evaluate(wrds,[Hc.i : i in [1..Ngens(Hc)]]);
 //if ttype eq "Omega+" and m eq 6 then
 //   _,rels := ClassicalStandardPresentation("Omega+",6,4);
 //    #{Evaluate(r,wrds) : r in rels} eq 1;
 //end if;
 //"all good";

   vprint evenSX, 2: "... done rec call";
                                                                                        
   pos    := [Position(ugH,g) : g in  gHc];                                                  
   nslp   := [A`SLPGroup.i : i in pos];                                                       
   wrds   := Evaluate(wrds,nslp);
                                                                                           
   while #elts lt 9 do Append(~elts,elts[1]^0); Append(~wrds,wrds[1]^0); end while;                                    
  //add additional elements (inv and fpf) for recursion                                              
   if A`type in ["SL","SU","Sp"] then                                                                          
      k  := elts[2]; wk  := wrds[2];                                                                  
      if A`type eq "SL" then k := k^-2; wk := wk^-2; end if;                                   
      kk := k;          wkk := wk;                                                              
      inv := elts[3]; winv := wrds[3];                                          
      fpf := elts[4]; wfpf := wrds[4];                                                         
      for i in [2..(m div 2)] do                                                                
         inv := inv*elts[3]^kk; winv := winv*wrds[3]^wkk;                                             
         fpf := fpf*elts[4]^kk; wfpf := wfpf*wrds[4]^wkk;                              
         kk   := kk*k; wkk := wkk*wk;                                                           
      end for;                                                                                  
   elif A`type eq "O+" then                                                      
      k  := elts[8]^2; wk  := wrds[8]^2;                 
      kk := k;          wkk := wk;                
      inv := elts[2]; winv := wrds[2];               
      fpf := elts[6]; wfpf := wrds[6];    
      for i in [2..(m div 4)] do         
         inv := inv*elts[2]^kk; winv := winv*wrds[2]^wkk;       
         fpf := fpf*elts[6]^kk; wfpf := wfpf*wrds[6]^wkk; 
         kk   := kk*k; wkk := wkk*wk;     
      end for;    
   elif A`type eq "O-" then              
       elts[6] := elts[3]^(q+1); wrds[6] := wrds[3]^(q+1); //fpf for glue  
       elts[7] := elts[1]*(elts[1]*elts[2])^2; wrds[7] := wrds[1]*(wrds[1]*wrds[2])^2; 
   end if;                  
   if not A`type eq "O-" then 
      Append(~elts,inv);  Append(~elts,fpf);  
      Append(~wrds,winv); Append(~wrds,wfpf);   
   end if;                  
  //add two gens for glue in SL5         
    if A`type eq "SL" and m eq 4 then 
       Append(~elts,elts[2]^-1); Append(~elts,elts[2]^2);
       Append(~wrds,wrds[2]^-1); Append(~wrds,wrds[2]^2);
    end if;                 
    return elts,wrds;
end function;




SXEaddOp8prelimElts := function(elts,wrds)
   while #elts lt 9 do Append(~elts,elts[1]^0); Append(~wrds,wrds[1]^0); end while;
   k  := elts[8]^2; wk  := wrds[8]^2;                 
   kk := k;          wkk := wk;                
   inv := elts[2]; winv := wrds[2];               
   fpf := elts[6]; wfpf := wrds[6];    
   for i in [2..(8 div 4)] do         
      inv := inv*elts[2]^kk; winv := winv*wrds[2]^wkk;       
      fpf := fpf*elts[6]^kk; wfpf := wfpf*wrds[6]^wkk; 
      kk   := kk*k; wkk := wkk*wk;     
   end for;    
   Append(~elts,inv);  Append(~elts,fpf);  
   Append(~wrds,winv); Append(~wrds,wfpf);   
   return elts,wrds;
end function;


SXEaddSp4prelimElts := function(elts,wrds)
   while #elts lt 11 do Append(~elts,elts[1]^0); Append(~wrds,wrds[1]^0); end while;
   return elts,wrds;
end function;


/***************************************************************************/        
/* constructs std gens as words in UserGens; plus good involution and fpf elt
/* first elts are ClassicalStandardGens, inv and fpf is elt 10 and 11
/***************************************************************************/   
SXEStandardGeneratorsEven := function(G : lv:=1, onlyBlack:=SXEonlyBlack, silent:=true)
 
   if onlyBlack then "ONLY BLACK IS ON!!!!!!!!!"; end if;

   np   := G`natParams;
   type := np[1];
   d    := np[2];
   q    := np[3];
   p    := np[4];

   vprint evenSX, 2: "black call SXEStandardGensEven",type,d;       

   str := "--- Recursion Level " cat IntegerToString(lv) cat " ---";
   vprint evenSX, 1: str,"START SXEStandardGenerators for ",np;
 
   vprint ClassicalRecognition,2: "SXEStandardGenerators for",type,q,d;

   rnt  := Cputime();
   cob  := -1;

   //XXXXX

   Gorg     := SXECopyGroup(G);
   G, red   := SXEReduceToSection(G);

   if red then 
      vprint evenSX, 2: "  reduced from",Degree(Gorg),"to",Degree(G); 
      vprint ClassicalRecognition,2: "SXEStandardGenerators: reduced from ",Degree(Gorg),"to",Degree(G); 
   end if;

   if q eq 2 and not SXEIsNatRep(G) then error "code does not work for q=2 and non-natural rep"; end if;

   G`UserWords := Gorg`UserWords;
   SXEInitGroup(G : type:=type, natParams:=np);
   natrep := SXEIsNatRep(G);

   if natrep and not onlyBlack then
 
      vprint evenSX, 2: "    SXEStandardGenerators: CALL MyCCR for",G`natParams;
      if type eq "SL" then cs := "SL";
      elif type eq "SU" then cs := "SU";
      elif type eq "Sp" then cs := "Sp";
      elif type eq "O+" then cs := "Omega+";
      elif type eq "O-" then cs := "Omega-";
      end if;

    //copy group for saving user generators!
      Gct   := sub<Generic(G) | UserGenerators(G)>;
      ugct  := [Generic(G)!u : u in UserGenerators(G)]; //UserGenerators(G);

      Gct`UserGenerators := ugct; // ADDED LATER... necessary?!

      cntf := 0;
      repeat
         cntf := cntf + 1;
         f, _,_,_,_,elts, wrds := ClassicalConstructiveRecognition(Gct,cs,d,q);  // : type:=cs);
      until f or cntf ge 3; 
      if not f cmpeq true then error "MyCCR for ",type,d,q; end if;
     
      vprint evenSX, 2: "                          done, now evaluate!";
      pos    := [Position(ugct,Gct.j) : j in [1..Ngens(Gct)]];
      nslp   := [G`SLPGroup.i : i in pos];
      wrds   := Evaluate(wrds,nslp);
      vprint evenSX, 2: "                          evaluation done!";

      while #elts lt 9 do Append(~elts,elts[1]^0); Append(~wrds,wrds[1]^0); end while;

    //add inv and fpf
      if type in ["SL","SU","Sp"] then
         k  := elts[2]; wk  := wrds[2];
         if type eq "SL" then k := k^-2; wk := wk^-2; end if;
         kk := k;          wkk := wk;
         inv := elts[3]; winv := wrds[3];
         fpf := elts[4]; wfpf := wrds[4];  
         for i in [2..(d div 2)] do
            inv := inv*elts[3]^kk; winv := winv*wrds[3]^wkk;
            fpf := fpf*elts[4]^kk; wfpf := wfpf*wrds[4]^wkk;
            kk   := kk*k; wkk := wkk*wk;
         end for;
      elif type eq "O+" then
         k  := elts[8]^2; wk  := wrds[8]^2;
         kk := k;          wkk := wk;
         inv := elts[2]; winv := wrds[2];
         fpf := elts[3]; wfpf := wrds[3];  
         for i in [2..(d div 4)] do
            inv := inv*elts[2]^kk; winv := winv*wrds[2]^wkk;
            fpf := fpf*elts[3]^kk; wfpf := wfpf*wrds[3]^wkk;
            kk   := kk*k; wkk := wkk*wk;
         end for;
      elif type eq "O-" then
          elts[6] := elts[3]^(q+1); wrds[6] := wrds[3]^(q+1); //fpf for glue
          elts[7] := elts[1]*(elts[1]*elts[2])^2; wrds[7] := wrds[1]*(wrds[1]*wrds[2])^2;
      end if;
      if not type eq "O-" then
         Append(~elts,inv);  Append(~elts,fpf);
         Append(~wrds,winv); Append(~wrds,wfpf);
      end if;
 
    //add two gens for glue in SL5
      if type eq "SL" and d eq 4 then
         Append(~elts,elts[2]^-1); Append(~elts,elts[2]^2);
         Append(~wrds,wrds[2]^-1); Append(~wrds,wrds[2]^2);
      end if;
    
      if red then elts := Evaluate(wrds,UserGenerators(Gorg)); end if;   
      vprint evenSXcpu,1: str,"runtime SXEStandardGenerators for",np," is",Cputime(rnt);        
      vprint evenSX, 1: str,"END SXEStandardGenerators for",np,"with runtime",Cputime(rnt);  

      
    //"SLP test after nat rep";
    // assert wrds subset G`SLPGroup;

      return elts, wrds;
   end if;

   if natrep and not silent then "StdGens: COULD USE SMALLER NAT REP BUT DON'T"; end if;

 //Base cases
   if d le 5 
          or (type  eq "SU" and d in [7])
          or (type eq "Sp" and d in [6]) 
	  or (type eq "O-" and d in [6,8,10])  //because in d=10 we glue in 10...  
          or (type eq "O+" and d in [6,8]) then

      elts, wrds := SXEBaseCaseBlack(G:lv:=lv);
      if red then elts := Evaluate(wrds,UserGenerators(Gorg)); end if;   
      vprint evenSX, 2: "evaluation ok for std gens of",np;                                 
      vprint evenSXcpu,1: str,"runtime SXEStandardGenerators for",np," is",Cputime(rnt);        
      vprint evenSX, 1: str,"END SXEStandardGenerators for",np,"with runtime",Cputime(rnt); 
      return elts, wrds;
   end if;
 
  
 //recurse to first group
   vprint evenSX, 1: str,"   get first subgroup in ",d;
   if type in ["SL"] and d eq 6 then 
      tmp := [2,4]; 
   elif type in ["O+","O-"] and d eq 12 then 
      tmp := [4]; 
   else 
      tmp := []; 
   end if;
  
 //have repeat loop for 8 in [m,d-m] and type OmegaPlus 8
  
   A          := false;
   m          := 0;

   cntA := 0;
   cntB := 0;
   cntC := 0;


   firstRound := true;
   havetriedglue := false;
   oneOp8 := false; 

   tryglue:=1;

   repeat

    //"Start rec process for",G`natParams;
    //check if one group is OmegaPlus8 or Sp4
     
      vprint evenSX, 2: "--------->  in",G`natParams," number of tries A, B, all:", cntA,cntB,cntC;
      cntC := cntC + 1;
 
      if firstRound or not oneOp8 then
         A, m       := SmallerClassicalGroup(G : range := tmp, silent:=silent); 

       //"In LOOP: Constructed new A",A`natParams,"in",G`natParams;

         roundA     := 1;
         firstRound := false;
         cntA := cntA + 1;
         vprint evenSX, 1: str,"    got smaller group of degree",m;     

         vprint evenSX, 2: "--------->  in",G`natParams," number of tries A, B, all:", cntA,cntB,cntC;
         cntC := cntC + 1;
         eltA, wrdA  := MyCCRwithElts(A,m,q); 
         wrdA        := Evaluate(wrdA,A`UserWords);
         GC          := SXECopyGroup(G);
         eltA        := [Generic(Universe(eltA))| x : x in eltA];     
         vprint evenSX, 1: str,"   finished top group of deg",m,"in",d,"continue with",d-m;

         if A`type eq "O+" and m eq 8 then
            graphAslp := SXEOp8GraphAutSLPs(q);
            graphA    := true;
            nrslpA    := 3;
            oneOp8    := true;
         else
            graphAslp := 0;
            graphA   := false;
            nrslpA   := 1;
         end if;
      else

       //"ok in graph A part"; 
          tryglue := tryglue +1; 
         if havetriedglue or tryglue gt 3 then
            tryglue := 1;
            roundA := roundA + 1;
 
             //"apply graph aut group A",roundA;          
          //"APPLY GRAPH AUTS TO FIRST GROUP A",roundA;

            eltA := Evaluate(graphAslp,eltA);
            wrdA := Evaluate(graphAslp,wrdA);
            eltA, wrdA := SXEaddOp8prelimElts(eltA,wrdA);  
  
            if roundA eq 5 then 
             //"APPLICATION OF 3 graph auts A did not work!!! -- start all over";
               firstRound := true;
            end if;
         end if; 
         havetriedglue := false;
      end if; 

     //have repeat loop for d=6; sometimes we didn't construct a nat embedded sl2
      getC := 0;
      repeat    
         getC := getC + 1;
         C,Cw := SXECentraliserOfInvolution(GC,eltA[10],wrdA[10]);                                      
         if type eq "SU" and d eq 6 then
            B  := SXEgetSU2(C,eltA[11],wrdA[11],G) ; // :cb:=SXEBaseChangeInvolution(eltA[10]));
         else 
            B  := SXEgetSection(C,eltA[11],wrdA[11],G,d,p,d-m,type);//:cb:=SXEBaseChangeInvolution(eltA[10]));
         end if;   
      vprint evenSX, 2:" ---------->  in",G`natParams," found correct group B?",not B cmpeq false;
      until not B cmpeq false or getC gt 3;

      if B cmpeq false then 
       //"could not find B in C, so B is false and we start over";
      else
       //"ok, found B",B`natParams;
      end if;

      gens := false;
      if not B cmpeq false then

       //" ------------>  first/second group:",A`natParams, B`natParams;

        //assert #A eq #OmegaPlus(8,4);
       //assert IsIsomorphic(B,OmegaPlus(4,4));
       //"isom good";

         vprint evenSX,2:" ------------>  first/second group:",A`natParams, B`natParams;
         oneOp8 := (A`type eq "O+" and m eq 8) or (B`type eq "O+" and (d-m) eq 8) or (B`type eq "Sp" and (d-m) eq 4);

         if G`type eq "O+" and d-m eq 6 and B`type eq "SL" then
            B`type := "O+";
            B`natParams := <"O+",6,q,2>;
         end if;
         if G`type eq "O-" and d-m eq 6 and B`type eq "SU" then
            B`type := "O-";
            B`natParams := <"O-",6,q,2>;
         end if;
         if G`type eq "O-" and d-m eq 4 and B`type eq "SL" then
            B`type := "O-";
            B`natParams := <"O-",4,q,2>;
         end if; 
         if G`type eq "SU" and d-m eq 2 and B`type eq "SL" then
            B`type := "SU";
            B`natParams := <"SU",2,q,2>;
         end if;

         vprint evenSX, 1: str,"   continue with second group of degree ",d-m;

         tryB := 1; 

         Bc := SXECopyGroup(B);

         repeat

            vprint evenSX,2: " -------------> in",G`natParams," number of tries A, B, all:", cntA,cntB,cntC;
            B         := SXECopyGroup(Bc);
            cntB      := cntB + 1;
    
           
            eltB, wrdB := MyCCRwithElts(B,d-m,q); 
            wrdB      := Evaluate(wrdB,B`UserWords); 
            eltB      := [Generic(Universe(eltB))| x : x in eltB];

            if B`type eq "Sp" and d-m eq 4 then
               graphBslp := SXESp4GraphAutSLPs(q);
               graphB   := true;
               nrslpB   := 2;
            elif B`type eq "O+" and d-m eq 8 then
               graphBslp := SXEOp8GraphAutSLPs(q);
               graphB   := true;
               nrslpB    := 3;
            else
               graphBslp := 0;
               graphB   := false;
               nrslpB   := 1;
            end if;

         //TEST THE TWO SMALLER GROUPS
           if false then
              "first group",A`natParams;
              "second group",B`natParams;
              "ok test stuff"; 
              "first group",A`natParams;
              "second group",B`natParams;
              "commute?";
               forall(a){a : a in eltA | forall(b){b : b in eltB | a*b eq b*a}};
               assert Evaluate(wrdA,UserGenerators(G)) eq eltA; 
               assert Evaluate(wrdB,UserGenerators(G)) eq eltB;
               SXEcheckPresentation(A`natParams[1],eltA,A`natParams[2],A`natParams[3]);
               SXEcheckPresentation(B`natParams[1],eltB,B`natParams[2],B`natParams[3]);
               "eval and pres ok, now glue";
               "SLP test 1";  
               assert wrdA subset G`SLPGroup;
               assert wrdB subset G`SLPGroup;
               "SLPGroup OK";
           end if;
               
           if graphB then

             //"SLP test 2";        
             //assert wrdA subset G`SLPGroup;
             //assert wrdB subset G`SLPGroup;
             //"SLPGroup OK";


               havetriedglue := true;
             //"start glue in graphB";

               for i in [1..nrslpB] do
                  vprint evenSX, 1: str,"   try ",tryB," to glue",m,"with",d-m,"for type",type;
                  if type eq "SL" then gens, wrds := SXEGlueSL(G,eltA,wrdA,eltB,wrdB,m); end if;
                  if type eq "SU" then gens, wrds := SXEGlueSU(G,eltA,wrdA,eltB,wrdB,m); end if;
                  if type eq "O+" then gens, wrds := SXEGlueOp(G,eltA,wrdA,eltB,wrdB,m); end if;
                  if type eq "Sp" then gens, wrds := SXEGlueSp(G,eltA,wrdA,eltB,wrdB,m); end if;
                  if type eq "O-" then gens, wrds := SXEGlueOm(G,eltA,wrdA,eltB,wrdB,m); end if;
                  if gens cmpeq false then    
                   //"apply graph aut B!!!";          
                     eltB := Evaluate(graphBslp,eltB);
                     wrdB := Evaluate(graphBslp,wrdB);
                     if B`type eq "O+" then 
                        eltB, wrdB := SXEaddOp8prelimElts(eltB,wrdB);
                     else
                        eltB, wrdB := SXEaddSp4prelimElts(eltB,wrdB);
                     end if;
                  else
                     break; 
                  end if;
               end for;
               if gens cmpeq false then 
                //"group B is",B`natParams,"and graph aut strategy did NOT work!!!";
               end if;

            else
 

               
              //"SLP test 3";
             //assert wrdA subset G`SLPGroup;
             //assert wrdB subset G`SLPGroup;
             //"SLPGroup OK";

               havetriedglue := true;
            //"start glue";

               vprint evenSX, 1: str,"   try ",tryB," to glue",m,"with",d-m,"for type",type;
               if type eq "SL" then gens, wrds := SXEGlueSL(G,eltA,wrdA,eltB,wrdB,m); end if;
               if type eq "SU" then gens, wrds := SXEGlueSU(G,eltA,wrdA,eltB,wrdB,m); end if;
               if type eq "O+" then gens, wrds := SXEGlueOp(G,eltA,wrdA,eltB,wrdB,m); end if;
               if type eq "Sp" then gens, wrds := SXEGlueSp(G,eltA,wrdA,eltB,wrdB,m); end if;
               if type eq "O-" then gens, wrds := SXEGlueOm(G,eltA,wrdA,eltB,wrdB,m); end if;
 
            end if;  

          //"did it work?",not(gens cmpeq false); 

            tryB := tryB + 1;
            if tryB gt 100 then error "gluing didn't work"; end if;
            if gens cmpeq false then 
                vprint evenSX,2: " --------> in",G`natParams," gluing went wrong, rec B again,  try nr",tryB; 
            end if;
        until not gens cmpeq false or tryB eq 2;

      end if;

   until not gens cmpeq false;

   if red then gens := Evaluate(wrds,UserGenerators(Gorg)); end if;

//"test";
//  assert gens eq Evaluate(wrds,UserGenerators(G));
// SXEcheckPresentation(type,gens,d,q);
// "ok";

    
            //"SLP test 4";
            //assert wrds subset G`SLPGroup;
           //"SLPGroup OK";


   vprint evenSXcpu,1: str,"runtime SXEStandardGenerators for",np," is",Cputime(rnt);        
   vprint evenSX, 1: str,"END SXEStandardGenerators for",np,"with runtime",Cputime(rnt);  
   return gens,wrds;
end function;



/************************************************************************/
/* G isomorphic to a classical matric group
/*
/***********************************************************************/
intrinsic Internal_ClassicalSolveEven (G :: Grp, type :: MonStgElt, d :: RngIntElt, q :: RngIntElt : onlyBlack:=SXEonlyBlack)  -> [], []
{G is isomorphic to a classical group of specificied <type> in 
dimension d over field of EVEN characteristic and size q; 
the string <type> is one of SL, Sp, SU, Omega+, Omega-; 
return standard generators of G and their SLPs in the defining user generators of G}


   require IsEven (q) and IsPrimePower (q): "Field size is not valid";
   require d ge 2: "Dimension must be at least 2";
   require type in ["SL", "Sp", "SU", "Omega+", "Omega-"]: 
      "Type is not valid";

   vprint evenSX,2: "CALL BLACK ClassicalSolveEven",type,d;
   vprint ClassicalRecognition,2: "ClassicalSolveEven (black) for",type,d;

   if type eq "Omega+" then type := "O+"; elif type eq "Omega-" then type := "O-"; end if;
   G`natParams := <type,d,q,Factorisation(q)[1][1]>;
   G`type      := type;

    if d eq 2 and type[1] in ["O+","O-","Sp"] then
        error "degree for Sp, O+, and O- must be at least 4";
    end if;

    np := G`natParams;

  //make sure the group will have the correct flags
    if assigned G`RandomProcess then delete G`RandomProcess; end if;
    if assigned G`SLPGroup then delete G`SLPGroup; end if;
    if assigned G`cob then delete G`cob; end if;
    if assigned G`UserWords then delete G`UserWords; end if;
    if assigned G`initialised then delete G`initialised; end if;
    if assigned G`natParams then delete G`natParams; end if;

   
  //initialise group and start computation
    G`natParams := np;
    SXEInitGroup(G : type := np[1]);


    E, W := SXEStandardGeneratorsEven(G:onlyBlack:=onlyBlack);

    if type eq "SL" then nr := 4;
    elif type eq "SU" then nr := 7;
    elif type eq "Sp" then nr := 6;
    elif type eq "O+" then nr := 8;
    elif type eq "O-" then nr := 5;
    end if; 

  //if possible, then replace G`SLPGroup by WordGroup(G)
    if Ngens(G) eq #UserGenerators(G) then
        if forall(i){i : i in [1..Ngens(G)] | G.i eq UserGenerators(G)[i]} then
           WG := WordGroup(G);
           G`SLPGroup := WG;
           W := Evaluate(W,[WG.i : i in [1..Ngens(G)]]);           
         //"reseted SLPGroup";
        end if;
   end if;

  //"FINAL"; 
  //"test";
  //assert E eq Evaluate(W,UserGenerators(G));
  //SXEcheckPresentation(type,E,d,q);
  //"ok";
  //assert W subset G`SLPGroup;
  //"ok";
  //if Ngens(G) eq #UserGenerators(G) then  assert W subset WordGroup(G); end if;
  //"ok";

    return [E[i] : i in [1..nr]], [W[i] : i in [1..nr]];
end intrinsic;



