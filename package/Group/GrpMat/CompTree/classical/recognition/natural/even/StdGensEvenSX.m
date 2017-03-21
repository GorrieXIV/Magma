freeze;


/*********************************************************************/
/* INVOLUTIONS AND STANDARD GENERATORS FOR FINITE CLASSICAL GROUPS   */
/*       IN NATURAL REPRESENTATION AND EVEN CHARACTERISTIC           */
/*                                                                   */
/*    Heiko Dietrich, Eamonn O'Brien, Charles R. Leedham-Green       */
/*     Implementation by Heiko Dietrich (and Eamonn O'Brien)         */
/*********************************************************************/
/*
/* Let G=SX(d,q) with q=2^n and d>1 be a finite classical group in 
/* natural representation and even characteristic where SX is one of
/* of "SL", "SU", "Sp", "O+" (OmegaPlus), or "O-" (OmegaMinus). 
/* If the type is "O+" or "O-", then let d>2 be even. 
/*
/* The algorithms provided in this file construct an involution in G 
/* of large (or small) corank, and standard generators of G, both with 
 /* SLPs in the UserGenerators of G.
/*
/*
/* MAIN FUNCTIONS
/****************
/* There are two main functions; the input G is as described above.
/*
/* 1/ InvolutionClassicalGroupEven(G: type,smallCorank) --> g,w,r
/*    
/*    - g is an involution of corank r in G, 
/*    - w is an SLP in G`SLPGroup such that
/*          g eq Evaluate(w,UserGenerators(G))
/*
/*    If the type is not OmegaMinus and smallCorank=false, then the
/*    involution g is a 'good' involution.
/*    - The optional parameter "type" is one of "SL", "SU", "Sp", 
/*      "O+", "O-", and MUST describe the type of G.
/*    - The optional parameter "smallCorank" is either true or false.
/*      If true, then involution does not have large corank. 
/*      The default is false, and the corank of g is as follows:
/*      * If type is not "O-","O+", then  r = (Degree(G) div 2). 
/*      * If G=OmegaPlus(4m,q) or G=OmegaPlus(4m+2,q), then r = 2m.
/*      * If G=Sp(4m,q) or G=Sp(4m+2,q), then r = 2m.
/*      * If G=OmegaMinus(d,q) and q>2, then r is even and r=O(d/4).
/*      * If G=OmegaMinus(d,2) and d>14, then r is even and r=O(d/4).
/*
/* 2/ SolveClassicalEven( G : type ) --> elts, wrds, cob
/*
/*    - elts are the standard generators of the standard copy of G as 
/*      defined in mgrp/classical/recognition/standard.m;
/*    - cob is a base change matrix
/*    - wrds are SLPs in G`SLPGroup such that 
/*
/*     elts eq [cob*Evaluate(w:UserGenerators(G))*cob^-1: w in wrds].
/*
/*    The optional parameter type is one of "SL","SU","Sp","O+","O-",
/*    and MUST describe the type of G.
/*
/*
/* STRUCTURE OF THIS FILE
/************************
/*    I. PRELIMINARY FUNCTIONS
/*   II. KILLFACTOR AND FORMULA
/*  III. CONSTRUCT SMALLER SX
/*   IV. CONSTRUCT INVOLUTIONS
/*    V. FIND TWO SX
/*   VI. PRELIMINARIES FOR CONSTRUCTING STANDARD GENERATORS
/*  VII. SOME BASE CASE FUNCTIONS 
/* VIII. CONSTRUCT STANDARD GENERATORS
/*
/*
/* COMMENTS 
/******************************
/*  0/ Be aware of a time blow-up when Magma is not freshly started.
/*  1/ RecogniseSU4 might not work for large fields; this has impact
/*     also for OmegaMinus
/*  2/ For very large fields, "ProjectiveOrder( - : Proof:=false)" 
/*     can take quite long.
/*  3/ The word lengths for Sp and O+ is rather large. Reason:
/*     TwoSXEC constructs a smaller Sp and O+ resp. in a centraliser!
/*  4/ InvolutionClassicalGroupEven with smallCorank=true might 
/*     sometimes be slower than RandomInvolutionSmallField.
/*  5/ For Sp, O+, O- over GF(2), everything is slower! 
/*     We cannot reduce to degree d-6 and d-4; hence, O-(14,2) 
/*     and O+-(i,2) with i<= 12  are base cases!
/*     In general, GF(2) and GF(4) is slower.
/*
/* TO-DO
/********
/*  1/ Check parameters (priorities) for CompTree calls; 
/*     avoid circular calls!
/*  2/ Reduce number of generators in classical groups (rewrite!)
/*     for example, in classical groups extracted from centralisers
/*********************************************************************/
/*********************************************************************/




//Attributes for the groups
AddAttribute(GrpMat,"COB"); 
AddAttribute(GrpMat,"initialised");
AddAttribute(GrpMat,"type");

//Verbose modes SXEC = SX Even Characteristic
//Verbose mode for constructing the involution
declare verbose SXECinv, 5;
SetVerbose("SXECinv",0);

//Verbose mode for constructing standard generators
declare verbose SXECstdgens, 5;
SetVerbose("SXECstdgens",0);

//Verbose mode for the CPU time
//usual level: 1
//level 2 also shows runtime of MyCentraliserOfInvolution
//        if a check using "Sections" is done
declare verbose SXECcpu, 5;
SetVerbose("SXECcpu",0);


//forward declarations
forward StandardGeneratorsSXEven;
forward StandardGeneratorElements;
forward ConstructInvolutionEvenMain;
forward SolveSL4;
forward SolveSLSU5;
forward SolveSp6;
forward SolveOp6;
forward SolveOm6;




/*********************************************************************/
/*********************************************************************/
/* 
/* I. PRELIMINARY FUNCTIONS
/*
/*********************************************************************/
/*********************************************************************/




/*********************************************************************/
/* New version of "Sections"
/* time blow up possible, but no memory blow up (?)
/*********************************************************************/
MyDefSections := function(G)
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
    end for;
    return section;
end function;


/*********************************************************************/
/* USE ALWAYS MYSECTIONS?
/* if not, then time blow-up
/* if so, then memory blow-up (?)
/*********************************************************************/
MySections := function(G) return MyDefSections(G); end function;


/*********************************************************************/
/* Input:  matrix g     
/* Output: rank of g-1
/*********************************************************************/
Corank := function(g)
    MA := MatrixAlgebra(BaseRing(Parent(g)),Nrows(g));
    return Rank(MA!g-Identity(MA));
end function;


/*********************************************************************/
/* Input:  group element g
/* Output: test if g is a non-trivial involution
/*********************************************************************/
IsInvolution := function(g)
    return (g^2 eq g^0) and not (g eq g^0);
end function;


/*********************************************************************/
/* Input:  matrix involution g        
/* Output: base change matrix B such that B*g*B^-1 has Suzuki form
/*********************************************************************/
BaseChangeInvolution := function(g)
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
/* Input:  matrix group G
/* Output: true if group contains SL in natural rep
/*********************************************************************/
MyIsLinearGroup := function(G)
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
MyIsUnitaryGroup := function(G)
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
MyIsOmegaPlusGroup := function(G)
    if IsAbsolutelyIrreducible(G) eq false then return false; end if;
    if Degree(G) eq 1 then return true; end if;
    erg := IsOrthogonalGroup(G);
    if not erg then return false; end if;
    flag, type, form := OrthogonalForm(G);
    if flag and type eq "orth+" then 
        if Degree(G) eq 4 then 
          //"check order OmegaPlus4";
          //if not #G eq #OmegaPlus(4,BaseRing(G)) then 
          //    return false; 
          //end if;   
        end if;
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
MyIsOmegaMinusGroup := function(G)
    if IsAbsolutelyIrreducible(G) eq false then return false; end if;
    if Degree(G) eq 1 then return true; end if;
    erg := IsOrthogonalGroup(G);
    if not erg then return false; end if;
    flag, type, form := OrthogonalForm(G);
    if flag and type eq "orth-" then
        if Degree(G) eq 4 then
          //"check order OmegaMinus4";
          //if not #G eq #OmegaMinus(4,BaseRing(G)) then 
          //    return false; 
          //end if;   
        end if; 
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
MyIsSymplecticGroup := function(G)
    if IsAbsolutelyIrreducible(G) eq false then return false; end if;
    if Degree(G) eq 1 then return true; end if;
    t := IsSymplecticGroup(G);
    if t cmpeq true then G`type := "Sp"; end if;
    return t;
end function;


/*********************************************************************/
/* Input:  matrix group G  
/* Output: true if group contains Sp or Omega+
/*********************************************************************/
MyIsSpOmega := function(G)
    if    MyIsOmegaPlusGroup(G) then return true;
    elif  MyIsSymplecticGroup(G) then return true;
    else return false;
    end if;
end function;


/*********************************************************************/
/* Input:  matrix group G
/* Output: type if G is SL, SU, Sp, O+ or O-
/*********************************************************************/
WhichType := function(G)
    F := BaseRing(G);
    if assigned G`type then return G`type; end if;
    if Degree(G) eq 2 and #F eq 2 and MyIsLinearGroup(G) then
        return "SL";
    end if;
    if Degree(G) eq 2 and #F eq 4 and MyIsUnitaryGroup(G) then
        return "SU";
    end if;
    if RecognizeClassical(G) then
        t := ClassicalType(G);
        if t cmpeq false then return false; end if;
        if   t eq "linear"          then G`type := "SL"; return "SL";
        elif t eq "symplectic"      then G`type := "Sp"; return "Sp";
        elif t eq "unitary"         then G`type := "SU"; return "SU";
        elif t eq "orthogonalminus" then G`type := "O-"; return "O-";
        elif t eq "orthogonalplus"  then G`type := "O+"; return "O+";
        end if;
    end if;
    return false;
end function;


/*********************************************************************/
/* Input:  type of SX ("SL","SU","O+","O-","Sp","SpO","SX")   
/* Output: corresponding IsMyType function
/*********************************************************************/
IsType := function(type)
    if   type eq "SL" then return MyIsLinearGroup;
    elif type eq "SU" then return MyIsUnitaryGroup;
    elif type eq "Sp" then return MyIsSymplecticGroup;
    elif type eq "O+" then return MyIsOmegaPlusGroup;
    elif type eq "O-" then return MyIsOmegaMinusGroup;
    elif type eq "SpO" then return MyIsSpOmega;
    elif type eq "SX" then
        return function(G) 
               return not WhichType(G) cmpeq false;
               end function;
    end if;
    error "IsType: wrong type";
end function;


/*********************************************************************/
/* Input:  matrix group G     
/* Output: G with the following flags:
/*         G`UserGenerators
/*         G`SLPGroup      - on U=UserGens
/*         G`COB           - change of base mat, id(G)       
/*         G`UserWords     - Ugen[i]=COB*Evaluate(w,OrigGens)*COB^-1
/*                           for w=UserWord[i])
/*         G`RandomProcess - on G`SLPGroup with UserGens(G)
/*         G`type          - type of group
/*********************************************************************/
InitialiseGroup := procedure(G : UserWords :=[], 
                                 type      := false)

    if not assigned G`UserGenerators then
        U := [Generic(G)!G.i : i in [1..Ngens(G)]];
        G`UserGenerators := U;
        G`SLPGroup := WordGroup (G);
    end if;
    U := UserGenerators(G);
    if not UserWords eq [] then G`UserWords := UserWords; end if; 
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
    if not assigned G`COB then G`COB := Identity(G); end if;
  //do not determine type of group
    if not type cmpeq "no" then
        if not type cmpeq false then G`type := type; end if;
        if not assigned G`type then 
            t := WhichType(G);
            if not t cmpeq false then G`type := WhichType(G); end if;
        end if;
    end if;
   G`initialised := true;
end procedure;


/*********************************************************************/
/* Input:  initialised matrix group G     
/* Output: copy of G with all flags
/*********************************************************************/
MakeCopyOfInitialisedGroup := function(G)
    if not assigned G`initialised then 
        if not assigned G`type then 
            InitialiseGroup(G : type := "no");
        else
            InitialiseGroup(G);
        end if; 
    end if;
    ugens            := [Generic(G)!u : u in UserGenerators(G)];
    H                := sub<Generic(G) | ugens>;
    H`UserGenerators := ugens;
    H`SLPGroup       := G`SLPGroup;
    H`UserWords      := G`UserWords;
    H`RandomProcess  := G`RandomProcess;
    H`initialised    := true;
    H`COB            := G`COB;
    if assigned G`type then H`type := G`type; end if;
    return H;
end function;


/*********************************************************************/
/* Input:   matrix group G
/* Output:  random g in G and corresponding SLP w in G`SLPGroup
/* Options: onlyElt: returns only element (no SLP)
/*********************************************************************/
MyRandomWord := function( G : onlyElt := false)
    if not assigned G`RandomProcess then 
        InitialiseGroup(G : type := "no"); 
    end if;
    g, w := Random(G`RandomProcess);
    if onlyElt then return g; else return g,w; end if;
end function;


/*********************************************************************/
/* Input:  initialised matrix group G and base change matrix
/* Output: initialised copy of G w.r.t. new base
/*********************************************************************/
ApplyCOB := function(G, CB)
   U     := UserGenerators(G);
   CBinv := CB^-1;
   U     := [Generic(G) ! (CB * U[i] * CBinv): i in [1..#U]];
   K     := sub <Generic(G) | U>;
   K`UserGenerators := U;
   K`SLPGroup       := G`SLPGroup;
   K`UserWords      := G`UserWords;
   if assigned K`type then K`type := G`type; end if;
   K`RandomProcess  := RandomProcessWithWords(K:
                                              WordGroup  := K`SLPGroup,
                                              Generators := U);
   K`COB            := CB*G`COB;
   if assigned G`type then K`type := G`type; end if;
   K`initialised    := true;
   return K;
end function;


/*********************************************************************/
/* Input:  matrix g and list of indices
/* Output: submatrix with entries g[i][i], i in index
/*         (submatrix must be invertible)
/*********************************************************************/
ExtractBlockNEW := function(g, index)
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
ExtractGroup := function (G, action : type    := false, 
                                      onlyGrp := false)
   U   := UserGenerators(G);
   tmp := GL(#action,BaseRing(G));
   U   := [tmp!ExtractBlockNEW(U[i], action): i in [1..#U]];
   B   := sub<tmp | U>;
   if onlyGrp then return B; end if;
   B`UserGenerators := U;
   if assigned G`SLPGroup then B`SLPGroup := G`SLPGroup; end if;
   if assigned G`UserWords then B`UserWords := G`UserWords; end if;
   if not type cmpeq false then B`type := type; end if;
   InitialiseGroup(B);
   return B;
end function;


/*********************************************************************/
/* Input:  matrix group G, g in G, w corresponding SLP in G`SLPGroup 
/*         f a factor of minimal polynomial of g
/* Output: power of g (and corresp. SLP) which acts as 
/*         scalar matrix on ker(f(g))
/*********************************************************************/
TrivialActionOnInvBlock := function(G,g,w,f : trivial := false)
    MA  := MatrixAlgebra(BaseRing(G),Degree(G));
    h   := MA!g;
  //the next evaluation is a bottleneck for large groups
    B   := Basis(Nullspace(Evaluate(f,h)));
    dim := #B;
    Bim := [i*h : i in B];
    B   := Matrix(Degree(G),&cat([Eltseq(u) : u in B])); 
  //now mat describes restriction of g to ker(f(g))
    mat := &cat([Eltseq(u): u in Solution(B,Bim)]);
  //note that dim = Degree(f) only minPol(g)=f^e, in gen dim>Degree(f)
    mat := GL(dim,BaseRing(G))!mat;
  //act trivially or only as scalars on block?
    if trivial then
        o := Order(mat); //: Proof:=false);
    else
      //for very large fields this can be a bottleneck
      //"start proj order";
        o := ProjectiveOrder(mat : Proof:=false);//: Proof:=false);
      //"done";
    end if;;
    return g^o, w^o, dim, o, mat;
end function;


/*********************************************************************/
/*Input:  matrix group G in block form s.t. there is a
/*        m x m block starting at (index,index)
/*Output: element (+SLP) whose restriction to this block has
/*        odd order and is fixed point free
/*********************************************************************/
ElementActsFPF := function(G, index, m)
    vprint SXECinv,5: "     start ElementsActsFPF";
    P := GL(m,BaseRing(G));
    repeat
        repeat
            g, w := MyRandomWord(G);
            s    := P!ExtractBlock(g, index, index, m, m);
        until not PrimeOrderElement(s,2);
        ev   := {x[1] : x in Eigenvalues(s)};
    until not (1 in ev);
  //c odd order, no FP --> c^2 odd order, no FP
  //if g=[c0*;010;00c], then  g^2 has odd order!
    vprint SXECinv,5: "     end ElementsActsFPF";
    return g^2, w^2;
end function;


/*********************************************************************/
/* Input:   initialised matrix group G
/* Output:  derived subgroup of G with SLPs (Monte Carlo)
/* Comment: only needed in Degree4Involution and SolveSLSU5
/*********************************************************************/
MyDerivedSubgroupWithWords := function(G : NumberOfElements := 10) 
    vprint SXECinv, 5: "     start MyDerivedSG ind degree",Degree(G);
    gens  := []; 
    words := [];
    U     := UserGenerators(G);
    Limit := Minimum(2*#U, #U + 10);  
    nmr   := 0;
    repeat
       nmr +:= 1;
       x, w := MyRandomWord(G);
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
    if assigned G`COB then D`COB := G`COB; end if;
    InitialiseGroup(D : UserWords :=  words); 
    vprint SXECinv, 5: "     end MyDerivedSG in degree",Degree(G);
    return D;
end function;


/*********************************************************************/
/* Input:   initialised mgrp G, elt g with SLP w
/* Output:  centraliser of g with SLPs (Monte Carlo, Bray's Algorithms)
/*********************************************************************/
MyCentraliserOfInvolution := function(G,g,w,type)
    vprint SXECinv, 3: "     start MyCentraliserOfInvolution";
    t := Cputime();
    F := BaseRing(G);
  //in particular for F=GF(2) and GF(4) it's necessary to check
  //if nat. module of centraliser contains all required sections!
    if #F in [2,4] then chk := true; else chk := false; end if;
    nrg := 25;
  //set minimal number of gens:
  //For SL(100,2) and SL(30,2) we sometimes need 86 and 58 generators 
  //to to have all required sections!
    if type eq "SL" then
        if   #F eq 2 then nrg := 100; 
        elif #F eq 4 then nrg := 40;
        elif #F eq 8 then nrg := 30;
        end if;
    elif type eq "SU" and #F eq 4 then 
        nrg := 40;
    elif type in ["Sp","O+","O-"] then
        if not type eq "O-" then 
            type := "SpO"; 
        else 
            type := "SX"; 
        end if;
        if   #F eq 2 then nrg := 100;
        elif #F eq 4 then nrg := 50;
        elif #F eq 8 then nrg := 40;
        end if;
    end if;

  //completion check for CentraliserOfInvolution
    isCent := function(H,Ccand,inv,Cw)
        ug  := #UserGenerators(Ccand);
        flg := false;
        if ug lt nrg then return false; else flg := true; end if;
        if chk then
            S   := MySections(Ccand);
            flg := #S eq 3 and 
                   forall(t){i:i in S | IsType(type)(i) eq true};
        end if;
        return flg;
    end function;

    C,Cw := CentraliserOfInvolution(G, g, w : 
                                    Randomiser      := G`RandomProcess,
                                    CompletionCheck := isCent,
                                    NumberRandom    := nrg); 
    InitialiseGroup(C : UserWords := Cw, type := "no");
    if chk then
        vprint SXECcpu,2:"CPU time MyCentOfInv with check in degree",
                            Degree(G),":",Cputime(t);
    end if;
    vprint SXECinv,3: "     end MyCentraliserOfInvolution";
    return C,Cw;
end function;


/*********************************************************************/
/* Input:  matrix group G in natural rep, type
/* Output: G^B, B such that G^B respects "normal form"
/*********************************************************************/
MyConjugateToStandardCopy := function(G, type) 
    vprint SXECinv, 5: "     start conj form";    
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
      //elt    := StandardGeneratorElements(GF(q),n,"O-");
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
  
  //if form eq standard then 
  //    vprint SXECinv, 5: "     end conj form";  
  //    return G, Identity(G), Identity(G); 
  //end if;
 
    if   type eq "SU" then type := "unitary"; 
    elif type eq "Sp" then type := "symplectic"; 
    elif type eq "O+" then type := "orthogonalplus";
    elif type eq "O-" then type := "orthogonalminus";
    end if;
    
    x     := TransformForm(form, type);
    y     := TransformForm(standard, type)^-1;
    
    if form eq standard then cb := Identity(G); else cb := x*y; end if;
 
    cbinv := cb^-1;
    K     := ApplyCOB(G,cbinv);
    vprint SXECinv, 5: "     end conj form";    
    return K,cbinv,y;
end function;




/*********************************************************************/
/*********************************************************************/
/* 
/* II. KILLFACTOR AND FORMULA
/*
/*********************************************************************/
/*********************************************************************/




/*********************************************************************/
/* Input:   matrix group G in block diag form, 
/*          lists Alist and Blist of lists of 
/*          index positions, type SX.
/*          (either Alist=[ list ] or Alist=[list, list])
/* Output:  subgroup of G acting trivially on sections indexed
/*          in Blist, acting as group containing SX on 
/*          sections indexed by Alist. 
/*
/* Options:  Squares: have a gen system whose
/*                    squares do also generate the group
/*           Parent:  evaluate words in UserWords
/*           notSX:   does not check whether blocks
/*                    contain SX, this is necessary
/*                    if first block is reducible, which 
/*                    happens if we have Sp, O+, O-
/*                    (we consider the centraliser of a non-good
/*                     involution; degree of first block is 4)
/*********************************************************************/
KillFactor := function (G, Alist, Blist, type: Squares := false, 
                                               Parent  := true, 
                                               Limit   := 100,
                                               notSX   := false) 
/* 
"SEED ", GetSeed ();
"IN THIS FFGGFGFG";
G:Magma;
Alist, Blist, type;
*/

  //how many generators needed if notSX=true (degree 4 block)
    nrgensNotSX := 60;
    cput        := Cputime();
    d           := Degree(G);
    F           := BaseRing(G);   
    if #F in [2,4] then Limit := 1000; end if;

    if type in ["Sp","O+"] then type := "SpO"; end if;
    if type eq "O-" then type := "SX"; end if;

    vprint SXECinv,3: "     start killfactor in degree",Degree(G),
                     "with blocks ",#Alist[1],#Blist[1];
    while [] in Alist do Exclude (~Alist, []); end while;
    while [] in Blist do Exclude (~Blist, []); end while;

 //ensures that H contains the group SX on factor Alist[1]
 //if notSX then this is not possible and only ensure enough gens
    IsGoodGroup := function (H, type) 
        if notSX then 
            return #UserGenerators(H) ge nrgensNotSX; 
            //if #UserGenerators(H) le nrgensNotSX then
            //    return false;
            //else
            //    exgrp := ExtractGroup(H,Alist[1]:onlyGrp:=true);
            //    tmsec := [Degree(s) : s in MySections(exgrp)];
            //    tmdeg := Degree(exgrp)-2;
            //    if tmdeg eq 0 then tmdeg := 1; end if;
            //    if 1 in tmsec and tmdeg in tmsec then
            //        "have degs and gens",tmsec,#UserGenerators(H);
            //        return true;
            //    else
            //        return false;
            //    end if;
            //end if;
        else 
          //exgrp := ExtractGroup(H,Alist[1]:onlyGrp:=true);
          //"type in IsGoodFunction",WhichType(exgrp);
            exgrp := ExtractGroup(H,Alist[1]:onlyGrp:=true);
            return IsType(type)(exgrp);
        end if;
    end function;
   
  //find suitable element
    getElement := function(exp)
        nmr := 0;
        repeat
            g,wg := MyRandomWord(G);
            nmr +:= 1;
            B    := [* ExtractBlockNEW(g, Blist[i]): 
                                       i in [1..#Blist] *];
            o    := LCM([Order(x:Proof:=false): x in B]);
            A    := [* ExtractBlockNEW(g, Alist[i]): 
                                       i in [1..#Alist] *];
          //avoid (projective) involutions
            required := forall{i:i in [1..#A] | 
                               not IsScalar(A[i]^(exp*o))};
        until required or nmr gt Limit * 10;
        if not required then
            "Alist,Blist",Alist,Blist;
            error "KillFactor: Failed to find element in deg", d;
        end if;
        return g^o, wg^o;
    end function;

    if notSX then exp := 1; else exp := 2; end if;
    g, wg := getElement(exp);
    Large := [Generic(G)|g];
    WA    := [wg]; 
    required := [#x : x in Alist];
    Sort(~required);
    Nmr   := 0;

  //Problems if one factor is SX(2,2) since C_3 is normal
    spcCase :=  (type eq "SL" and #F eq 2 and #Alist[1] eq 2) or
                (type eq "SU" and #F eq 4 and #Alist[1] eq 2) or
                (type in ["SpO","SX"] and #Alist[1] eq 2);

    repeat 
        Nmr +:= 1;
        nmrd := 0;
        repeat
          //add more conjugates or (if spcCase) more getElements()'s
            nmrd +:= 1;
            if spcCase then 
                h,wh := getElement(1);
            else
                k,wk := MyRandomWord(G); 
                h    := g^k;
            end if;
          //still nothing found? try more getElements()'s
            if nmrd ge 75 then spcCase := true; end if;
        until (nmrd gt 100) or not h in Large;
        if nmrd gt 100 then error "KillF: no elts in class"; end if;
        Append(~Large, h);
        if spcCase then Append(~WA,wh); else Append(~WA,wg^wk); end if;
        H    := sub<Generic(G) | Large>;
        flag := IsGoodGroup(H, type); 
        if Squares then 
            K    := sub<Generic(G) | [x^2 :x in Large]>;
            flag := IsGoodGroup(K, type); 
        end if;
      //if we need many elements, then try some more getElements()
        if Nmr ge 15 then spcCase := true; end if;
    until flag or Nmr gt Limit;
   
    if Nmr gt Limit then 
        error "KillFactor: Failed to constr. gen set in", Degree(G); 
    end if;
 
  //SMALL FIELDS:
  //Add more generators to ensure that not only the blocks on the
  //diagonal are complete but also the rest
    nrg := 5;
    if type in ["SL","SpO","SX"] then
        if   #F eq 2 then nrg := 20; 
        elif #F eq 4 then nrg := 15; 
        elif #F eq 8 then nrg := 10;
        end if;
    elif type eq "SU" then
        if   #F eq 4 then  nrg := 20; 
        elif #F eq 16 then nrg := 10;
        end if;
    end if;

    for i in [1..nrg] do
        nmrd := 1;
        repeat 
            nmrd +:= 1;
            h,wh := getElement(1); 
            if nmrd ge 1000 then 
                error "killFactor: can't find elements"; 
            end if;
        until not h in Large;
        Append(~Large,h); Append(~WA,wh);
    end for;

    H                 := sub<Generic(G) | Large>;
    H`UserGenerators  := Large;
    OrigWA            := WA;
    if Parent then WA := Evaluate(OrigWA,G`UserWords); end if;

  //set type if possible
    if not notSX then
        if assigned G`type then 
          //this happens when G is [SX 0 ; 0 scalar]
            H`type := G`type; 
        elif not type in ["SX","SpO"] then
            H`type := type;
        else
            cnt := 1;
            repeat
               tp  := WhichType(ExtractGroup(H,Alist[1]:onlyGrp:=true));
               cnt := cnt +1;
            until cnt eq 5 or not tp cmpeq false;
            H`type := tp;
          //"which type at set type res,cnt",H`type,cnt;
        end if; 
    else
        H`type := false;
    end if;
    InitialiseGroup(H : UserWords := WA);
    H`COB := G`COB;
    vprint SXECinv,3: "     end killfactor";
    vprint SXECcpu,3:"CPU time KillFactor",type,"(",d,"), gens:",
                   #Large,"time:",Cputime(cput);

    if not notSX and H`type cmpeq false then
        if RecogniseClassical(ExtractGroup(H,Alist[1]:onlyGrp:=true)) then
	    "recogniseClassical found a group but";
        else
            "recogniseClassical could not find a group and";
        end if;
        tmp := ExtractGroup(H,Alist[1]:onlyGrp:=true);
        tmp: Magma;
        WhichType(tmp);
        error "KF: type of group not determined";
    end if;
    return H, true, OrigWA;
end function;


/*********************************************************************/
/*Input:  x, z group elements, x of order k
/*Output: element in C_G(x) 
/*********************************************************************/
Formula := function(x, z, k)
   return x*z*(x*x^z)^((k-1) div 2);
end function;


/*********************************************************************/
/*Input:  matrix group H in upper block form (dim m,2d-m,m), type
/*Output: element h (with SLP w) of odd order and fixed point 
/*        free action in middle block, COB matrix s.t.
/*        h has the form [I 0 0 // 0 B 0 // 0 0 I]
/*        NOTE: SLP w is SLP in H`UserWords!
/*********************************************************************/
FormulaElement := function(H, m, type)
    vprint SXECinv,5: "     start FormulaElement";
    F     := BaseRing(H);
    d     := Degree(H);
    K     := KillFactor(H,[[m+1..d-m]], [[1..m], [d-m + 1..d]], type);
  //now K is [I * * // 0 B * // 0 0 I] 
  //and K`UserWords SLP in H`UserWords  
    index := m + 1;
    h, w  := ElementActsFPF(K, index, d-2*m);
  //use eigenvectors from eigenspace 1 to change basis
  //note that B-I has full rank! 
    E     := Eigenspace(h, 1);  
    MA    := MatrixAlgebra(F, d);
    V     := VectorSpace(F, d);
    CB    := &cat[Eltseq(E.i): i in [1..m]] cat 
             &cat[Eltseq (V.i) : i in [m+1..d]];
    CB    := MA ! CB;
    h     := CB*h*CB^-1;
  //now h has the form [I 0 0 // 0 * * // 0 0 I] 
    MB    := KMatrixSpace(F, d - 2 * m, d);
    hm1   := h - Identity(MA);
    X     := MB ! &cat[Eltseq(V.i) : i in [m+1..d-m]]; 
  //this is middle part of h-1
    Y     := X*hm1;                          
    CB1   := Identity (MA);
    InsertBlock(~CB1, Y, m + 1, 1);
    h     := Generic(K) ! (CB1 * h * CB1^-1);
  //rows of Y are invariant under h and 
  //now h has the form [I 0 0 // 0 B 0 // 0 0 1]   
  //w is SLP in Parent of H
    w     := Evaluate(w,K`UserWords);
    vprint SXECinv,5: "     end FormulaElement"; 
    return h, w, CB1 * CB;
end function;


/*********************************************************************/
/*Input:   matrix group Q ot type  [A * * // 0 B * // 0 0 A],
/*         where A is m x m FormulaElement h with SLP wh of type
/*         [1 0 0 // 0 B 0 // 0 0 1], B fpf
/*Output:  [A0*;010;00A] and [100;0B0;001] containing SX
/*          UserGens of grps are evaluated UserWords in 
/*         "Parent" of Q, modulo COB
/*Options: glue: computes only [A0*;0I0;00A]
/*         notSX: if glue and notSX, then A might be
/*                 reducible: delete only B! 
/*********************************************************************/
FormulaAB := function(Q, m, h, wh, type : glue  := false, 
                                          notSX := false)   
    d     := Degree(Q);
    vprint SXECinv,5: "     start FormulaAB with degrees", d, m;
    F     := BaseRing(Q);

    A     := KillFactor(Q,[[1..m],[d-m+1..d]],[[m+1..d-m]],type:
                        notSX := notSX); 
    typeA := A`type;
  //now A is [A * * // 0 1 * // 0 0 A] 
  //for smallFields: KillFactor added more generators to A
    U     := UserGenerators(A);
    W     := A`UserWords;
    oh    := Order(h);
    gensA := [Formula(h, u,oh): u in U];
    W     := [Formula(wh, w, oh): w in W];
    A     := sub <Generic(Q) | gensA>;
    A`UserGenerators := gensA;
    InitialiseGroup(A: UserWords := W, type := typeA);
    A`COB  := Q`COB;
  //now A has form [A 0 * // 0 1 0 // 0 0 A]
    if glue then return A,_; end if;

    rg,wrg := ElementActsFPF(A, 1, m);
    wrg    := Evaluate(wrg, A`UserWords);
  //now rg has form [A 0 * // 0 1 0 // 0 0 A] 
  //where A has no fixed point
    B      := KillFactor(Q,[[m+1..d-m]],[[1..m],[d-m+1..d]],type: 
                            Squares := true);
    U      := UserGenerators(B);
    typeB  := B`type;
  //now B is [1 * * // 0 B * // 0 0 1]    
    org    := Order(rg);
    gensB  := [Formula(rg, U[i],org)^2: i in [1..#U]];
    W      := B`UserWords;
    W      := [Formula(wrg, W[i], org)^2: i in [1..#W]];
  //square to obtain form [1 0 0 // 0 B 0 // 0 0 1]
    B      := sub <Generic(Q) | gensB>;
    B`UserGenerators := gensB;
    InitialiseGroup(B:UserWords := W, type := typeB);
    B`COB  := Q`COB;
  //UserGens of A are evaluated A`UserWords 
  //in "Parent" of Q, modulo COB and similar UserGens of B
    vprint SXECinv,5: "     end FormulaAB";
    return A, B;
end function;


/*********************************************************************/
/*Input:   matrix group C in upper block form, indices, type
/*Output:  odd order generators of section defined by action
/*Comment: needed only in FormulaAB2
/*********************************************************************/
OddOrderGenerators := function(C, action, type)
    d     := Degree(C); 
    F     := BaseRing(C);
    gens  := []; 
    words := [];
    found := false;
    repeat
        x,wx := MyRandomWord(C);
        y    := ExtractBlockNEW(x, action);
        if not PrimeOrderElement(y,2) and not x in gens then
             Append(~gens, x);
             Append(~words, wx);
             D  := sub<Generic(C) | gens>;
             S  := MySections(D);
             fl := exists(i){i : i in [1..#S] | 
                            Degree(S[i]) eq #action};
             if fl then 
                 S     := S[i]; 
                 found := IsType(type)(S); 
             end if;
        end if;
    until found;
    D`UserGenerators := gens;
    InitialiseGroup(D : type      := type, 
                        UserWords := Evaluate(words,C`UserWords) );
    return D;
end function;


/*********************************************************************/
/*Input:  matrix group G ot type  [A*;0B] with A of degree m
/*        P is parent of G
/*Output: [A0;0I] and [I0;0B]
/*Remark: Assumes that smaller groups are of same type!
/*        (in InitialiseGroups!)
/*Comment: Needed only in SolveSL4
/*********************************************************************/
FormulaAB2 := function(G, m, type)
    vprint SXECinv,5: "     start FormulaAB2 with degrees", Degree(G);
  //helping function to construct groups using the formula
    makeGrp := function(ugens,fh,fw,uwords,cob)
        oh      := Order(fh);
        gens    := [Formula(fh, ugens[i],oh) : i in [1..#ugens]];
        grp     := sub<Generic(G) | gens>;
        grp`UserGenerators := gens;
        grp`COB := Generic(G)!cob;
        InitialiseGroup(grp : type := type, UserWords :=
                       [Formula(fw,uwords[i],oh): i in [1..#uwords]]);
        return grp;
    end function;
    F  := BaseRing(G);
    d  := Degree(G);
    MA := MatrixAlgebra(F, d);
  //now CC = [* *; 0 1] and DC = [0 *;0 1]
    C  := KillFactor(G,[[1..m]],[[d-m + 1..d]],type);
    CC := OddOrderGenerators(C,[1..m],type);
    D  := KillFactor(G,[[d-m+1..d]], [[1..m]], type);
    DD := OddOrderGenerators(D, [d - m + 1..d],type);
  //now lg=[1 0 *;0 1 0;0 0 *]
    lg, wlg := ElementActsFPF(DD, d - m + 1, m);
    wlg     := Evaluate(wlg,DD`UserWords);
    E       := Eigenspace(lg, 1);
  //use eigenvectors from eigenspace to change basis 
    V   := VectorSpace(F, d);
    CB4 := &cat[Eltseq (E.i): i in [1..m]] cat 
           &cat[Eltseq (V.i) : i in [m + 1..d]];
    CB4 := MA ! CB4;
    lg  := Generic(G)! (CB4 * lg * CB4^-1);
    CC2 := ApplyCOB(CC, CB4);
  //now make left and right copy of groups...
    L       := makeGrp(UserGenerators(CC2),lg,wlg,
                       CC2`UserWords,CC2`COB);
    rg, wrg := ElementActsFPF(L, 1, m);
    wrg     := Evaluate(wrg, L`UserWords ); 
    R       := makeGrp(UserGenerators(DD),rg,wrg,
                       DD`UserWords,L`COB);
    vprint SXECinv,5: "     end FormulaAB2 with degrees", Degree(G);
    return L, R;
end function;




/*********************************************************************/
/*********************************************************************/
/* 
/* III. CONSTRUCT SMALLER SX
/*
/*********************************************************************/
/*********************************************************************/




/*********************************************************************/
/* Input:   matrix group G, list range of possible ranks  
/* Output:  a power g^o (and corresp. SLP) of some g 
/*          in G with charPol(g)=minPol(g) squarefree, 
/*          s.t. g^o acts as a scalar on ker(f(g)) of 
/*          dimension in range, where f is irred factor
/*          of minPol(g). 
/* Remark:  does not work for some small input        
/*********************************************************************/
FindElement := function(G, range : Limit := 1000)   
    d   :=Degree(G);
    F   := #BaseRing(G);
    vprint SXECinv,5: "    start FindElement in deg/range", d, range;
    nmr := 0;
    repeat
        nmr +:= 1;
        g, w := MyRandomWord(G);
        fac  := Factorisation(CharacteristicPolynomial(g));
        deg  := [Degree(f[1]) : f in fac];
        m,i  := Maximum(deg);
        f    := fac[i][1];
      //only if charPol=minPol is squarefree
        if &+deg eq d and m in range then
          //now x acts as a scalar on factor of degree m
            x, w, dim := TrivialActionOnInvBlock(G,g,w,f);
          //note that dim=m as charPol=MinPol is squarefree
          //and order of x is odd as it divides q^deg(f)-1
            if not IsDiagonal(x) then
                vprint SXECinv,5: "     end FindElement";
                return x,w,m;
            end if;
        end if;
    until nmr gt Limit;   
    error "FindElement: failed to find pair in deg", Degree(G);
end function;


FindElementJustTestSth := function(G, range : Limit := 1000)
    d   :=Degree(G);
    F   := #BaseRing(G);
    q   := F;
    vprint SXECinv,5: "    start FindElement in deg/range", d, range;
    nmr := 0;
    repeat
        nmr +:= 1;
        repeat g, w := MyRandomWord(G); until not PrimeOrderElement(g,2);
        g    := g^((q^3-1) div (q-1));
        w    := w^((q^3-1) div (q-1));
        "use new";
        if not Order(g) eq 1 and 3 in [x[2] : x in Eigenvalues(g)] then
            return g,w,3;
        end if;
       
    until nmr gt Limit;
    error "FindElement: failed to find pair in deg", Degree(G);
end function;



/*********************************************************************/
/* FindElement for OmegaPlus(8,q), OmegaMinus(16,2), OmegaMinus(18,2)     
/*********************************************************************/
FindElementOp := function(G, range : Limit := 1000)   
    d   := Degree(G);
    F   := #BaseRing(G);
    vprint SXECinv,5: "    start FindElement for OmegaPlus(8)";
    nmr := 0;
    if G`type eq "O+" then fdeg := [2]; else fdeg := [4..d-6]; end if;
    repeat
        repeat
            nmr +:= 1;
            g, w := MyRandomWord(G);
            fac  := Factorisation(CharacteristicPolynomial(g));
        until forall(i){i: i in fac | i[2] eq 1} and 
              exists(j){j:j in [1..#fac] | Degree(fac[j][1]) in fdeg};
        deg := [Degree(k[1]) : k in fac];
        pos := [k : k in [1..#fac] | not k eq j];
        f   := &*[fac[k][1] : k in pos];
      //now x acts as a scalar on factor of degree m
        x, w, dim,o6,m6  := TrivialActionOnInvBlock(G,g,w,f);
        if not IsDiagonal(x) then
            vprint SXECinv,5: "     end FindElement";
            return x,w,d-Degree(fac[j][1]);
        end if;
    until nmr gt Limit;   
    RecogniseClassical(G);
    ClassicalType(G);
    error "FindElement: failed for OmegaPlus(8)";
end function;


/*********************************************************************/
/* Input:  matrix group G, list of elements L and SLPs W, rank R
/*         expected sum of ranks sum, type
/* Output: 2-gen subgroup of H which acts as scalars on
/*         space of dimension s-d with s in sum and 
/*         contains SX on section of dimension 2d-s        
/*********************************************************************/
InvestigatePair := function(G,L,R,W,sum, type)
    vprint SXECinv,5: "     start InvestigatePair";
    d      := Degree(G);
    j      := #R; 
    isType := IsType(type); 

  //isType := function(x)
  //    rrr := WhichType(x);
  //    return rrr cmpeq "O+" or rrr cmpeq "O-";
  //end function;

    for i in [1..#R-1] do
        if R[i]+R[j] in sum then
           exp := 2*d-(R[i]+R[j]);
           H   := sub< Generic(G) | L[i], L[j]>;
           S   := MySections(H);
           if exists(x){x:x in S|Degree(x) eq exp and isType(x)} then  
              vprint SXECinv,5: "     end InvestigatePair";
              H`UserGenerators := [L[i],L[j]];
              InitialiseGroup(H : UserWords := [W[i],W[j]], 
                                  type      := "no");
              if type in ["SL","SU","O+","O-","Sp"] then  
                  H`type := type;
              else
                  H`type := WhichType(x);
              end if;
              return true, H, Degree(x);             
           end if;
        end if;
    end for;
    vprint SXECinv,5: "     end InvestigatePair";
    return false, _,_;
end function;


/*********************************************************************/
/* Input:  matrix group G such that sections of G have one block
/*         of size m with G acting as SX, and one block of 
/*         size d-m with G acting as scalar matrices
/* Output: base change matrix such that top left corner 
/*         contains SX of rank m         
/*********************************************************************/
MakePretty :=  function (G, m)
    vprint SXECinv,5: "    start MakePretty";
    S     := MySections(G);
  //By constr: One block of deg m, rest dim 1
    degs  := [Degree(S[i]): i in [1..#S]];
    index := Position (degs, m);
    other := Rep([x : x in [1..#S] | x ne index]);
    F     := BaseRing (G);
    d     := Degree (G);
    MA    := MatrixAlgebra (F, d);
    V     := VectorSpace (F, d);
    E     := [* *]; 
    U     := [* *];
    for i in [1..Ngens(G)] do
        alpha := UserGenerators(S[other])[i][1][1];
        E[i]  := Eigenspace (G.i, alpha);
        U[i]  := (G.i +  ScalarMatrix(d, alpha));
    end for; 
  //Basis of intersection of Eigenspaces
    BE := Basis(&meet([x : x in E]));
    Y  := &cat[[U[j][i] : i in [1..d]]: j in [1..#U]];
    B  := Basis(sub < V | Y >); 
    T  := [B[i] : i in [1..#B]] cat [BE[i] : i in [1..#BE]];
    CB := MA ! &cat [Eltseq (t): t in T]; 
    vprint SXECinv,5: "     end MakePretty"; 
    return CB; 
end function;


/*********************************************************************/
/* Input:  initialised matrix group G, rank, type of SX     
/* Output: subgroup H of G which acts on a section as a
/*         overgroup of SX(k,F) with k in rank and as 
/*         scalars on a space of dimension d-k
/*********************************************************************/
SmallerSXEC := function( G, rank ,type: Limit := 10000 )
    vprint SXECinv,4: "    start SmallerSXEC";
    if Type(rank) eq RngIntElt then rank := [rank]; end if;
    e     := Maximum(rank);
    d     := Degree(G);
    range := [d-e+1..d-1];
    sum   := [2*d-e : e in rank];
    L := []; R := []; W:= [];
    total := 0;

    if not type eq "SX" then
        if   G`type eq "Sp" then type := "SpO";
        elif G`type eq "O+" then type := "O+"; 
        elif G`type eq "O-" then type := "O+"; 
        end if;
    end if;

  //special case?
    spcase := (G`type eq "O+" and d eq 8)
              or (#BaseRing(G) eq 2 and G`type eq "O-" 
                  and d in [16,18]);

  //need this if we construct O+(4) within Sp(4);
    if type eq "SpO" and d eq 4 and rank eq [4] then 
        type := "O+"; 
    end if; 

    for i in [1..Limit] do
      //elements, slps, ranks on which elts act diagonally
        if spcase then
            L[i], W[i], R[i] := FindElementOp(G, range);
        else
            L[i], W[i], R[i] := FindElement(G, range); 
        end if;
        found, H, e      := InvestigatePair(G,L,R,W,sum,type);
        if found then 
            vprint SXECinv,4: "    end SmallerSXEC";
            return H, e; 
        end if;
    end for;
    error "SmallerSXEC: failed to find suitable pair"; 
end function;


/*********************************************************************/
/* Input:  initialised mtgrp G, rank, type of SX     
/* Output: subgroup of H with top left corner of type
/*         SX with dimension m in rank and lower right
/*         corner the identity. 
/*********************************************************************/
ConstructSmallerSXEC := function(P,rank, type)
    vprint SXECinv,3: "   start ConstructSmallerSXEC with rank",rank; 
    cput  := Cputime();
    d     := Degree(P);
    H,m   := SmallerSXEC(P,rank,type);
  //the following happens if we construct Omega+(d) in Sp(d)
    if m eq d then return H,m,Id(P); end if;
    CB    := MakePretty(H,m);
    H     := ApplyCOB(H,CB);
  //norm scalars to 1

  //type := H`type;

    if #BaseRing(P) gt 2 then
        H := KillFactor(H, [[1..m]], [[i] : i in [m+1..d]],type);
    end if;
    vprint SXECinv,3: "   end ConstructSmallerSXEC";
    vprint SXECcpu,2:"CPU time ConstructSmaller",H`type,
                       "(",m,") in",type,"(",d,") time:",
                       Cputime(cput);
    return H,m,CB;
end function;
    

/*********************************************************************/
/* Input:  degree d  
/* Output: list of possible degrees for reductions
/*********************************************************************/
SelectRanks := function(d, F, type)
    if  type eq "SU" and d le 12 and #F eq 4 then
        if   d eq  7  then rank:= [4]; 
        elif d eq  8  then rank:= [4]; 
        elif d eq 10 then rank:= [6]; 
        elif d eq 11 then rank:= [4,6];
        elif d eq 12 then rank:= [4,6,8]; 
        else rank:= [4];
        end if;
    elif type in ["SL","SU"] then
        if   d eq  4 then rank:= [2]; 
        elif d eq  9 then rank:= [6]; 
        elif d eq 10 then rank:= [4,6];
        elif d le 11 then rank:= [4]; 
        elif d le 13 then rank:= [6]; 
        elif d le 16 then rank:= [8]; 
        elif d eq 19 then rank:= [8]; 
        elif d le 20 then rank:= [8,10];
        elif d le 50 then
            rank:= [i:i in [(d div 3)..(2*d div 3)] | 
                    IsEven(i) and not i eq 2]; 
        else
            rank:= [i:i in [(9*d div 20)..(11*d div 20)] | 
                    IsEven(i) and not i eq 2];
        end if;
    elif type in ["O+","Sp","O-"] then
      //add odd degree for FindElement (degs of polynomial!)
        if   d eq  4 then rank:= [2]; 
        elif d eq  6 then rank:= [3,4,5];
        elif d eq  8 then rank:= [3,4,5];
        elif d le 10 then rank:= [3,4,5];
        elif d le 12 then rank:= [4,5,7,8];
        elif d le 14 then rank:= [4,5,7,8];
        elif d eq 16 then rank:= [8,12];
        elif d le 18 then rank:= [8,12];
        else
            rank := [i:i in [(d div 3)..(2*d div 3)] | 
                     ((i mod 4 eq 0) and not i eq 2) or IsOdd(i)]; 
        end if;
      //avoid reduction to OmegaMinus(10,4) and OmegaPM(14,2)
        if type eq "O-" and #F eq 4 then
            rank := [r : r in rank | not d-r eq 10];
        end if;
        if #F eq 2 and type in ["O+","Sp","O-"] then
            rank := [r : r in rank | not d-r eq 14];
        end if;
      //make sure KF works, i.e. have not O+(4,2) or Sp(4,2) 
      //as middle block in centraliser of involution;
      //don't reduce to degree 6 due to problems of finding fpf elts
        if type in ["Sp","O+","O-"] and #F eq 2 then
            rank := [r : r in rank | not r eq d-4];
            if not type eq "Sp" then 
                 rank := [r : r in rank | not d-r eq 6];
            end if;
            if rank eq [] then error "rank list is empty!"; end if;
        end if;
    end if;
    return rank;
end function;




/*********************************************************************/
/*********************************************************************/
/* 
/* IV. CONSTRUCT INVOLUTIONS
/*
/*********************************************************************/
/*********************************************************************/




/*********************************************************************/
/* Input:  matrix group G in nat. rep over field F_2 or F_4
/* Output: involution of corank d div 2 and SLP
/*********************************************************************/
RandomInvolutionSmallField := function(G : crank  := 0,
                                           BCform := false)
    d := Degree(G);
    vprint SXECinv, 2: "start random inv for small field in degree",d;   
    if crank cmpeq 0 then crank := [d div 2]; end if;
    if G`type in ["O+","O-"] and IsOdd(d div 2) then 
        crank[1] := crank[1]-1; 
    end if;
    if not assigned G`initialised then InitialiseGroup(G); end if;
    inv    := []; 
    wrd    := []; 
    repeat
        repeat 
            g,w := MyRandomWord(G); 
            o   := Order(g); 
        until o mod 2 eq 0;
        if not g^2 eq Id(G) then 
            g := g^(o div 2); 
            w := w^(o div 2); 
        end if;
        cr := Corank(g);
        if cr in crank then 
            vprint SXECinv, 2: "end random inv sml field in deg",d;
          //if G=SU then we have changed the basis; undo this!
            if not BCform cmpeq false then 
                g := g^BCform;
            end if;
            return g,w,cr; 
        end if;
    until false;
end function;


/*********************************************************************/
/* Input:  matrix groups X\leq K, index set action     
/* Output: construct an involution in the section of X identified 
/*         by action; pull this involution back to parent K of X
/*********************************************************************/
PullbackInvolution := function(K,X,action,type: ParentWord    := true, 
                                                Small         := true, 
                                                SmallerCorank := false, 
                                                Evaluation    :=true,
                                                block         := false) 
    vprint SXECinv, 3:"   start PullbackInvolution";
    d         := Degree(K); 
    F         := BaseRing(K);
    if block cmpeq false then
        AX  := ExtractGroup(X, action : type := type);
    else
        AX  := block;
    end if;

    vprint SXECinv,4:"     found this group",WhichType(AX);
    inv, winv := ConstructInvolutionEvenMain(AX, type : 
                                SmallerCorank := SmallerCorank);
     
  //SLP in UserGens(X), Evaluate(winv,UserGens(X)) has inv as block
    winv := Evaluate(winv,UserGenerators(X`SLPGroup));
    m    := Minimum(action) - 1;
    if Evaluation eq false then
       I   := Identity(MatrixAlgebra (F, d)); 
       InsertBlock (~I, inv, m+1, m+1);
       inv := Generic(K)!I;
    else 
     //this evaluation is only called in degree 4 or 5!
       inv := Evaluate(winv, UserGenerators(X)); 
    end if;
    oldw := winv;
    if ParentWord then winv := Evaluate(winv,X`UserWords); end if;
    vprint SXECinv, 3:"   end PullbackInvolution";

    return inv, winv, oldw;
end function;


/*********************************************************************/
/* Input:  matrix group G, rank, type   
/* Output: computes involution of corank rank in G
/*********************************************************************/
SmallCorankInvolution := function(G, rank, type: SmallerCorank:=false)
  //if O-, then construct smaller O+
    if type eq "O-" then
        X, m, CB := ConstructSmallerSXEC(G,rank,"O+"); 
    else
        X, m, CB := ConstructSmallerSXEC(G,rank,type);
    end if;
    inv, w   := PullbackInvolution(G,X,[1..m],X`type :
                Evaluation := false);
    return inv, w, CB, m;
 end function;


/*********************************************************************/
/* Input:  matrix group H, involution inv of corank m with 
/*         SLP w in UserGens(G)
/*         inv is block diag form with inv. in upper left corner,
/*         group H has smaller SX in upper corner
/* Output: Constructs involution of corank d div 2
/*********************************************************************/
CompleteConstruction := function (H, m, inv, w, type : smallSX := 0)
    vprint SXECinv ,3: "   start completion of cr ",m,
                       " in deg", Degree(H);
    d    := Degree(H);
    F    := BaseRing(H);
    cbi  := BaseChangeInvolution(inv);
    H    := ApplyCOB(H, cbi);
    inv  := Generic(H)! (cbi * inv * cbi^-1);
    C,Cw := MyCentraliserOfInvolution(H,inv,w,type);
    S    := MySections(C);
    vprint SXECinv,4:"      have these sections in completion",
                   [*WhichType(i): i in S*];

    h, wh, COB := FormulaElement(C, m, type);
  //C is of type [A * *; 0 B *; 0 0 A];
  //apply formula to construct A and B as SXs 
  //hence, again change the forms of A and B
    C   := ApplyCOB(C, COB);
    A,B := FormulaAB(C, m, h, wh, type);
  //Now A=[A 0 *; 0 I 0; 0 0 A] and B=[1 0 0;0 B 0; 0 0 1]
  //pull back involution from B:
  //construct inv of corank (d div 2)-m in block of dim d-2m
  //that is, the product is inv. of corank d div 2
   
    invB, winvB := PullbackInvolution(H, B, [m + 1 .. d - m], type: 
                                         Evaluation := false);

  //two involutions commute and sum of coranks is desired value 
    inv  := inv*invB;
    w    := w*winvB;
    vprint SXECinv, 3: "   end completion of cr ",m," in deg", d;
    return inv, w, COB*cbi; 
end function;


/*********************************************************************/
/* Input:  G=SL(4,F) or SU(4,F), type
/* Output: involution of corank 2 in G with SLP
/*********************************************************************/
Degree4Involution := function(K, type:  SmallerCorank := false,
                                        Limit         := 1000,
                                        BCform        := false)
    vprint SXECinv, 2: "start Degree4Involution";  
    F := BaseRing(K); 
  //use random search if field is small
    if #F le 32 then  
        return RandomInvolutionSmallField(K : BCform:=BCform);
    end if;   
  //construct SX2 as subgroup and so obtain corank 1 involution
    X, rank, COB := ConstructSmallerSXEC(K, [2], type);
    H            := ExtractGroup(X, [1..2] : type := type);
    InitialiseGroup(H : UserWords := X`UserWords);
    inv, w       := ConstructInvolutionEvenMain(H, type : 
                             SmallerCorank := SmallerCorank);  
  //this is involution in G
    w      := Evaluate(w,X`UserWords);
    inv    := COB^-1*Generic(X)!DiagonalJoin(inv,Id(GL(2,F)))*COB;
    inv    := Generic(K)!inv;
    cobinv := BaseChangeInvolution(inv);
    inv    := cobinv*inv*cobinv^-1;
    G      := ApplyCOB(K,cobinv);
    X, Xw  := MyCentraliserOfInvolution(G,inv,w,type);
 
  //need repeat loop for the following reasons:
  //1) derived group might not be complete
  //2) wa and wb below are not always the same, try different ones
    Nmr  := 0;
    inv2 := inv;
    repeat
      //construct SX2 = H as section 
      //X has many gens so use less elements in the following:
        Y    := MyDerivedSubgroupWithWords(X:NumberOfElements := 3);
        S    := MySections(Y);
        flag := exists(i){i: i in [1..#S] | Degree(S[i]) eq 2
                                            and IsType(type)(S[i])};
        if flag then 
            ugens            := UserGenerators(S[i]);
            H                := S[i];
            H`UserGenerators := ugens;
            H`type           := type;
            InitialiseGroup(H : UserWords := Y`UserWords);
            if type eq "SU" then 
                bring := Isqrt(#F);
                exp   := bring+1;
                H     := MyConjugateToStandardCopy(H,"SU");
                tmp   := GL(2,bring);
              //rewrite over GF(bring) for faster recogniseSL2
                ug    := [tmp!u : u in UserGenerators(H)];
                H     := sub<tmp|ug>;
                H`UserGenerators := ug;
                InitialiseGroup(H : UserWords := Y`UserWords);
            else
                bring := #F;
                exp   := 1;
                std   := Id(H);
            end if;
            Hc        := MakeCopyOfInitialisedGroup(H);
            gHc       := [Generic(Hc)!Hc.i : i in [1..Ngens(Hc)]];

            flag := false;
            fcnt := 1;
            while not flag or fcnt lt 4 do
               flag,_,_,map,_ := RecogniseSL2(Hc,bring);
               fcnt := fcnt + 1;
            end while;
            if not flag then error "ResSL2 failed"; end if;

          //construct a and b in same Sylow 2-subgroup of H
          //so that they commute
          //wa and wb are not always the same, hence repeat loop!
            a    := Generic(Hc) ! [1, 1, 0, 1];
            b    := Generic(Hc) ! [1, F.1^exp, 0, 1];
            wa   := map(a); 
            wb   := map(b);
            pos  := [Position(UserGenerators(H),g) : g in gHc]; 
            l    := Evaluate([wa,wb],[H`SLPGroup.i : i in pos]);
            l    := Evaluate(l, H`UserWords);
            wa   := l[1];
            wb   := l[2];
            l    := Evaluate(l, UserGenerators(G));
          //expect commutator to be a corank 2 involution 
            inv2 := (l[1], l[2]);
        end if;
        Nmr +:= 1;
    until (Nmr gt Limit) or (IsInvolution(inv2) and Corank(inv2) eq 2);
    if Nmr gt Limit then error "Deg4Inv: Found no involution"; end if;   
    inv2 := cobinv^-1*inv2*cobinv;
    winv := (wa, wb);
  //if G=SU then we might have done a base change - undo now!
    if not BCform cmpeq false then inv2 := inv2^BCform; end if;
    vprint SXECinv, 2: "end Degree4Involution";
    return inv2, winv;
end function;


/*********************************************************************/
/* Input:  matrix group G in nat rep of odd degree d, type   
/* Output: involution of corank d div 2 with SLP
/*         computed in SX(d-1)
/* Remark: called only in deg 3,5,7
/*********************************************************************/
OddDegreeInvolution := function(G, type: SmallerCorank := false,
                                         BCform        := false)
    vprint SXECinv, 2: "start odd degree inv with deg",Degree(G);
    F          := BaseRing (G); 
    d          := Degree(G);
    X,rank,COB := ConstructSmallerSXEC(G, [d-1], type);
    W          := X`UserWords;
    H          := ExtractGroup(X, [1..d-1]:type := type);
    InitialiseGroup(H : UserWords := X`UserWords);
    inv, w     := ConstructInvolutionEvenMain(H,type: 
                         SmallerCorank:=SmallerCorank); 
    w          := Evaluate(w,X`UserWords);
    inv        := COB^-1*DiagonalJoin(inv,Id(GL(1,F)))*COB;
    inv        := Generic(G)!inv;
    if not BCform cmpeq false then inv := inv^BCform; end if;
    vprint SXECinv, 2: "end odd degree involution";
    return inv, w;
end function;



/*********************************************************************/
/* Input:  matrix group G in nat rep, type (not O-) 
/* Output: involution inv of corank d div 2 with SLP
/*         (and a base change matrix CB)
/* Options: SmallerCorank: constructs inv of corank less than d/2
/*                         then CB*inv*CB^-1 has type [inv 0;0I]
/*********************************************************************/
ConstructInvolutionEvenMain := function(G,type : SmallerCorank:=false)
    if not assigned G`initialised then InitialiseGroup(G); end if;
    d  := Degree(G);
    vprint SXECinv, 1: "start inv in ",G`type,"(",d,")";
    F  := BaseRing(G);
  //for small fields / degrees use random search
  //NOT for Sp, O+, O- because we need good involutions!
    if (type eq "SL" and 
             ((#F eq 2 and d in [1..14]) or 
              (#F eq 4 and d in [1..8])))       or
       (type eq "SU" and 
             ((#F eq   4 and d le 15) or
              (#F eq  16 and d le 9)  or
              (#F eq  64 and d le 6)  or
              (#F in {256,1024,4096} and d in [1,2,3])))  then       
        if not SmallerCorank or d in [1..4] then
            inv,w := RandomInvolutionSmallField(G);
        else
            cr    := [(d div 3)..(2*d div 3)];
            inv,w := RandomInvolutionSmallField(G:crank:=cr);
        end if;
        vprint SXECinv, 1: "end inv in ",G`type,"(",d,")";
        return inv,w;
    end if;

  //for small degrees (base cases) use specialised functions
  //e.g. for 5 and 7 reduce to 4 and 6   
    if d in {2,3,4,5,7} or (d eq 6 and type in ["Sp","O+","SpO"]) 
         or (d in [8,10,12] and #F eq 2 and type in ["Sp","O+","SpO"]) 
         or (d in [14] and #F eq 2 and G`type in ["O+"]) then

        cputime := Cputime();

      //For large fields this is better than RecogniseSp4Even
        if d eq 4 and G`type eq "Sp" and #F ge 2^10 then 
          //comp tree for Sp(4) is slow, but fast for Omega+(4)
          //hence construct smaller Omega+ in Sp(4)!
            X, m, CB     := ConstructSmallerSXEC(G,[4],"O+");
            inv, w, wold := PullbackInvolution(G,X,[1..m],"O+" : 
                                               Evaluation:=false);
            inv          := CB^-1*inv*CB;
            vprint SXECinv, 1: "end inv in ",G`type,"(",d,")";
            vprint SXECcpu, 2: 
                         "CPUtime base case red from Sp4 to O+4:",
                         Cputime(cputime);
            return inv, w, Id(G);
        end if;
        if (d eq 6 and not #F eq 2) or (d eq 10 and #F eq 2) then 
          //construct inv of corank 2 /4 in smaller Omega+
            X, m, CB     := ConstructSmallerSXEC(G,[d-2],type);
            inv, w, wold := PullbackInvolution(G,X,[1..m],X`type : 
                                               Evaluation:=false);
            inv          := CB^-1*inv*CB;
            vprint SXECinv, 1:  "end inv in ",G`type,"(",d,")";
            vprint SXECcpu,2: "CPU time base case red from deg",d,
                                "to deg",d-4,":",Cputime(cputime);
            return inv, w, Id(G);
        end if;

      //keep copy of input group
        cG := MakeCopyOfInitialisedGroup(G);
      //conjugate SU,Sp,O+ to standard copy
        if not type eq "SL" then
            H, BCform, toStd := MyConjugateToStandardCopy(G,type);
            H`UserWords      := G`UserWords;
            H`COB            := G`COB;
            H`type           := G`type;
            G                := H;

        else
            toStd            := Id(G);
            BCform           := false;
        end if;  

      //write SU(2,-) as SL(2,-)
        if type eq "SU" and d eq 2 then
            P     := GL(2,Isqrt(#F));
            ugs   := [P!u: u in UserGenerators(G)];
            G     := sub<P|ugs>;
            G`UserGenerators := ugs; 
            toStd :=Generic(G)!toStd;
            InitialiseGroup(G : type := "SU");
        end if; 

      //for fast "Position"  
        ug := [Generic(G)!u : u in UserGenerators(G)]; 

      //copy for Recognise functions
        H  := MakeCopyOfInitialisedGroup(G);

      //define involution for Recognise functions
        if   d eq 2 then inv := Generic(H)![1,1,0,1]^toStd; 
        elif d eq 3 then inv := Generic(H)![1,0,1,0,1,0,0,0,1]^toStd; 
        elif d eq 4 then 
            inv := Generic(H)![1,0,1,0,0,1,0,1,0,0,1,0,0,0,0,1]^toStd;
        elif d eq 5 then 
            inv := Generic(H)![1,0,0,1,0,0,1,0,0,1,0,0,
                               1,0,0,0,0,0,1,0,0,0,0,0,1]^toStd;
        end if;
       
      //define "good" involutions for Sp, O+
        if G`type in ["Sp","O+"]  then
            if d eq 4 then
                inv := Generic(H)![1,0,1,0,0,1,0,0,0,0,1,0,0,1,0,1];
            elif d eq 6 then
                inv := Generic(H)!
                       [1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,
                        0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,1,0,0];
            elif d eq 8 then
                inv := Generic(H)!
                       [0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,
                        0,1,0,0,0,0,1,0,1,0,0,0,1,0,0,0,0,
                        1,0,0,0,0,0,0,1,0,1,0,1,1,0,1,0,1,0,0,0,
                        0,1,0,0,0,0,0,0 ];

            end if;
        end if;

        if G`type in ["Sp","O+"] then
            if #F eq 2 and d eq 12 then
                inv :=Generic(H)!
                      [ 1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0,
                        0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,
                        0,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0,
                        0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,
                        0,0,0,1,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,
                        0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,
                        0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,1,0,1 ];
            elif #F eq 2 and d eq 10 then
                inv := Generic(G)!
                       [ 1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,
                         0,1,0,1,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,
                         0,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,
                         0,0,0,1,0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,0,
                         0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,1 ];
            elif #F eq 2 and d eq 14 then
                inv := Generic(G)!
                       [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,
                        0,0,1,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,
                        0,0,0,1,0,1,1,0,0,0,0,1,1,0,1,0,1,0,1,0,0,
                        0,1,0,1,1,1,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,
                        0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,
                        1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,
                        0,0,0,0,0,1,0,0,0,1,0,0,0,0,1,0,1,0,0,1,0,
                        0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,
                        0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,1,0,0,1,0,
                        0,0,0,0,0,0,1 ];
            end if;       
        end if;

      //now call specialised functions
        if  G`type eq "SU"  then
            if  d in [5,7] then
                g,w := OddDegreeInvolution(H,type:BCform:=BCform);
                vprint SXECinv, 1: "end inv in ",G`type,"(",d,")";
                vprint SXECcpu, 2: "CPU time inv base case",
                                  G`type,"(",d,")",Cputime(cputime);
                return g,w;
            elif d eq 4 then 
                g,w := Degree4Involution(H,type:BCform:=BCform);
                vprint SXECinv, 1: "end inv in ",G`type,"(",d,")";
                vprint SXECcpu, 2: "CPU time inv base case",
                                 G`type,"(",d,")",Cputime(cputime);
                return g,w; 
            elif d eq 3 then 
                vprint SXECinv, 2: "start recogniseSU",d;

                flag := false;                                                                                                     fcnt := 1;   
                while not flag or fcnt lt 4 do                                                                                        flag,_,_,m1,m2 := RecogniseSU3(H,Isqrt(#F));
                   fcnt := fcnt + 1;                                                                
                end while;                                                                                                         if not flag then error "RecogniseSU3 failed"; end if;

            elif d eq 2 then
                vprint SXECinv, 2: "start recogniseSU",d;
              //note: H is written as SL2

              flag := false; 
              fcnt := 1;    
              while not flag or fcnt lt 4 do
                 flag,_,_,m1,m2 := RecogniseSL2(H,#BaseRing(H));      
                 fcnt := fcnt + 1;    
              end while;    
              if not flag then error "RecogniseSL2 failed"; end if;

              //  _,_,_,m1,m2  := RecogniseSL2(H, #BaseRing(H));

            end if;
            vprint SXECinv, 2: "end recogniseSU",d;
            w    := m1(inv);
            pos  := [Position(ug,H.i) : i in [1..Ngens(H)]];
        elif G`type eq "SL" then
            if  d in {3,5,7} then 
                g,w := OddDegreeInvolution(H,type);
                vprint SXECinv, 1: "end inv in ",G`type,"(",d,")";
                vprint SXECcpu, 2: "CPU time inv base case",
                                  G`type,"(",d,")",Cputime(cputime);
                return g,w;
            elif d eq 4 then  
                g,w := Degree4Involution(H,type);
                vprint SXECinv, 1: "end inv in ",G`type,"(",d,")";
                vprint SXECcpu, 2: "CPU time inv base case",
                                  G`type,"(",d,")",Cputime(cputime);
                return g,w; 
            elif d eq 2 then 
                vprint SXECinv, 2: "start recogniseSL2",d;


                flag := false; 
                fcnt := 1;    
                 while not flag or fcnt lt 4 do
                    flag,_,_,m1,m2 := RecogniseSL2(H,#F);      
                    fcnt := fcnt + 1;    
                 end while;    
                 if not flag then error "recogniseSL2 failed"; end if;

              //_,_,_,m1,m2  := RecogniseSL2(H, #F);
                vprint SXECinv, 2: "end recogniseSL2",d;
            end if;
            w    := m1(inv);
            pos  := [Position(ug,H.i) : i in [1..Ngens(H)]];
          
        elif G`type eq "Sp" and d eq 4 then 
            vprint SXECinv, 2: "start recogniseSp4",d;

             flag := false; 
             fcnt := 1;    
             while not flag or fcnt lt 4 do
              flag,_,_,m1,m2 := RecogniseSp4(H,#F);      
                // flag,_,_,m1,m2 := ClassicalConstructiveRecognition(H,"Sp",4,#F);
                fcnt := fcnt + 1;    
             end while;    
          
          //f,_,_,m1,m2  := RecogniseSp4Even(H, #F);
            if not flag then 
                H:Magma;
                error "RecogniseSp4 was not successful"; 
            end if;
            vprint SXECinv, 2: "end recogniseSp4",d;
            w    := m1(inv);
            pos  := [Position(ug,H.i) : i in [1..Ngens(H)]];
        elif G`type in ["Sp","O+","SpO"] then
            vprint SXECstdgens, 3: "      start COMP TREE for",type,d;
            prior := [i : i in [19 .. 1 by -1]];
            for i in [16..18] do prior[i] := 0; end for; 
          //T   := CompositionTree(H : Priorities := prior); 
          //"test new CT 1";
          //T   := CompositionTree(H : Priorities := prior, LeafPriorities := [1,2,3,4,5]);
          //"new CT 1";
            T   := CompositionTree(H : Priorities := prior, LeafPriorities := [5,4,3,2,1]);
            flg, w := CompositionTreeElementToWord(H,inv);
            if not flg then
                "flag fault!";
                "this is inv",inv;
                "this is group",type,d,H:Magma;
                OrthogonalForm(H);
                QuadraticForm(H);
                 error "ups";
            end if;
            map := CompositionTreeNiceToUser(H);
            w   := Image(map,w);
            pos := [Position(ug,H.i) : i in [1..Ngens(H)]]; 
            vprint SXECstdgens, 3: "      end COMP TREE for",type,d;
        end if;
        w  := Evaluate(w,[G`SLPGroup.i : i in pos]);
        cb := Id(cG);

        if not BCform cmpeq false then 
            inv := Generic(cG)!inv;
            inv := BCform^-1*inv*BCform;
        end if;
        vprint SXECinv, 1: "end inv in ",G`type,"(",d,")";
        vprint SXECcpu, 2: "CPU time inv base case",G`type,
                         "(",d,"):",Cputime(cputime);
        return inv,w; 
    end if;

  //otherwise use recursion
  //now inv is [i 0; 0 1]
    ranks           := SelectRanks(d,F, type);
    inv, w, CB, mSX := SmallCorankInvolution(G, ranks, type);

  //inv is block diag form with involultion in left upper corner
  //ApplyCOB(G,CB) has SX in upper left corner.
    if SmallerCorank eq false then
        H          := ApplyCOB(G,CB);
      //now inv is [I 0 I; 0 J 0; 0 0 I] with J involution
        cr         := Corank(inv);
        inv, w, cb := CompleteConstruction(H,cr,inv,w, H`type:
                                           smallSX   := mSX);
    else cb := Identity(G); end if;
 
    CB  := cb*CB;
    inv := CB^-1*inv*CB;
    inv := Generic(G)!inv;

    vprint SXECinv, 1: "end inv in ",G`type,
                       "(",d,"), corank",Corank(inv);
    return inv, w, CB;  
end function;


/*********************************************************************/
/* Input:  initialised matrix group G
/* Output: involution of small corank, SLP
/*********************************************************************/
FindAnyInvolution := function(G)    
    d := Degree(G);
    F := BaseRing(G);
    t := G`type;
    if #F le 64  or
       (#F eq 128 and d le 100)  then 
        return RandomInvolutionSmallField(G : crank := [1..d-1]);
    end if;
    if d eq 3 and t eq "SU" and #F le 4096 then
       return RandomInvolutionSmallField(G : crank := [1..d-1]);
    end if;
    if (t eq "O-" and d eq 4)  then 
        a,b,c := StandardGeneratorsSXEven(G,"O-"); // changed!
        g     := c^-1*a[1]*c;
        w     := b[1];
        return g,w;
    end if;
  //construct smaller copy of SX and recurse
    if (#F ge 4 and d ge 7) or (#F eq 2 and d ge 10)  then
        if t in ["SL","SU"] then
            if t eq "SU" then 
                rank := [2,4,5] cat [8..(d div 2)+2];
            else
                rank := [2..(d div 2)+2];
            end if;
            H, m := ConstructSmallerSXEC(G,rank,t);
        else
            rank := [ i : i in [4..((d div 2)+1)] | not i eq 8];
            H, m := ConstructSmallerSXEC(G,rank,"SpO");
        end if;
        K   := ExtractGroup(H, [1..m] : type := H`type);
        g,w := $$(K);
        w   := Evaluate(w,H`UserWords);
        g   := DiagonalJoin(g,Id(GL(d-m,BaseRing(G))));
        g   := H`COB^-1*g*H`COB;
        return g,w;
    else
        g, w := ConstructInvolutionEvenMain(G,G`type : 
                                            SmallerCorank := true);
        return g, w;
    end if;
end function;


/*********************************************************************/
/* Input:  classical group SL,SU,Sp,OmegaPlus or OmegaMinus 
/*         in nat. rep., even characteristic;
/*         O+ and O- must have even degree at most 4 and
/*         base field with at least 4 elements. 
/* Output: involution of "large" corank, SLP, corank
/* Op.Par: type:        type of input group
/*         smallCorank: construct inv of small corank
/*********************************************************************/

intrinsic InvolutionClassicalGroupEven (G :: GrpMat[FldFin]: Case := false,
SmallCorank := false) -> GrpMatElt, GrpSLPElt, RngIntElt
{ G is quasisimple classical group in natural representation, even characteristic;
  if G is of type Omega+ and Omega- then it must have even degree
   at least 4 and be defined over a field with at least 4 elements;
   corank (g) = rank (g - Identity (G));
   returns involution of "large" corank, corresponding SLP for
   involution in WordGroup (G), and the corank of the involution;
   Case:       "SL", "Sp", "SU", "Omega-", "Omega+";
   SmallCorank: accept involution of small corank
}
    F := BaseRing(G);
    if IsOdd(#F) then error "Even characteristic only"; end if;

    // reset various parameter values to accord with early decisions 
    smallCorank := SmallCorank;
    type := Case;
    if type cmpeq "Omega+" then type := "O+"; end if;
    if type cmpeq "Omega-" then type := "O-"; end if;

    if not type cmpeq false and 
       not type in ["SL","SU","Sp","O+","O-"] then
             error "illegal type";
    end if;
    if Degree(G) eq 1 then 
        error "Degree of input group must be at least 2."; 
    end if;
    if not (type cmpeq false) then G`type := type; end if;
    if type cmpeq false and not assigned G`type then
        type := WhichType(G);
        if type cmpeq false then
            error "could not determine type of group";
        end if;
        G`type := type;
    end if;
    InitialiseGroup(G: type := G`type);

  //construct involution of large corank
    d    := Degree(G);
    type := G`type;
    if type in ["O+","O-"] then
        if not IsEven(d) or d eq 2 then
            error "Omega+ and Omega- must have even degree >2.";
        end if;
    end if;

    if type eq "O-" and d le 14 and #F eq 2 then
        inv, w := FindAnyInvolution(G);
        done   := true;
    else
      //do not need large corank
        if smallCorank then
            inv, w := FindAnyInvolution(G);
            return inv, w, Corank(inv);
        end if;
    
        if type eq "O-" then
            if d eq 4 or (d eq 6 and #F in [4]) then
                a,b,c := StandardGeneratorsSXEven(G,"O-"); 
                inv   := c^-1*a[1]*c;
                w     := b[1];
            else
              //construct O+(4) within O-(6) and recurse
                ranks := [d div 2 .. d-2];
                H,m   := ConstructSmallerSXEC(G,ranks,"O+");
                inv,w := PullbackInvolution(G, H, [1..m], H`type:
                                            Evaluation := false);
                inv   := H`COB^-1*inv*H`COB;
                inv   := Generic(H)!inv;
            end if; 
        else
            inv, w := ConstructInvolutionEvenMain(G, type);
        end if;
    end if;
    return inv, w, Corank(inv);
end intrinsic;
// end function;


/*********************************************************************/
/* 
/* V. FIND TWO SX
/*
/*********************************************************************/



/*********************************************************************/
/* Input:   G, A, B, m as output of TwoSXEC
/* Output:  adjusts forms of A and B in G (everything has std form)
/*********************************************************************/
AdjustFormsOfTwoSXEC := function(K,H,B,m)
    F := BaseRing(K);
    d := Degree(K);
    StandardFormOp := function(n)
        J := MatrixAlgebra(F,2)![0,1,0,0];
        f := DiagonalJoin ([J: i in [1..(n div 2)]]);
        return f;
    end function;
    StandardFormAlt := function(n)
        J := MatrixAlgebra(F,2)![0,1,1,0];
        f := DiagonalJoin ([J: i in [1..(n div 2)]]);
        if IsOdd(n) then 
            f:=DiagonalJoin(f,Id(MatrixAlgebra(F,1))); 
        end if;
        return f;
    end function;
    StandardFormOm := function(n)
        q      := #F;
        A      := MatrixAlgebra(F,2);
        J      := A![0,1,0,0];
        m      := (n div 2) - 1;
        form   := DiagonalJoin([J : i in [1..m]]);
        gam    := GF(q^2).1;
        I      := A![1,gam+gam^q,0,gam^(q+1)];
        form   := DiagonalJoin(form,I);
        return form;
    end function;
  //StandardFormOm := function(n)
  //    tmp := OmegaMinus(n,F);
  //    InitialiseGroup(tmp);
  //    _,f := QuadraticForm(MyConjugateToStandardCopy(tmp,"O-"));
  //    return f;
  //end function;

    if K`type eq "O+" then
        _,form := QuadraticForm(ApplyCOB(K,H`COB));
        formH  := ExtractBlock(form,1,1,m,m);
        formB  := ExtractBlock(form,m+1,m+1,d-m,d-m);   
        stdH   := StandardFormOp(m);
        stdB   := StandardFormOp(d-m);
        typeH  :="orthogonalplus";
        typeB  := "orthogonalplus";  
    elif K`type eq "O-" then
        _,form := QuadraticForm(ApplyCOB(K,H`COB));
        formH  := ExtractBlock(form,1,1,m,m);
        formB  := ExtractBlock(form,m+1,m+1,d-m,d-m);
        stdH   := StandardFormOp(m);
        stdB   := StandardFormOm(d-m); 
        typeH  := "orthogonalplus";
        typeB  := "orthogonalminus";
    elif K`type eq "SU" then
        _,form := UnitaryForm(ApplyCOB(K,H`COB));
        formH  := ExtractBlock(form,1,1,m,m);
        formB  := ExtractBlock(form,m+1,m+1,d-m,d-m); 
        stdH   := StandardFormAlt(m);
        stdB   := StandardFormAlt(d-m); 
        typeH  := "unitary";
        typeB  := "unitary";
    elif K`type eq "Sp" then
        _,form := SymplecticForm(ApplyCOB(K,H`COB));
        formH  := ExtractBlock(form,1,1,m,m);
        formB  := ExtractBlock(form,m+1,m+1,d-m,d-m); 
        stdH   := StandardFormAlt(m);
        stdB   := StandardFormAlt(d-m);
        typeH  := "symplectic";
        typeB  := "symplectic";
    end if; 
    if formH eq stdH then
        cbH := formH^0;
    else
        xH     := TransformForm(formH, typeH)^-1;
        yH     := TransformForm(stdH,  typeH);
        cbH    := yH*xH;
    end if;
    if formB eq stdB  then
        cbB := formB^0;
    else
        xB     := TransformForm(formB, typeB)^-1;
        yB     := TransformForm(stdB,  typeB);
        cbB    := yB*xB;
    end if;
    cb := DiagonalJoin(cbH,cbB);
    H  := ApplyCOB(H,cb);
    B  := ApplyCOB(B,cb);
    return B,H,cb;
end function;


/*********************************************************************/
/* Input:   matrix group K with subgroup H (w.r.t. H`COB)
/*          H top block SX, g\in H inv of large crank, slp 
/*          block of H has degree m 
/*          wold is SLP of g in H, w is SLP of g in K
/*          m degree of block of H
/* Output:  subgroups SX(m) and SX(d-m), stdgens in one copy
/* Comment: This is an internal helping function for
/*          StandardGeneratorsSXEven       
/*********************************************************************/
TwoSXEC := function(K,H,g,wold,w,m,type)
    cput := Cputime();
    d    := Degree(K);
    F    := BaseRing(K);
    vprint SXECstdgens,2: "   start TwoSXEC in degree", d;

    G            := ApplyCOB(K,H`COB);
    r            := m div 2;

  //Construct centraliser of g in G, it contains SX(d-m);
  //make cob such that C^scob has upper block diagonal form
    C, Cw        := MyCentraliserOfInvolution(G,g,w,type);

    scob := DiagonalJoin(Identity(GL(r,F)),ZeroMatrix(F,d-r,d-r));  
    InsertBlock(~scob,Identity(GL(d-m,F)),r+1,m+1); 
    InsertBlock(~scob,Identity(GL(r,F)),d-r+1,r+1); 
  //now C = [* * *; 0 * *; 0 0 *]
    C    := ApplyCOB(C,scob);   
 
  //construct  CH = [* 0 *;0 I 0; 0 0 *]
  //This call of MyCentraliserOfInvolution is a bottleneck
  //for GF(2) and GF(4) (due to the check); hence, reduce to
  //smaller copy of H, which improves runtime
    if #F in [2,4,8] then
        Hex      := ExtractGroup(H,[1..m]: type := H`type);
        gex      := ExtractBlockNEW(g,[1..m]);
        CHex,CHw := MyCentraliserOfInvolution(Hex,gex,wold,type); 
        id       := Id(GL(d-m,F));
        newgens  := [DiagonalJoin(u,id):u in UserGenerators(CHex)];
        newcob   := DiagonalJoin(CHex`COB,id);
        CH       := sub<Generic(H)|newgens>;
        CH`UserGenerators := newgens;
        InitialiseGroup(CH : UserWords := CHw, type := "no");
        CH`COB   := newcob;
        CH      := ApplyCOB(CH,scob);
    else
        CH, CHw := MyCentraliserOfInvolution(H,g,wold,type);
        CH      := ApplyCOB(CH,scob);
    end if;
 
  //find element a=[* 0 *;0 I 0;0 0 *] for formula
    nr := 0;
    if #F in [2,4,8] then lmt := 1000; else lmt := 100; end if;
    repeat
        a,aw := MyRandomWord(CH);
        bla  := ExtractBlockNEW(a,[1..r]);
        nr  +:= 1;
        if nr gt lmt then 
            error "TwoSXEC: Problems finding formula element";
        end if;
    until not PrimeOrderElement(bla,2) 
          and not 1 in {x[1] : x in Eigenvalues(bla)};
    a  := a^2;
    aw := aw^2;
    aw := Evaluate(aw,CH`UserWords);
    aw := Evaluate(aw,H`UserWords);
   
  //now B is [1 * * // 0 B * // 0 0 1]
  //use options "Squares" so that [u^2 : u in ugens] is gen set
    B      := KillFactor(C,[[r + 1..d - r]],[[1..r],[d - r + 1..d]],
                         type : Squares := true); 
    typB   := B`type;
    if typB cmpeq false then
        RecogniseClassical(ExtractGroup(B,[r+1..d-r]));
        error "KF in TwoSX: type not detected deg",d-2*r;
    end if;
    U      := UserGenerators(B);   
    oa     := Order(a);
    gensB  := [Formula(a, U[i],oa)^2: i in [1..#U]];
    W      := B`UserWords;
    W      := [Formula(aw, W[i], oa)^2: i in [1..#W]];
  //square to obtain form [1 0 0 // 0 B 0 // 0 0 1]
    B      := sub<Generic(C) | gensB>;
    B`UserGenerators := gensB;
    InitialiseGroup(B : UserWords := W, type := typB);
    B      := ApplyCOB(B,scob^-1);
    B`COB  := H`COB; 
    vprint SXECstdgens,2: "   end TwoSXEC in degree", d, 
                      "found degs",m,d-m;
    
    vprint SXECcpu,1:"CPU time splitting",K`type,"(",d,") into",
           H`type,"(",m,") and",B`type,"(",d-m,"):", Cputime(cput);
    return H,B;
end function;


/*********************************************************************/
/* Special TwoSX function of SolveSp6
/*********************************************************************/
TwoSXECSp6 := function(K)
    cput := Cputime();
    F    := BaseRing(K);
  //Find SmallSXwithInvolution 
    rank       := SelectRanks(6,BaseRing(K),K`type);
    H, m, CB   := ConstructSmallerSXEC(K,rank,"Sp");
    g, w, wold := PullbackInvolution(K,H,[1..m],H`type : 
                                     Evaluation:=false);
    cb         := Generic(K)!DiagonalJoin(
                      BaseChangeInvolution(ExtractBlockNEW(g,[1..m])),
                      Id(GL(6-m,BaseRing(K))));
    g          := Generic(K)!cb*g*cb^-1;
    H          := ApplyCOB(H,cb);
    G          := ApplyCOB(K,H`COB);
    r          := m div 2;
    C, Cw      := MyCentraliserOfInvolution(G,g,w,"Sp");
    scob       := DiagonalJoin(Identity(GL(r,F)),
                               ZeroMatrix(F,6-r,6-r));  
    InsertBlock(~scob,Identity(GL(6-m,F)),r+1,m+1); 
    InsertBlock(~scob,Identity(GL(r,F)),6-r+1,r+1); 
    C          := ApplyCOB(C,scob);   
    CH, CHw := MyCentraliserOfInvolution(H,g,wold,"Sp");
    CH      := ApplyCOB(CH,scob);
     
  //find element a=[* 0 *;0 I 0;0 0 *] for formula
    nr := 0;
    if #F in [2,4,8] then lmt := 1000; else lmt := 100; end if;
    repeat
        a,aw := MyRandomWord(CH);
        bla  := ExtractBlockNEW(a,[1..r]);
        nr  +:= 1;
        if nr gt lmt then error "TwoSXECSp6: formula elt"; end if;
    until not PrimeOrderElement(bla,2) 
          and not 1 in {x[1] : x in Eigenvalues(bla)};
    a  := a^2;
    aw := aw^2;
    aw := Evaluate(aw,CH`UserWords);
    aw := Evaluate(aw,H`UserWords);
   
  //now B is [1 * * // 0 B * // 0 0 1]
  //use options "Squares" so that [u^2 : u in ugens] is gen set
    B      := KillFactor(C,[[r + 1..6 - r]],[[1..r],[6 - r + 1..6]],
                        "Sp" : Squares := true); 
    typB   := B`type;
    U      := UserGenerators(B);   
    oa     := Order(a);
    gensB  := [Formula(a, U[i],oa)^2: i in [1..#U]];
    W      := B`UserWords;
    W      := [Formula(aw, W[i], oa)^2: i in [1..#W]];
  //square to obtain form [1 0 0 // 0 B 0 // 0 0 1]
    B      := sub<Generic(C) | gensB>;
    B`UserGenerators := gensB;
    InitialiseGroup(B : UserWords := W, type := typB);
    B      := ApplyCOB(B,scob^-1);
    B`COB  := H`COB; 
    vprint SXECstdgens,2: "   end TwoSXEC deg 6, found degs",m,6-m;
    
  //constructed O+ and Sp; switch to have Sp and O+
    idm  := Id(GL(m,F));
    idmd := Id(GL(6-m,F));
    cbSp := Zero(MatrixAlgebra(F,6));
    InsertBlock(~cbSp,idm,6-m+1,1);
    InsertBlock(~cbSp,idmd,1,m+1);
    cbSp := GL(6,F)!cbSp;
    H    := ApplyCOB(H,cbSp);
    B    := ApplyCOB(B,cbSp); 
    m    := 6-m;
    tmp  := MakeCopyOfInitialisedGroup(B);
    B    := MakeCopyOfInitialisedGroup(H);
    H    := MakeCopyOfInitialisedGroup(tmp);
    if not K`type eq "SL" then
        B, H := AdjustFormsOfTwoSXEC(K,H,B,m);
    end if;
    vprint SXECcpu,1:"CPU time splitting",K`type,"(",6,") into",
           H`type,"(",m,") and",B`type,"(",6-m,"):", Cputime(cput);
    return H,B,m;
end function;




/*********************************************************************/
/*********************************************************************/
/* 
/* VI. PRELIMINARIES FOR CONSTRUCTING STANDARD GENERATORS
/*
/*********************************************************************/
/*********************************************************************/



/*********************************************************************/
/* Input:   finite field F of char 2, degree d, type
/* Output:  modified stdgens which are to construct as SLPs
/*********************************************************************/
StandardGeneratorElements := function(F,d,type);
  //construct all non-cycle generators for SL and SU
    if type eq "SL" then 
        elt := [GL(2,F)!v : v in [[0,1,1,0],[1,1,0,1],[F.1,0,0,F.1^-1],
                             [1,0,0,1],[1,0,0,1],[1,0,0,1],[1,0,0,1]]];
        if d-2 gt 0 then 
            low   := Identity(GL(d-2,F));
            elt   := [GL(d,F)!DiagonalJoin(v,low) : v in elt];
            if d ge 4 then
                x     := GL(4,F)![0,1,0,0,0,0,1,0,0,0,0,1,1,0,0,0];
                if d-4 gt 0 then
                    low := Identity(GL(d-4,F));
                    x   := GL(d,F)!DiagonalJoin(x,low);
                end if;
                elt[6] := x;
            end if;
        end if;

    elif type eq "SU" then      
        gam := PrimitiveElement(F);
        q   := Isqrt(#F);
        phi := Trace(gam, GF(q))^(-1)*gam;
        elt := [GL(2,F)!v:v in [[0,1,1,0],[1,1,0,1],
                          [gam^(q+1),0,0,gam^-(q+1)],
                          [1,0,0,1],[1,0,0,1],[1,0,0,1],[1,0,0,1]]];

        if d-2 gt 0 then 
            low   := Identity(GL(d-2,F));
            elt   := [GL(d,F)!DiagonalJoin(v,low) : v in elt];
            if d ge 4 then
                u     := GL(4,F)![0,0,1,0, 0,0,0,1, 1,0,0,0, 0,1,0,0];
                if d-4 gt 0 then
                    low := Identity(GL(d-4,F));
                    u   := GL(d,F)!DiagonalJoin(u,low);
                end if;
                elt[4] := u;
            end if;
        end if;

      //fix SU(3,2)
        if type eq "SU" and d eq 3 and #F eq 4 then
            elt[2] := GL(3,4)![1,gam,gam, 0,1,0, 0,gam^2,1];
        end if;

      //construct x and y for even/odd degree SL and SU
        x := Id(GL(d,F));
        y := Id(GL(d,F));
        if IsEven(d) then
            if d ge 4 then
                InsertBlock(~x,GL(4,F)![1,0,1,0,0,1,0,0,
                                        0,0,1,0,0,1,0,1],1,1);
                InsertBlock(~y, 
                GL(4,F)![gam,0,0,0,0,gam^-q,0,0,0,0,gam^-1,
                         0,0,0,0,gam^q],1,1);
            end if;
        else
          //put everything to bottom 3x3 block
            MA := MatrixAlgebra(F,d);
            x           := MA!x;      y           := MA!y;
            x[d-2][d]   := One(F);    y[d-1][d-1] := gam^-q;
            x[d][d-1]   := One(F);    y[d-2][d-2] := gam;
            x[d-2][d-1] := phi;       y[d][d]     := gam^(q-1); 
        end if;  
        elt[6] := GL(d,F)!x;
        elt[7] := GL(d,F)!y;
    end if;
 
  //now construct cycle for SL and SU
    if type eq "SL" and d gt 2 then
        if IsEven(d)  then
            id2 := Identity(GL(2,F));
            bl  := Identity(GL(d-2,F));
            v   := Identity(MatrixAlgebra(F,d));
            InsertBlock(~v,bl,1,3);
            InsertBlock(~v,id2,d-1,1);
            for i in [1..d] do v[i][i] := Zero(F)*v[i][i]; end for;
            v      := GL(d,F)!v;
            elt[5] := v;
        else
            if d gt 3 then
                bl  := Identity(GL(d-3,F));
                v   := Identity(MatrixAlgebra(F,d));
                InsertBlock(~v,bl,1,3);
                for i in [1..d] do v[i][i] := Zero(F)*v[i][i]; end for;
                v[d-2][1] := One(F); v[d-1][d] := One(F);
                v[d][2]   := One(F); v         := GL(d,F)!v;
                elt[5]    := v;
            else
                v      := GL(d,F)![1,0,0,0,0,1,0,1,0];
                elt[5] := v;
            end if;
        end if;
    elif type eq "SU" and d ge 4 then
         id2 := Identity(GL(2,F));
         if IsOdd(d) then l := d-1; else l := d; end if;
         bl  := Identity(GL(l-2,F));
         v   := Identity(MatrixAlgebra(F,d));
         InsertBlock(~v,bl,1,3);
         InsertBlock(~v,id2,l-1,1);
         for i in [1..l] do v[i][i] := Zero(F)*v[i][i]; end for;
         v      := GL(d,F)!v;
         elt[5] := v;
    end if;
  
  //standard gens for Sp
    if type eq "Sp" then
        w       := PrimitiveElement(F);
        M       := MatrixAlgebra(F, d);
        a       := Identity(M);
        a[1][1] := 0;
        a[1][2] := 1;
        a[2][1] := 1;
        a[2][2] := 0;
        t       := Identity (M);
        t[1][2] := 1;
        delta   := Identity (M);
        delta[1][1] := w;
        delta[2][2] := w^-1;
        if d ge 4 then 
            p := Zero (M);
            p[1][3] := 1; p[2][4] := 1; p[3][1] := 1; p[4][2] := 1;
            for i in [5..d] do p[i][i] := 1; end for;
        else
            p := Identity (M);
        end if;
        if d ge 4 then 
            b := Zero (M);
            n := d div 2;
            for i in [1..d - 3 by 2] do
                b[i][i + 2] := 1;
            end for; 
            b[d - 1][1] := 1;
            for i in [2..d - 2 by 2] do
                b[i][i + 2] := 1;
            end for; 
            b[d][2] := 1;
        else 
            b := Identity (M);
        end if;
        P := GL(d, F);
        a := P!a; b := P!b; p := P!p; t := P!t; delta := P!delta;
        M := MatrixAlgebra (F, 4);
        I := Identity (M);
        I[2][3] := 1;
        I[4][1] := 1;
        I := GL (4, F)!I;
        if d gt 4 then 
            I := P!(DiagonalJoin(I, Identity(MatrixAlgebra(F,d-4))));
        elif d le 3 then 
            I := Identity(P);
        end if;
        elt := [a, t, delta, p, b, I, Id(P),a*a^p];
    end if;

  //Standard gens for OmegaPlus   
    if type eq "O+" then
        q := #F;
        w := PrimitiveElement (F);
        A := MatrixAlgebra (F, 2);
        if d eq 2 then
            Gens := [A | Identity (A): i in [1..8]];
            if #F gt 3 then 
                x := OmegaPlus(2, F).1; Gens[3] := x; 
            end if;
            Gens[#Gens + 1] := A![0,1,1,0];
        else 
            MA := MatrixAlgebra (F, d);
            M := MatrixAlgebra (F, 4);
            s := Zero (MA);
            for i in [5..d] do s[i][i] := 1; end for;
            s[1][4] := 1; s[2][3] := 1; s[3][2] := 1; s[4][1] := 1;
            t4 := M![1,0,0,1, 0,1,0,0, 0,1,1,0, 0,0,0,1];
            t := Identity (MA);
            InsertBlock (~t, t4, 1, 1);
            delta4 := DiagonalMatrix (F, [w, w^-1, w, w^-1]);
            delta := Identity (MA);
            InsertBlock (~delta, delta4, 1, 1);
            s1 := Zero (MA);
            for i in [5..d] do s1[i][i] := 1; end for;
            s1[1][3] := 1;  s1[2][4] := 1; 
            s1[3][1] := -1; s1[4][2] := -1;
            t4 := M![1,0,1,0,  0,1,0,0, 0,0,1,0, 0,1,0,1];
            t1 := Identity (MA);
            InsertBlock (~t1, t4, 1, 1);
            delta4 := DiagonalMatrix (F, [w, w^-1, w^-1, w]);
            delta1 := Identity (MA);
            InsertBlock (~delta1, delta4, 1, 1);
            u := Identity (MA);
            I := Identity (A);
            v := Zero (MA);
            for i in [1..d div 2 - 1] do
                x := (i - 1) * 2 + 1;
                y := x + 2;
                InsertBlock (~v, I, x, y);
            end for;
            InsertBlock (~v, I, d - 1, 1);
            Gens := [s, t, delta, s1, v, t1, delta1, u];
        end if;     
        P := GL (d, F);
        elt  := [P!x: x in Gens];
    end if;

  //Standard gens for OmegaMinus
    if type eq "O-" then        
        q      := #F;

        gamma  := PrimitiveElement(GF(q^2));
        w      := PrimitiveElement(F);

        tmp := gamma^(q+1);
        for i in [1..q - 1] do
           if tmp^i eq w then pow := i; break i; end if;
        end for;
        gamma := gamma^pow;
        alpha  := gamma^(q+1);
        assert alpha eq w;

        M      := MatrixAlgebra(GF(q^2), d);


        C      := GL(4,GF(q^2))!
                  [1,0,0,0,0,gamma,1,0,0,gamma^q,1,0,0,0,0,1];
        C      := Transpose(C);
        CC     := GL(4,GF(q^2))![1,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0];
        sl     := SL(2, GF(q^2));
        t      := sl![1, 1, 0, 1];
        r      := sl![1, 0, 1, 1];
        delta  := sl![gamma, 0, 0, gamma^-1];
        deltaq := sl![gamma^q, 0, 0, gamma^-q];
        G      := GL(4, GF(q^2));
        t1     := (G!TensorProduct(t, t)^(C^-1))^(CC^-1);
        r1     := (G!TensorProduct(r, r)^(C^-1))^(CC^-1);
        d1     := (G!TensorProduct(delta, deltaq)^(C^-1))^(CC^-1);
        GG     := GL(d, GF(q));
        tt     := InsertBlock(Id(GG), GL(4, GF(q))!t1, d-3, d-3);
        rr     := InsertBlock(Id(GG), GL(4, GF(q))!r1, d-3, d-3);
        dd     := InsertBlock(Id(GG), GL(4, GF(q))!d1, d-3, d-3);
      //for finding the glue later
        if d ge 6 then
            my     := InsertBlock(Id(GG), GL(2,GF(q))![0,1,1,0],1,1);
            my     := InsertBlock(my, GL(2,GF(q))![0,1,1,0],3,3);
        elif d eq 4 then
            my := GL(4,q)![0,1,0,0, 1,0,0,0, 0,0,0,w^((q-2)div 2), 
                           0,0,w^(q div 2),0];
        end if;
        Gens   := [tt, rr, dd];
        I      := Id(GL(2, GF(q^2)));
        if d gt 4 then
            p := Zero(M);
            InsertBlock (~p, I, 1, 3);
            InsertBlock (~p, -I, 3, 1);
            for i in [5..d] do p[i][i] := 1; end for;
        else
            p := Id(GG);
        end if;
        Append (~Gens, GG!p);
        if d gt 6 then 
            h := Zero (M);
            m := d - 2;
            for i in [1..m div 2 - 1] do
                x := (i - 1) * 2 + 1;
                y := x + 2;
                InsertBlock (~h, I, x, y);
            end for;
            II := I;
            InsertBlock (~h, II, m - 1, 1);
            InsertBlock (~h, I, d - 1, d - 1);
            Append (~Gens, h);
        else
            Append (~Gens, GG!p);
        end if;
        elt :=[GL(d, q)! g: g in Gens]; 
        Append(~elt,my);
    end if;

  //to avoid confusion Sp / SL
    if type in ["SL","SU"] then Append(~elt,elt[1]^0); end if;

  //add a good involution; for new version of StdGens
    if not type eq "O-" then
        if type in ["SL","SU"] and IsEven(d) then
            pow  := elt[2];
            inv  := elt[2];
            for i in [1..(d div 2) -1] do
                pow := pow^elt[5];
                inv := inv*pow;
            end for;
            Append(~elt,inv);
        elif type in ["Sp","O+"] and (d mod 4 eq 0) then
            pow := elt[1];  
            inv := elt[1];  
            cyc := elt[5]^2;
            for i in [1..(d div 4)-1] do
                pow     := pow^cyc;
                inv     := inv*pow;
            end for;
            Append(~elt,inv);
        else
            Append(~elt,elt[1]^0);
        end if;
    end if;

    return elt;
end function;


/*********************************************************************/
/* Input:   field F, degree d, type
/* Output:  stdgens of SX(F,d)  which are to construct
/*********************************************************************/
StandardGenerators := function(F, d, type)
    elt := StandardGeneratorElements(F,d,type);
  //delete prelim element
    Prune(~elt);
    return elt;
end function;


/*********************************************************************/
/* Input:   matrix group G=SX(d,2^n) and type, with small d
/* Output:  stdgens as SLPs using specialised functions 
/*********************************************************************/
StandardGensSmallDegree := function(G, type : posBl := 0, debug:=false)
  
 
  //if debug eq true then "aha...", #G; end if;	

  //keep copy of input group
    cput := Cputime();  
    cG   := MakeCopyOfInitialisedGroup(G);
    F    := BaseRing(G);
    d    := Degree(G);
    vprint SXECstdgens,2: "   start StandardSmallDeg", d,posBl; 
    
  //first call?
    if posBl cmpeq 0 then posBl := "top"; end if;

  //these elements are to construct
    elt     := StandardGeneratorElements(F,d,G`type);
    eltcopy := elt;

  //conjugate SU to standard copy
    if G`type in ["SU","Sp","O+","O-"] then
        H, BCform, toStd := MyConjugateToStandardCopy(G,G`type);
 
      //"this is orig Group",UnitaryForm(G);
      //"this is nwe group",UnitaryForm(H);
      //"this is BCform",BCform;
      //"this is toStd",toStd;

        H`UserWords      := G`UserWords;
        H`COB            := G`COB;
        G                := H;
        G`type           := cG`type;
    else
        toStd            := Id(G);
        BCform           := Id(G);
    end if;  
 
  //write SU(2,-) as SL(2,-)
    if type eq "SU" and d eq 2 then
        P      := GL(2,Isqrt(#F));
        ugs    := [P!u: u in UserGenerators(G)];
        G      := sub<P|ugs>;
        G`UserGenerators := ugs;
        G`type := "SU";
        InitialiseGroup(G);
      //toStd  :=Generic(G)!toStd;
        F      := BaseRing(G);
        elt    := [P!u : u in elt];
    end if; 
   
  ///copy for Recognise functions and for fast "Position"  
    ug  := [Generic(G)!u : u in UserGenerators(G)];
    H   := MakeCopyOfInitialisedGroup(G);
 
  //if we're in bottom then don't need all gens
  //note that we might need bottom x,y for SU in odd degree!
    if posBl eq "bottom" and (IsEven(d) or type eq "SL") 
       and not type in ["Sp","O+","O-"] then 
        for i in [1,4,6,7] do elt[i] := elt[i]^0; end for;
    end if;
    if posBl eq "bottom" and type eq "SU" and IsOdd(d) then
        for i in [1,4] do elt[i] := elt[i]^0; end for;
    end if;

  //construct this if we construct stdgens for Sp
  //but we only have O+ as a bottom group
    if posBl eq "bottom" and G`type eq "O+" and type eq "Sp" then
        for i in [6] do elt[i] := elt[i]^0; end for;
    end if;
  //for small fields we need elt[1] for finding fpf element (glue) 
    if (type eq "SL" and #F eq 2) or (type eq "SU" and #F eq 4) then
        InsertBlock(~elt[1],GL(2,F)![0,1,1,0],1,1);
    end if;

  //to apply the map given by the recognise functions to the elts;
  //to avoid having non-trivial words representing the identity
    mapIt := function(m,els)
        idw  := m(els[1]^0)^0;
        wrds := [ ];
        for e in els do
            if e eq Id(H) then 
                Append(~wrds,idw); 
            else 
                Append(~wrds,m(e)); 
            end if;
        end for;
        return wrds, [Position(ug,H.i) : i in [1..Ngens(H)]];
    end function;


    done := false;
    if G`type eq "SL"  then
        if d eq 2 then 
            vprint SXECstdgens, 3: "      start recSL2",d;

          //if debug then "this is group before RSL2"; H:Magma; end if;

             flag := false; 
             fcnt := 1;    
             while not flag or fcnt lt 4 do
                flag,_,_,m1,m2 := RecogniseSL2(H,#F);      
                fcnt := fcnt + 1;    
            end while;    
            if not flag then error "recogniseSL2 failed"; end if;

          //f,_,_,m1,m2  := RecogniseSL2(H, #F);

          //if debug then "this is group after RSL2"; H:Magma; end if;
            if not flag then H:Magma; error "RecSL2 failed"; end if;  


          //"again";
          //f,_,_,m1,m2  := MyClassicalConstructiveRecognition(H,"SL",2,#F);

            vprint SXECstdgens, 3: "      end recSL2",d;
            w, pos := mapIt(m1,elt);
        elif d eq 3 then
            vprint SXECstdgens, 3: "      start recSL3",d;

            flag := false; 
            fcnt := 1;    
            while not flag or fcnt lt 4 do
               flag,_,_,m1,m2 := RecogniseSL3(H,#F);      
               fcnt := fcnt + 1;    
            end while;    
           

          //f,_,_,m1,m2  := RecogniseSL3(H, #F);

            if not flag then H:Magma; error "RecSL3 failed"; end if;
            vprint SXECstdgens, 3: "      end recSL3",d;
            w, pos := mapIt(m1,elt);
        elif d eq 4 and not #F eq 2 then
            vprint SXECstdgens, 3: "      start solveSL4",d;
            elt,w,cb := SolveSL4(G);
            done     := true;
            vprint SXECstdgens, 3: "      end solveSL4",d;
        elif d eq 5 then
            vprint SXECstdgens, 3: "      start solveSLSU5",d;
            elt,w,cb := SolveSLSU5(G,"SL");
            done     := true;
            vprint SXECstdgens, 3: "      end solveSLSU5",d;
        else
          //this is ONLY called for small fields,
          //composition tree does not call the old SLeven code!
            vprint SXECstdgens, 3: "      start COMP TREE for",type,d;
     
            //"start comptree with this group H",H:Magma;
            //"these are user gens",H`UserGenerators:Magma;
            //"want these elts", elt:Magma;

            prior := [i : i in [19 .. 1 by -1]];
            for i in [16..18] do prior[i] := 0; end for;
          //T    := CompositionTree(H: Priorities := prior);
          //"test new CT 2";
          //T   := CompositionTree(H : Priorities := prior, LeafPriorities := [1,2,3,4]);
          //"new CT 2";
            T   := CompositionTree(H : Priorities := prior, LeafPriorities := [4,3,2,1]);
            w    := [];
            _,id := CompositionTreeElementToWord(H,Id(H));
            id   := id ^0;
            for e in elt do
                if not e eq Id(H) then
                    flg, wtmp := CompositionTreeElementToWord(H,e);
                    assert flg;
                    Append(~w,wtmp);
                else 
                    Append(~w,id); 
                end if;
            end for;
   
            map := CompositionTreeNiceToUser(H);
            w   := [Image(map,e) : e in w];
            pos := [Position(ug,H.i) : i in [1..Ngens(H)]];
          //pos := [Position(ug,u) : u in UserGenerators(H)]; 
            vprint SXECstdgens, 3: "      end COMP TREE for ",type,d;
        end if;
        if not done then
            w  := Evaluate(w,[G`SLPGroup.i : i in pos]);
            cb := Id(cG);
        end if;
    end if;
    if G`type eq "SU" then
        if d eq 2 then 
            vprint SXECstdgens, 3: "      start recSU2",d;
          //note: H is written as SL2


           flag := false; 
           fcnt := 1;    
           while not flag or fcnt lt 4 do
             flag,_,_,m1,m2 := RecogniseSL2(H,#F);      
             fcnt := fcnt + 1;    
          end while;    
         
        //f,_,_,m1,m2  := RecogniseSL2(H, #F);
 
            if not flag then H:Magma; error "RecSU(L)2 failed"; end if;
            vprint SXECstdgens, 3: "      end recSU2",d;
            w, pos := mapIt(m1,elt);
        elif d eq 3 and not #F eq 4 then
            vprint SXECstdgens, 3: "      start recSU3",d;

            flag := false; 
            fcnt := 1;    
            while not flag or fcnt lt 4 do
               flag,_,_,m1,m2 := RecogniseSU3(H,Isqrt(#F));      
               fcnt := fcnt + 1;    
            end while;    
            
          //f,_,_,m1,m2  := RecogniseSU3(H, Isqrt(#F));


            if not flag then H:Magma; error "RecSU3 failed"; end if;
            vprint SXECstdgens, 3: "      end recSU3",d;
            w, pos := mapIt(m1,elt);
        elif d eq 5 and not #F eq 4 then
            vprint SXECstdgens, 3: "      start solveSLSU5",d;
            elt,w,cb := SolveSLSU5(G,"SU");
            done     := true;
            vprint SXECstdgens, 3: "      end solveSLSU5",d;
        elif d eq 4 then
            vprint SXECstdgens, 3: "      start recSU4",d;

          flag := false; 
          fcnt := 1;    
          while not flag or fcnt lt 4 do
             flag,_,_,m1,m2 := RecogniseSU4(H,Isqrt(#F));      
             fcnt := fcnt + 1;    
          end while;  


          //f,_,_,m1,m2  := RecogniseSU4(H, Isqrt(#F));


            if not flag then H:Magma; error "RecSU4 failed"; end if;
            vprint SXECstdgens, 3: "      end recSU4",d;
            w, pos := mapIt(m1,elt);
            w      := Evaluate(w,[G`SLPGroup.i : i in pos]);
            cb     := Id(cG);
            done   := true;
        else
          //does not work for larger fields!
            vprint SXECstdgens, 3: "      start COMP TREE for",type,d;
            prior := [i : i in [19 .. 1 by -1]];
            for i in [16..18] do prior[i] := 0; end for;
            // EOB added LeafPriorities to avoid recursion 
          //T   := CompositionTree(H : Priorities := prior, LeafPriorities := [1,2,3,4,5]);
          //"CT 1'";
            T   := CompositionTree(H : Priorities := prior, LeafPriorities := [5,4,3,2,1]);

            w   := [];
            _,id := CompositionTreeElementToWord(H,Id(H));
            id   := id ^0;
            for e in elt do
                if not e eq Id(H) then
                    flg, wtmp := CompositionTreeElementToWord(H,e);
                    assert flg;
                    Append(~w,wtmp);
                else 
                    Append(~w,id); 
                end if;
            end for;
            map := CompositionTreeNiceToUser(H);
            w   := [Image(map,e) : e in w];
            pos := [Position(ug,H.i) : i in [1..Ngens(H)]]; 
            vprint SXECstdgens, 3: "      end COMP TREE for",type,d;
        end if;
        if not done then
            w  := Evaluate(w,[G`SLPGroup.i : i in pos]);
            cb := Id(cG);
        end if;
    end if;
    if G`type in ["Sp","O+","O-"] then

        if G`type eq "Sp" and d eq 6 and #F ge 4 then 
            w, cb := SolveSp6(H,posBl);
        elif G`type eq "Sp" and d eq 4 then
            vprint SXECstdgens, 3: "      start recSp4";

          flag := false; 
          fcnt := 1;    
          while not flag or fcnt lt 4 do
           flag,_,_,m1,m2 := RecogniseSp4(H,#F);      
             // flag,_,_,m1,m2 := ClassicalConstructiveRecognition(H,"Sp",4,#F);
             fcnt := fcnt + 1;    
          end while;



          //f,_,_,m1,m2  := RecogniseSp4Even(H, #F);
            if not flag then 
                H:Magma;
                error "RecogniseSp4 failed"; 
            end if;
            vprint SXECstdgens, 3: "      end RecogniseSp4";
            w, pos := mapIt(m1,elt);
            w      := Evaluate(w,[G`SLPGroup.i : i in pos]);
            cb     := Id(cG);
        elif G`type eq "O+" and d eq 6 then

            w, cb := SolveOp6(H,posBl);

        elif G`type eq "O-" and d eq 6 then
            w, cb := SolveOm6(H,posBl);
        elif G`type eq "O-" and d eq 4 then
            vprint SXECstdgens, 3: "      start recSL2 for O-(4)",d;

          flag := false; 
          fcnt := 1;    
          while not flag or fcnt lt 4 do
             flag,toSl,_,m1,m2 := RecogniseSL2(H,#F^2);      
             fcnt := fcnt + 1;    
          end while;
 
          //f,toSl,_,m1,m2  := RecogniseSL2(H, #F^2);
            if not flag then 
                H:Magma; error "RecSL2 for OmegaMinus(4) failed"; 
            end if;
            vprint SXECstdgens, 3: "      end recSL2 for O-(4)",d;
           
            w, pos := mapIt(m1,elt);
          
            w      := Evaluate(w,[G`SLPGroup.i : i in pos]); // THIS WAS MISSING?!?!?!
            cb     := Id(cG);
	else

	//SXEtestStdGens([18],[8],1,"O+":seed:=[ 1095988527, 143959546]);

          //this is often called for O+(4)\cong SL(2)
            vprint SXECstdgens, 3: "      start COMP TREE for",type,d;

          //T := CompositionTree(H);
          //"new CT 3";

         //H:Magma;
         //H`UserGenerators:Magma;
         //elt:Magma;
         //GetSeed();


          //T   := CompositionTree(H : LeafPriorities := [1,2,3,4,5]);
          //"CT ''";
            T   := CompositionTree(H : LeafPriorities := [5,4,3,2,1]);
            w := [];
            _,id := CompositionTreeElementToWord(H,Id(H));
            id   := id ^0;

            for e in elt do
                if not e eq Id(H) then
                    flg, wtmp := CompositionTreeElementToWord(H,e);
                  //if not flg then "cte2w returned false but elt in group", e in H; end if;
                    assert flg;
                    Append(~w,wtmp);
                else 
                    Append(~w,id); 
                end if;
            end for;

            map := CompositionTreeNiceToUser(H);
            w   := [Image(map,e) : e in w];
            pos := [Position(ug,H.i)  : i in [1..Ngens(H)]]; 
            vprint SXECstdgens, 3: "      end COMP TREE for",type,d;
            if not done then
                w  := Evaluate(w,[G`SLPGroup.i : i in pos]);
                cb := Id(cG);
            end if;

        end if;
    end if;

    if d ge 3 then
      //don't print all cputimes for base case in degree 2
        vprint SXECcpu,1: "CPU time StdGens for base case",
                            type,"(",d,"):",Cputime(cput);
    end if;
    vprint SXECstdgens,2: "   end StandardSmallDegree in degree", d; 
 
  //delete non-computed elements
    idw := w[1]^0;
    for i in [1..#w] do 
        if w[i] eq idw then eltcopy[i] := Id(H); end if; 
    end for;


  //"test in base case at bottom"; 
  // "eltcopy and should",eltcopy,Evaluate(w,UserGenerators(G));
  //  cb,BCform; 
  // assert eltcopy eq Evaluate(w,UserGenerators(G));

    return eltcopy ,w, cb*BCform; 
  //THIS WAS BCform*cb; THIS SHOULD BE CHANGED IN SLSU AS WELL!
  //ALTHOUGH IT HAS NO IMPACT BECAUSE EITHER CB=Id OR BCform=Id
end function;


/*********************************************************************/
/* Input:   matrix group G, stdgens elt for smaller SX(m) with
/*          SLPs w, base change CB, type, 
/*          pos in {"top","bottom"}
/* Output:  an element of odd order which acts fpf on either
/*          subspace [1..m-2] (top) or [m+3..d] (bottom)
/*********************************************************************/
FindFPFElForGlue := function(G,elt,w,CB,type,m,pos)
    d  := Degree(G);
    F  := BaseRing(G);
    sf := false; //smallField?

  //construct start elt, depending on field size
    if (type eq "SL" and #F eq 2) or (type eq "SU" and #F eq 4) then
        sf := true;
        if pos eq "top" then
          fp := [elt[1]*elt[2]];          fpw := [w[1]*w[2]];
        else
          fp := [(elt[1]*elt[2])^elt[5]]; fpw := [(w[1]*w[2])^w[5]];
        end if;
    else
        if pos eq "top" then
            fp := [elt[3]];               fpw := [w[3]];
        else
            fp := [elt[3]^elt[5]];        fpw := [w[3]^w[5]];   
        end if;
    end if;
   
  //now construct fpf elements
    if pos eq "top" then
      //note that m is always even and >=4 
        r   := m div 2;
        for i in [1..r-2] do 
            fp[i+1] := fp[i]^elt[5]; fpw[i+1] := fpw[i]^w[5];
        end for;
        fp  := &*fp;  fpw := &*fpw;
    elif pos eq "bottom" then
          if type eq "SU" or IsEven(d-m) then
            r   := (d-m) div 2;
            if r gt 1 then
                for i in [1..r-2] do
                    fp[i+1] := fp[i]^elt[5]; fpw[i+1] := fpw[i]^w[5];
                end for;
                fp  := &*fp; fpw := &*fpw;
                if type eq "SU" and IsOdd(d-m) then
                    if not sf then
                        fp  := fp*elt[7]^(elt[5]^(r-1));
                        fpw := fpw * w[7]^(w[5]^(r-1));
                    else
                        fp  := (fp*elt[6])^4;
                        fpw := (fpw*w[6])^4;
                   end if;
                end if;
            elif r eq 1  then
                return elt[1]^0,w[1]^0;
            end if;   
      //now consider odd degree
        else
          //new cycle:
            r := (d-m) div 2;
            if r gt 0 then
                for i in [1..r-2] do
                   fp[i+1]  := fp[i]^elt[5];
                   fpw[i+1] := fpw[i]^w[5];
                end for;
                fp  := &*fp;
                fpw := &*fpw;  
                if not sf then
                    fp  := fp*elt[3]^(elt[5]^-1);
                    fpw := fpw*w[3]^(w[5]^-1);
                else 
                    fp  := fp*elt[1]^(elt[5]^-1);
                    fpw := fpw*w[1]^(w[5]^-1);
                end if;;
            elif r eq 0  then
                return elt[1]^0,w[1]^0;
            end if;
        end if;
    end if;
    return fp,fpw;
end function;


/*********************************************************************/
/* Input:   matrix group G, stdgens elt for smaller SX(m) with
/*          SLPs w, base change CB, type, 
/*          pos in {"top","bottom"}
/*          Does not work for OmegaPlus(4,6;GF(2))
/* Output:  an element of odd order which acts fpf on either
/*          subspace [1..m-4] (top) or [m+5..d] (bottom)
/*********************************************************************/
FindFPFElForOPlus := function(G,elt,w,CB,type,m,pos : test := false)
    d := Degree(G);
    F := BaseRing(G);
    if #F eq 2 then 
        if type eq "Sp" then 
            el := elt[2]*elt[1]; wrd := w[2]*w[1];
            pc := 1;
            if pos eq "top" then
                l := ((m-4) div 2) -1;
                if m le 4 then return el^0, wrd^0; end if;
            else
                error "sp bottom should not occur";
            end if;
        elif type eq "O+" then
            el := elt[2]*elt[1]; wrd := w[2]*w[1];
            pc := 2;
            if pos eq "top" then
                l := ((m-4) div 4) -1;
                if m le 6 then error "deg 6 should not occur"; end if;
                if m le 4 then return el^0, wrd^0; end if;
                if not m mod 4 eq 0 then
                    el  := el^elt[5];
                    wrd := wrd^w[5];
                end if;
            else
                l := (((d-m)-4) div 4)-1;
                if d-m gt 6 then
                    el := el^(elt[5]^2); wrd := wrd^(w[5]^2);
                else
                    if (d-m) eq 4 then return el^0,wrd^0; end if;
                    error "deg 6 should not occur";
                end if;
            end if;
        end if;
        newel := el;
        nwrd  := wrd;
        pow   := elt[5]^pc;
        poww  := w[5]^pc;
        for i in [1..l] do
            newel := newel*el^pow;
            nwrd  := nwrd*wrd^poww;
            pow   := pow*elt[5]^pc;
            poww  := poww*w[5]^pc;
        end for;
        if type eq "O+" then
            if pos eq "top"  and not (m mod 4 eq 0) then 
                newel := elt[1]*newel;
                nwrd  := w[1]*nwrd;
            elif pos eq "bottom" and not ((d-m) mod 4 eq 0) then
                newel  := newel*elt[1]^(pow*elt[5]);
                nwrd   := nwrd*w[1]^(poww*w[5]);
            end if;
        end if;
        return newel, nwrd;
    end if;
    
  //if #F greater than 2
    el := elt[3]*elt[7]; wrd := w[3]*w[7];   
    if pos eq "top" then
        l := ((m-4) div 2) -1;
        if m le 4 then return el^0, wrd^0; end if;
    else
        l := (((d-m)-4) div 2) -1;
        if d-m ge 6 then
            el := el^(elt[5]^2); wrd := wrd^(w[5]^2);
        else
            return el^0,wrd^0;
        end if;
    end if;
    newel := el;
    nwrd  := wrd;
    pow   := elt[5];
    poww  := w[5];
    for i in [1..l] do
        newel := newel*el^pow;
        nwrd  := nwrd*wrd^poww;
        pow   := pow*elt[5];
        poww  := poww*w[5];
    end for;  
    return newel, nwrd;
end function;


/*********************************************************************/
/* Input:   matrix group G, stdgens elt for smaller SX(m) with
/*          SLPs w, base change CB
/* Output:  an element of odd order which acts fpf on either
/*          subspace [1..m-4] (top) 
/*********************************************************************/
FindFPFElForOMinus := function(G,elt,w,CB,m)
    d := Degree(G);
    F := BaseRing(G);
    if d-m eq 4 then return elt[3]^0, w[3]^0; end if;
    if d-m eq 6 then
      //bottleneck! 
        return elt[3]^(#F-1), w[3]^(#F-1);
    end if;
    if #F eq 2 then      
        if d-m eq 8 then
            return elt[1]*elt[2]*elt[3], w[1]*w[2]*w[3];
        end if;
        ab   := elt[1]*elt[2]; 
        wab  := w[1]*w[2];
        cyc  := elt[5];
        wcyc := w[5];
        el   := elt[3]*ab;
        wel  := w[3]*wab;
        for i in [3..((d-m-2) div 2)] do
            el  := el*ab^(cyc^i);
            wel := wel*wab^(wcyc^i);
        end for;
      //fix order
        if not (d-m) mod 4 eq 0 then 
            el  := el^4;
            wel := wel^4; 
        end if;
        return el, wel;
    else
        el := elt[5]^-3*elt[3]*elt[5]^3; wrd := w[5]^-3*w[3]*w[5]^3;
    end if;
    l := (((d-m)-8) div 2);
    newel := el;
    nwrd  := wrd;
    pow   := elt[5];
    poww  := w[5];
    for i in [1..l] do
        newel := newel*el^pow;
        nwrd  := nwrd*wrd^poww;
        pow   := pow*elt[5];
        poww  := poww*w[5];
    end for;
    
    if Eltseq(ExtractBlockNEW(newel,[d-1,d])) eq [1,0,0,1] then
        newel := newel*el;
        nwrd  := nwrd*wrd;
    end if;

    return newel, nwrd;
end function;


/*********************************************************************/
/* Input:   matrix group A= [SX(2) 0 *; 0 I 0; 0 0 SX(2)]
/* Output:  glue element + slp
/*********************************************************************/
FindGlueElement := function(A,type)  


    cput  := Cputime();
    vprint SXECstdgens,4: "         find Glue: Start CompTree deg 4";
    F     := BaseRing(A);
    d     := Degree(A);
  //make 4x4 copy A4
    ugens := UserGenerators(A);
    ugnew := [];
    for i in [1..#ugens] do
        a := ugens[i];
        b := Id(GL(4,F));
        InsertBlock(~b,ExtractBlock(a,1,1,2,2),1,1);
        InsertBlock(~b,ExtractBlock(a,1,1,2,2),3,3);
        InsertBlock(~b,ExtractBlock(a,1,d-1,2,2),1,3);
        ugnew[i] := GL(4,F)!b;
    end for;
    A4    := sub<GL(4,F)|ugnew>;
    A4`UserGenerators := ugnew;
    InitialiseGroup(A4:UserWords:=A`UserWords, type := "no");   
  //prepare copy A4c for composition tree 
    ug    := [Generic(A4)!u : u in UserGenerators(A4)];
    A4c   := MakeCopyOfInitialisedGroup(A4);
    prior := [i : i in [19 .. 1 by -1]];
    for i in [16..18] do prior[i] := 0; end for;   

  //T     := CompositionTree(A4c : Priorities := prior);
  //"new CT 4";
  //T   := CompositionTree(A4c : Priorities := prior, LeafPriorities := [1,2,3,4]);
  //"new CT 4";
    T   := CompositionTree(A4c : Priorities := prior, LeafPriorities := [5,4,3,2,1]);

    glue  := GL(4,F)![0,1,0,0, 1,0,0,0, 0,0,0,1, 0,0,1,0];
    flG,w := CompositionTreeElementToWord(A4c,glue);
    if not flG then
      //if this fails, then A=[SX(2)0*; 0I0; 00SX(2)] does 
      //not have the full group [SX(2)00;0I0;00SX(2)] as subgrp
      //this is a failure of MyCentraliserOfInvolution
        error "unfortunately we couldn't find glue element";
    end if;

  //pull back to element in A
    pos   := [Position(ugnew,A4c.i):i in [1..Ngens(A4c)]]; //changed here!   
    map   := CompositionTreeNiceToUser(A4c);
    w     := Image(map,w);
    vprint SXECcpu,1:"CPU time CompTree for glue (dim 4):",
                       Cputime(cput);
    w     := Evaluate(w,[A`SLPGroup.i : i in pos]);
   
    bl    := GL(2,F)![0,1,1,0];
    tmp   := DiagonalJoin(bl,Id(GL(d-4,F)));
    bl    := DiagonalJoin(tmp,bl);
    glue  := GL(d,F)!bl;

    vprint SXECstdgens,4: "         find Glue: End CompTree deg 4";
    return glue, w;
end function;


/*********************************************************************/
/* Input:   matrix group A= [SX(4) 0 *; 0 I 0; 0 0 SX(4)]
/* Output:  glue element + slp 
/* Comment: this is glueing function for Omega+Omega
/*********************************************************************/
FindGlueElementOO:= function(A,glue)
  
    cput  := Cputime();
    vprint SXECstdgens,4:"         find glueOO: Start CompTree deg 8";
    F     := BaseRing(A);
    d     := Degree(A);

  //make 8x8 copy A8
    ugens := UserGenerators(A);
    ugnew := [];
    for i in [1..#ugens] do
        a := ugens[i];
        b := Id(GL(8,F));
        InsertBlock(~b,ExtractBlock(a,1,1,4,4),1,1);
        InsertBlock(~b,ExtractBlock(a,1,1,4,4),5,5);
        InsertBlock(~b,ExtractBlock(a,1,d-3,4,4),1,5);
        ugnew[i] := GL(8,F)!b;
    end for;
    A8    := sub<GL(8,F)|ugnew>;
    A8`UserGenerators := ugnew;
    InitialiseGroup(A8:UserWords:=A`UserWords, type := "no");  

  //"this is block A of [A0*;0I0;00A]";
  //At := ExtractGroup(A,[1..4]);
  //At:Magma;
  //LMGCompositionFactors(At);

 
  //prepare copy A8c for composition tree 
    ug    := [Generic(A8)!u : u in UserGenerators(A8)];
    A8c   := MakeCopyOfInitialisedGroup(A8);
    prior := [i : i in [19 .. 1 by -1]];
    for i in [16..18] do prior[i] := 0; end for;   
  //T     := CompositionTree(A8c : Priorities := prior); 
  //"new CT 5";
  //T   := CompositionTree(A8c : Priorities := prior, LeafPriorities := [1,2,3,4,5]); 
  //"new CT 5";
    T   := CompositionTree(A8c : Priorities := prior, LeafPriorities := [5,4,3,2,1]);
    flG,w := CompositionTreeElementToWord(A8c,glue);
    if not flG then
      //if this fails, then A=[SX(4)0*; 0I0; 00SX(4)] does 
      //not have the full group [SX(4)00;0I0;00SX(4)] as subgrp
      //which is a failure of my centraliser / killfactor
        error "A8:unfortunately we couldn't find glue element";
    end if;

  //pull back to element in A
    pos   := [Position(ugnew,A8c.i):i in [1..Ngens(A8c)]]; // changed here!   
    map   := CompositionTreeNiceToUser(A8c);
    w     := Image(map,w);
    vprint SXECcpu,1:"CPU time CompTree for glue (dim 8):",
                       Cputime(cput);
    w     := Evaluate(w,[A`SLPGroup.i : i in pos]);
   
    if d ge 10 then
        bl    := One(MatrixAlgebra(F,d));
        InsertBlock(~bl,ExtractBlockNEW(glue,[1..4]),1,1);
        InsertBlock(~bl,ExtractBlockNEW(glue,[5..8]),d-3,d-3);
        InsertBlock(~bl,ExtractBlock(glue,1,5,4,4),1,d-3);  
        glue := Generic(A)!bl;
    end if;

    vprint SXECstdgens,4:"         find glueOO: End CompTree deg 8";
    return glue, w;
end function;


/*********************************************************************/
/* Input:  helping function for GlueCycles for special
/*         case that we have to glue SX(m) with SX(3)
/*         where  m is 4 or 6 and SX is SL or SU
/* Output: standard gens for SX(m+3)
/*********************************************************************/
SolveDegree3Problem := function(G,C,eltA,wA,eltB,wB,CB,type,m,cbinv)
      
    cput    := Cputime();
    d       := Degree(G);  
    vprint SXECstdgens,3: "         start SolveDeg3 for degs",m,d-m;
    F       := BaseRing(G);
  //note that C has type [2x2 * * ; 0 mxm *; 0 0 2x2] 
  //construct fp of type [I_3 0 0; 0 c 0; 0 0 I_2] 
  //with c odd order and fpf. Use this to
  //construct A of type [ 2x3 0 3x2; 0 1 0; 0 0 2x2]
    fp, fpw := FindFPFElForGlue(G,eltA,wA,CB,type,m,"top");
    fp      := cbinv*fp*cbinv^-1;
    A,_     := FormulaAB(C, 2, fp, fpw, type: glue := true);
 
  //construct element (glue) we look for 
    MA      := MatrixAlgebra(F,d);
    glue    := Id(MA);
    bl      := GL(2,BaseRing(A))![0,1,1,0];
    InsertBlock(~glue,bl,1,1);
    InsertBlock(~glue,bl,d-1,d-1);
    glue    := Generic(G)!glue;

  //make copy of group for composition tree
    ug      := [Generic(A)!u : u in UserGenerators(A)];
    Ac      := MakeCopyOfInitialisedGroup(A); 
    prior := [i : i in [19 .. 1 by -1]];
    for i in [16..18] do prior[i] := 0; end for;
  //T       := CompositionTree(Ac : Priorities := prior);
  //"new CT 6";
    if type eq "SU" then
     //T   := CompositionTree(Ac : Priorities := prior, LeafPriorities := [1,2,3,4,5]);
       T   := CompositionTree(Ac : Priorities := prior, LeafPriorities := [5,4,3,2,1]);
    else
     //T   := CompositionTree(Ac : Priorities := prior, LeafPriorities := [1,2,3,4]);
       T   := CompositionTree(Ac : Priorities := prior, LeafPriorities := [4,3,2,1]);
    end if;
    flG,w   := CompositionTreeElementToWord(Ac,glue);
    if not flG then
      //if this fails, then A=[SX(2)0*; 0I0; 00SX(2)] does 
      //not have the full group [SX(2)00;0I0;00SX(2)] as subgrp
      //this is failure of MyCentraliserOfInvolution
        error "Deg3: unfortunately we couldn't find glue element";
    end if;
    pos     := [Position(ug,Ac.i):i in [1..Ngens(Ac)]];   
    map     := CompositionTreeNiceToUser(Ac);
    w       := Image(map,w);

  //write everything as word in user gens of given group G
    w       := Evaluate(w,[A`SLPGroup.i : i in pos]);
    gluew   := Evaluate(w,A`UserWords);
    glue    := Id(MA);
    bl      := GL(2,F)![1,0,0,1];
    InsertBlock(~glue,bl,d-4,d-2);
    InsertBlock(~glue,bl,d-2,d-4);
    for i in [d-4,d-3,d-2,d-1] do glue[i][i] := 0; end for;
    glue    := Generic(G)!glue;
    eltA[5] := eltB[5]*glue*eltA[5];
    wA[5]   := wB[5]*gluew*wA[5];

    vprint SXECcpu,1: "CPU time CompTree in SolvDeg3 in deg",
                        m,d-m,":",Cputime(cput);
    vprint SXECstdgens,3: "         end SolveDeg3 in degs",m,d-m;
    return eltA, wA, CB;
end function;


/*********************************************************************/
/* This is a helping function for StandardGeneratorsSXEven
/* It glues the cycles of two sets of standard gens.
/* Input:   matrix group G, list of elts eltA, eltB 
/*          and corresponding SLPs wA and wB.
/*          base change CB such that 
/*          elt=CB*Eval(w,UserGens(G))*CB^-1.
/*          eltA comes from SX(m,F), and eltB from SX(d-m,F)
/* Output:  standard gens with glued cycle
/*********************************************************************/
GlueCycles := function(G,eltA,wA,eltB,wB,CB,type,m)
   
    d := Degree(G);
    F := BaseRing(G);
    if IsEven(m) then l:=-1; else l:=3; end if;
    if not IsEven(m) then error "glue:should be even!"; end if;
    vprint SXECstdgens,3:"     find Glue for combining degrees",m,d-m;
  
  //construct elt with block [1100;0100;0011;0001] at pos m-1
    e1  := eltA[2]; //[1 1; 0 1]
    w1  := wA[2];
    e2  := eltB[2]; //[1 1; 0 1]
    w2  := wB[2];
    c   := eltA[5]; //cycle
    w   := wA[5];
    elt := c^-l*e1*c^l*e2;
    wrd := w^-l*w1*w^l*w2;
  //make base change s.t. elt =[I2 0 I2; 0 I 0; 0 0 I2]
  //and glue has block diag form
  //do it manually to understand structure of matrix and
  //to see what's going on...  
    cbinv := Zero(MatrixAlgebra(F,d));
    cbinv[1][m+1] := One(F);   cbinv[2][m-1]   := One(F);
    cbinv[d][m]   := One(F);   cbinv[d-1][m+2] := One(F);
    InsertBlock(~cbinv,ReverseRows(Id(GL(m-2,F))),d-m+1,1);
    if d gt m+2 then 
        InsertBlock(~cbinv,ReverseRows(Id(GL(d-m-2,F))),3,m+3);
    end if;
    cbinv := Generic(G)!cbinv;

    H     := MakeCopyOfInitialisedGroup(G);
    H     := ApplyCOB(H,cbinv*CB);
    g     := cbinv * elt * cbinv^-1;
    C, Cw := MyCentraliserOfInvolution(H,g,wrd,type);
 
  //construct fp = [A 0 0;0 I_4 0; 0 0 B] with
  //A,B of odd order and fpf
  //then transform fp to fp=[I2 00;0C0;00I2], C odd order, fpf
  //use this element as formula element to extract [A0*;0I0;00A]
  //with A=SX(2)
    if not d-m eq 3 then
        fpel1, fpw1 := FindFPFElForGlue(G,eltA,wA,CB,type,m,"top");
        fpel2, fpw2 := FindFPFElForGlue(G,eltB,wB,CB,type,m,"bottom");
        fw          := fpw1*fpw2;
        fp          := cbinv*fpel1*fpel2*cbinv^-1;
        A,_         := FormulaAB(C, 2, fp, fw, type : glue:=true);
    else
       //only d=7 or d=9
        return SolveDegree3Problem(G,C,eltA,wA,eltB,wB,
                                   CB,type,m,cbinv);
    end if;

  //if A = [u 0 v;0 I 0;0 0 u] with u=[u1 u2; u3 u4] 
  //                           and  v=[v1 v2l v3 v4]
  //then cbinv^-1*A*cbinv has 4x4 block at pos m-1:
  //    [u4 v4 u3 v3] 
  //    [ 0 u4  0 u3]
  //    [u2 v2 u1 v1]
  //    [ 0 u2  0 u1]
  //Hence, look for A with u=[0 1;1 0] and v=0

    glue, gluew := FindGlueElement(A,type);
    gluew       := Evaluate(gluew,A`UserWords);
    glue        := cbinv^-1*glue*cbinv;

    eltA[5]     := eltB[5]*glue*eltA[5];



    wA[5]       := wB[5]*gluew*wA[5];
    vprint SXECstdgens,3: "     end Glue for combining degrees",m,d-m;
    return eltA, wA, CB;
end function;


/*********************************************************************/
/* This is a helping function for StandardGeneratorsSXEven
/* It glues the cycles of two sets of standard gens.
/* Input:   matrix group G, list of elts eltA, eltB 
/*          and corresponding SLPs wA and wB.
/*          base change CB such that 
/*          elt=CB*Eval(w,UserGens(G))*CB^-1.
/*          eltA comes from SX(m,F), and eltB from SX(d-m,F)
/* Output:  standard gens with glued cycle
/*********************************************************************/
GlueCyclesOPlus := function(G,eltA,wA,eltB,wB,CB,type,m)
   
    d := Degree(G);
    F := BaseRing(G);
    if not IsEven(m) then error "glue:should be even!"; end if;
    vprint SXECstdgens,3: "     find Glue for combining degrees",m,d-m;
  
  //construct elt with block [A0,0A] at pos m-3 
  //where [0100;1000;0001;0010]
    if type eq "Sp" then //HERE WAS 5
      //e1  := eltA[1]*eltA[1]^eltA[4]; //[0100;1000;0001;0010]
      //w1  := wA[1]*wA[1]^wA[4];
        e1  := eltA[8];
        w1  := wA[8];
    elif type eq "O+" then
        e1  := eltA[4]*eltA[1]; //[0100;1000;0001;0010]
        w1  := wA[4]*wA[1];
    end if;
    e2  := eltB[4]*eltB[1]; //[0100;1000;0001;0010]
    w2  := wB[4]*wB[1];
    c   := eltA[5]; //cycle
    w   := wA[5];
    elt := c^2*e1*c^-2*e2;
    wrd := w^2*w1*w^-2*w2;

  //construct glue we are looking for in A
    MA  := MatrixAlgebra(F,d);
    tmp := One(MA);
    for i in [m-1,m,m+1,m+2] do tmp[i][i] := 0; end for;
    tmp[m-1][m+1] := 1; tmp[m][m+2] := 1;
    tmp[m+1][m-1]:=1; tmp[m+2][m] :=1;

  //make base change s.t. elt =[I4 0 I4; 0 I 0; 0 0 I4]
  //and glue has block diag form
  //do it manually to understand structure of matrix and
  //to see what's going on...
    cbinv := Zero(MA);
    if not m eq 4 then
        InsertBlock(~cbinv,ReverseRows(Id(GL(m-4,F))),d-m+1,1);
    end if;
    if not d eq m+4 then
        InsertBlock(~cbinv,ReverseRows(Id(GL(d-m-4,F))),5,m+5);
    end if;
    cbinv[1][m+4]   := One(F); cbinv[2][m+2]   := One(F);
    cbinv[3][m]     := One(F); cbinv[4][m-2]   := One(F);
    cbinv[d][m-3]   := One(F); cbinv[d][m-2]   := One(F);
    cbinv[d-1][m-1] := One(F); cbinv[d-1][m]   := One(F);
    cbinv[d-2][m+1] := One(F); cbinv[d-2][m+2] := One(F);
    cbinv[d-3][m+3] := One(F); cbinv[d-3][m+4] := One(F);
    cbinv := GL(d,F)!cbinv;
    tmp   := GL(d,F)! cbinv*tmp*cbinv^-1;

  //check whether base change is correct!
  //btmp := BaseChangeInvolution(elt);
  //assert btmp*elt*btmp^-1 eq cbinv*elt*cbinv^-1;
  //btmp := One(MA);
  //btmp[2][2] := Zero(F); btmp[2][3] := One(F);
  //btmp[3][3] := Zero(F); btmp[3][2] := One(F);
  //btmp[d-1][d-1] := Zero(F); btmp[d-1][d-2] := One(F);
  //btmp[d-2][d-2] := Zero(F); btmp[d-2][d-1] := One(F);
  //btmp := GL(d,F)!btmp;
  //assert btmp eq tmp;

    H     := MakeCopyOfInitialisedGroup(G);
    H     := ApplyCOB(H,cbinv*CB);
    g     := cbinv * elt * cbinv^-1;
    C, Cw := MyCentraliserOfInvolution(H,g,wrd,"SpO");

  //"quad";
  //"this is involution",g;
  //"this is centraliser",C;
  //"this is form",SymplecticForm(H);
  //QuadraticForm(H);
  //htmp := ExtractGroup(C,[1..4]);
  //"htmp and sections",htmp,Sections(htmp);
 //"is this sl2?";
 //sl2 := ExtractGroup(C,[1..4]);
 //LMGCompositionFactors(sl2);


  //"group,inv", H:Magma;g:Magma;

  
  //construct fp = [A 0 0;0 I_4 0; 0 0 B] with
  //A,B of odd order and fpf
  //then transform fp to fp=[I4 00;0C0;00I4], C odd order, fpf
  //use this element as formula element to extract [A0*;0I0;00A]
  //with A=SX(4)
  //need notSX because elt is not a good involution and A is
  //reducible!
    if d ge 10 then
        fpel1, fpw1 := FindFPFElForOPlus(G,eltA,wA,CB,type,m,"top");
        fpel2, fpw2 := FindFPFElForOPlus(G,eltB,wB,CB,"O+",m,"bottom");
        fw          := fpw1*fpw2;
        fp          := cbinv*fpel1*fpel2*cbinv^-1;
        A,_         := FormulaAB(C,4,fp,fw,type : 
                                 glue:=true,notSX:=true);
    else
        A           := MakeCopyOfInitialisedGroup(C);
    end if;
 
  //now make 8x8 copy of tmp to get glue element
  //which is to find  
    new := Zero(MatrixAlgebra(F,8));
    InsertBlock(~new,ExtractBlockNEW(tmp,[1..4]),1,1);
    InsertBlock(~new,ExtractBlockNEW(tmp,[d-3..d]),5,5);
    InsertBlock(~new,ExtractBlock(tmp,1,d-3,4,4),1,5);
    glue := GL(8,F)!new;

    glue, gw  := FindGlueElementOO(A,glue);
    gw        := Evaluate(gw,A`UserWords);
    glue      := cbinv^-1*glue*cbinv;
    eltA[5]   := eltB[5]*glue*eltA[5];
    wA[5]     := wB[5]*gw*wA[5];
    vprint SXECstdgens,3: "     end Glue for combining degrees",m,d-m;
    return eltA, wA, CB;
end function;


/*********************************************************************/
/* This is a helping function for StandardGeneratorsSXEven
/* It glues the cycles of two sets of standard gens.
/* Input:   matrix group G, list of elts eltA, eltB 
/*          and corresponding SLPs wA and wB.
/*          base change CB such that 
/*          elt=CB*Eval(w,UserGens(G))*CB^-1.
/*          eltA comes from SX(m,F), and eltB from SX(d-m,F)
/* Output:  standard gens with glued cycle
/*********************************************************************/
GlueCyclesOMinus := function(G,eltA,wA,eltB,wB,CB,type,m)
   
    d := Degree(G);
    F := BaseRing(G);
    if not IsEven(m) then error "glue:should be even!"; end if;
    vprint SXECstdgens,3: "     find Glue for combining degrees",m,d-m;
  
  //construct elt with block [A0,0A] at pos m-3 
  //where [0100;1000;0001;0010]
    e1  := eltA[4]*eltA[1]; //[0100;1000;0001;0010]
    w1  := wA[4]*wA[1];
    e2  := eltB[6]; //[0100;1000;0001;0010]
    w2  := wB[6];
    c   := eltA[5]; //cycle
    w   := wA[5];
    elt := c^2*e1*c^-2*e2;
    wrd := w^2*w1*w^-2*w2;

  //if d-m = 4 then e2 is [0100;1000;000x;00y0]
  //with x=F.1^((q-2)/2) and y=F.1^(q/2)  because e2 as above 
  //does not lie in OmegaMinus(4)

  //construct glue we are looking for in A
    MA  := MatrixAlgebra(F,d);
    tmp := One(MA);
    for i in [m-1,m,m+1,m+2] do tmp[i][i] := 0; end for;
    tmp[m-1][m+1] := 1; tmp[m][m+2] := 1;
    tmp[m+1][m-1]:=1; tmp[m+2][m] :=1;

  //make base change s.t. elt =[I4 0 I4; 0 I 0; 0 0 I4]
  //and glue has block diag form
  //do it manually to understand structure of matrix and
  //to see what's going on...
    cbinv := Zero(MA);
    if not m eq 4 then
        InsertBlock(~cbinv,ReverseRows(Id(GL(m-4,F))),d-m+1,1);
    end if;
    if not d eq m+4 then
        InsertBlock(~cbinv,ReverseRows(Id(GL(d-m-4,F))),5,m+5);
    end if;
    cbinv[1][m+4]   := One(F); cbinv[2][m+2]   := One(F);
    cbinv[3][m]     := One(F); cbinv[4][m-2]   := One(F);
    cbinv[d][m-3]   := One(F); cbinv[d][m-2]   := One(F);
    cbinv[d-1][m-1] := One(F); cbinv[d-1][m]   := One(F);
    cbinv[d-2][m+1] := One(F); cbinv[d-2][m+2] := One(F);
    cbinv[d-3][m+3] := One(F); cbinv[d-3][m+4] := One(F);
    if d-m eq 4 then
      //modify cbinv since e2 in elt is different
        q     := #F;
        cbinv[d-3][d] := elt[d-1][d];
        cbinv[1][d]   := elt[d][d-1]^-1;
    end if;
    cbinv := GL(d,F)!cbinv;
    tmp   := GL(d,F)! cbinv*tmp*cbinv^-1;

  //check whether base change is correct!
  //btmp := BaseChangeInvolution(elt);
  //assert btmp*elt*btmp^-1 eq cbinv*elt*cbinv^-1;
  //btmp := One(MA);
  //btmp[2][2] := Zero(F); btmp[2][3] := One(F);
  //btmp[3][3] := Zero(F); btmp[3][2] := One(F);
  //btmp[d-1][d-1] := Zero(F); btmp[d-1][d-2] := One(F);
  //btmp[d-2][d-2] := Zero(F); btmp[d-2][d-1] := One(F);
  //btmp := GL(d,F)!btmp;
  //assert btmp eq tmp;

    H     := MakeCopyOfInitialisedGroup(G);
    H     := ApplyCOB(H,cbinv*CB);
    g     := cbinv * elt * cbinv^-1;
    C, Cw := MyCentraliserOfInvolution(H,g,wrd,"SX");
  
  //construct fp = [A 0 0;0 I_4 0; 0 0 B] with
  //A,B of odd order and fpf
  //then transform fp to fp=[I4 0 0; 0 C 0; 0 0 I4], C odd order, fpf
  //use this element as formula element to extract [A0*;0I0;00A]
  //with A=SX(2)
  //need notSX because elt is not a good involution and A is
  //reducible!
    if d ge 10 then
        fpel1, fpw1 := FindFPFElForOPlus(G,eltA,wA,CB,"O+",m,"top");
        fpel2, fpw2 := FindFPFElForOMinus(G,eltB,wB,CB,m);
        fw          := fpw1*fpw2;
        fp          := cbinv*fpel1*fpel2*cbinv^-1;
        A,_         := FormulaAB(C, 4, fp, fw, "SX" : 
                                 glue:=true,notSX:=true);
    else
        A           := MakeCopyOfInitialisedGroup(C);
    end if;
 
    new := Zero(MatrixAlgebra(F,8));
    InsertBlock(~new,ExtractBlockNEW(tmp,[1..4]),1,1);
    InsertBlock(~new,ExtractBlockNEW(tmp,[d-3..d]),5,5);
    InsertBlock(~new,ExtractBlock(tmp,1,d-3,4,4),1,5);
    glue := GL(8,F)!new;

    glue, gw  := FindGlueElementOO(A,glue);
    gw        := Evaluate(gw,A`UserWords);
    glue      := cbinv^-1*glue*cbinv;
    eltB[4]   := eltA[4];
    wB[4]     := wA[4];
    eltB[5]   := eltB[5]*glue*eltA[5];
    wB[5]     := wB[5]*gw*wA[5];
    eltB[6]   := eltA[4]*eltA[1];
    wB[6]     := wA[4]*wA[1];
    vprint SXECstdgens,3: "     end Glue for combining degrees",m,d-m;
    return eltB, wB, CB;
end function;




/*********************************************************************/
/* This is a helping function for StandardGeneratorsSXEven
/* It glues the cycles of two sets of standard gens.
/* Input:   matrix group G, list of elts eltA, eltB
/*          and corresponding SLPs wA and wB.
/*          base change CB such that
/*          elt=CB*Eval(w,UserGens(G))*CB^-1.
/*          eltA comes from SX(m,F), and eltB from SX(d-m,F)
/* Output:  standard gens with glued cycle
/*********************************************************************/
OLDGlueCyclesOMinus := function(G,eltA,wA,eltB,wB,CB,type,m)

    d := Degree(G);
    F := BaseRing(G);
    if not IsEven(m) then error "glue:should be even!"; end if;
    vprint SXECstdgens,3: "     find Glue for combining degrees",m,d-m;

  //construct elt with block [A0,0A] at pos m-3
  //where [0100;1000;0001;0010]
    e1  := eltA[4]*eltA[1]; //[0100;1000;0001;0010]
    w1  := wA[4]*wA[1];
    e2  := eltB[6]; //[0100;1000;0001;0010]
    w2  := wB[6];
    c   := eltA[5]; //cycle
    w   := wA[5];
    elt := c^2*e1*c^-2*e2;
    wrd := w^2*w1*w^-2*w2;

  //make base change s.t. elt =[I4 0 I4; 0 I 0; 0 0 I4]
  //do it manually to understand structure of matrix and
  //to see what's going on...
    cbinv := BaseChangeInvolution(elt);
    H     := MakeCopyOfInitialisedGroup(G);
    H     := ApplyCOB(H,cbinv*CB);
    g     := cbinv * elt * cbinv^-1;
    C, Cw := MyCentraliserOfInvolution(H,g,wrd,"SX");



  //construct fp = [A 0 0;0 I_4 0; 0 0 B] with
  //A,B of odd order and fpf
  //then transform fp to fp=[I4 0 0; 0 C 0; 0 0 I4], C odd order, fpf
  //use this element as formula element to extract [A0*;0I0;00A]
  //with A=SX(2)
  //need notSX because elt is not a good involution and A is
  //reducible!
    if d ge 10 then
        fpel1, fpw1 := FindFPFElForOPlus(G,eltA,wA,CB,"O+",m,"top");
        fpel2, fpw2 := FindFPFElForOMinus(G,eltB,wB,CB,m);
        fw          := fpw1*fpw2;
        fp          := cbinv*fpel1*fpel2*cbinv^-1;
        A,_         := FormulaAB(C, 4, fp, fw, "SX" :
                                 glue:=true,notSX:=true);
    else
        A           := MakeCopyOfInitialisedGroup(C);
    end if;

  //construct glue we are looking for in A
    MA  := MatrixAlgebra(F,d);
    tmp := One(MA);
    for i in [m-1,m,m+1,m+2] do tmp[i][i] := 0; end for;
    tmp[m-1][m+1] := 1; tmp[m][m+2] := 1;
    tmp[m+1][m-1]:=1; tmp[m+2][m] :=1;
    tmp := GL(d,F)! cbinv*tmp*cbinv^-1;

  //"check glue";
  //assert tmp*g eq g*tmp;
  //"is cent";
  //_,form := SymplecticForm(H);
  //assert Transpose(tmp)*form*tmp eq form;
  //"satisfies form";
  //"this is form",form;

    new := Zero(MatrixAlgebra(F,8));
    InsertBlock(~new,ExtractBlockNEW(tmp,[1..4]),1,1);
    InsertBlock(~new,ExtractBlockNEW(tmp,[d-3..d]),5,5);
    InsertBlock(~new,ExtractBlock(tmp,1,d-3,4,4),1,5);
    glue := GL(8,F)!new;

    glue, gw  := FindGlueElementOO(A,glue);
    gw        := Evaluate(gw,A`UserWords);
    glue      := cbinv^-1*glue*cbinv;
    eltB[4]   := eltA[4];
    wB[4]     := wA[4];
    eltB[5]   := eltB[5]*glue*eltA[5];
    wB[5]     := wB[5]*gw*wA[5];
    eltB[6]   := eltA[4]*eltA[1];
    wB[6]     := wA[4]*wA[1];
    vprint SXECstdgens,3: "     end Glue for combining degrees",m,d-m;
    return eltB, wB, CB;
end function;



























/*********************************************************************/
/*********************************************************************/
/* 
/* VII. SOME BASE CASE FUNCTIONS  
/*
/*********************************************************************/
/*********************************************************************/




/*********************************************************************/
/* Input:   G=SL(4) and subgroup H=[A*;0B]
/* Output:  glue [0100 1000 0010 0001] in H
/* Idea:    can construct R=[01** 10** 0010 0001] and want
/*          to construct T=[0100 1000 0010 0001]. Therefore
/*          construct S=[10** 01** 0010 0001] with R*S=T
/*********************************************************************/
LinearProblemSL4 := function(G, H)
    
    K    := BaseRing (G);
    type := "SL";

    MyVariations := function (a, wa, b, wb)
        d  := Nrows (a);
        MA := MatrixAlgebra(K, d);
        x  := MA ! a + MA ! b;
        r  := Rank(x);
        if r eq 2 then 
            return true,a*b,wa*wb;  
        else 
            return false,a,wa; 
        end if;
    end function;
  
    repeat 
      //construct h = [01** 10** 0010 0001]
        A, _, WA      := KillFactor(H, [[1,2]], [[3,4]], type);
        A2            := ExtractGroup(A,[1,2] : type := type);
        A2el, A2w, cb := StandardGeneratorsSXEven(A2,type); //changed
        wh            := Evaluate(A2w[1],A`UserWords);
        h             := Evaluate(wh, UserGenerators(G));
       
      //already found glue?
        if Rank(ExtractBlock(h,1,3,2,2)) eq 0 then return h,wh; end if;

      //construct element S of form I  * by squaring R = y         
        if IsInvolution(h) then 
            b, wb := MyRandomWord(A2);
            wb    := Evaluate(wb,A`UserWords);
            ord   := Order(b);
            b     := Evaluate(wb^ord,UserGenerators(G));
            h     := h*b;
            wh    := wh*wb^ord;
        end if;
    until IsInvolution(h^2); //Order(h) eq 4;

  //now y=[IY;0I] is an involution
    y := h^2;
    w := wh^2;
    Y := ExtractBlock(y,1,3,2,2);

  //construct element of corank 2
    B, _, WB := KillFactor(H,[[3,4]],[[1,2]],type);
    while Rank(Y) ne 2 do 
        a, wa := MyRandomWord(A);
        wa    := Evaluate(wa,A`UserWords);
        b, wb := MyRandomWord (B);
        wb    := Evaluate(wb,B`UserWords);
        flag, y, w := MyVariations (y^a, w^wa, y^b, w^wb);
        Y := ExtractBlock(y, 1, 3, 2, 2);
    end while;
     
    k := Degree(K);
    V := VectorSpace(GF(2), 4 * k);

  //obtain basis for V
    I := []; wI := []; basis := [];
    repeat
        a, wa := MyRandomWord (A);
        wa    := Evaluate(wa,A`UserWords);
        v     := y^a;
        S     := sub < V | basis>;
        u     := V! &cat[Eltseq (x): 
                         x in &cat[Eltseq(ExtractBlock(v,1,3,2,2))]];
        if not u in S then 
           Append(~I, a); 
           Append(~wI, wa);
           Append(~basis, u); 
        end if;
    until S eq V;

  //express u as linear combination of basis 
    u := V!&cat[Eltseq(x): x in &cat[Eltseq(ExtractBlock(h,1,3,2,2))]];
    M := MatrixAlgebra (GF(2), 4 * k) ! &cat[Eltseq (x): x in basis];
    flag, coords := IsConsistent(M, u);
    coords  := [Integers ()! x : x in Eltseq (coords)];
    product := &*[(y^I[i])^coords[i]: i in [1..#coords]];
    word    := &*[(w^wI[i])^coords[i]: i in [1..#coords]];

  //this is glue element
    g   := GL(4,K)! [0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1];
    wrd := word*wh;
    return g, wrd;
end function;


/*********************************************************************/
/* Input:   initialsided G=SL(4,2^q) with q > 1
/* Output:  stdGens of G and SLPS, base change
/*********************************************************************/
SolveSL4 := function(G : pos := 0)

    F    := BaseRing(G);
   
    findSecondInvAndCent := function(K,k,wk)
        cb   := BaseChangeInvolution(k);
        L    := ApplyCOB(K,cb);
        i    := cb*k*cb^-1;
        C,Cw := MyCentraliserOfInvolution(L,i,wk,"SL");
        InitialiseGroup(C:UserWords:=Cw, type := "no");
      //find second involution of corank 2 in C
      //and compute centraliser C2; define C := <C,C2>
        blk := ExtractGroup(C, [1..2] : type := "SL");
        repeat 
            h, wh := PullbackInvolution(L,C,[1..2],"SL": block:=blk);
            h     := h^2; 
            wh    := wh^2;
            b     := ExtractBlock(h,1,3,2,2);
            found := IsScalar(b) eq false and Rank(b) eq 2;
        until found;
        C2,C2w := MyCentraliserOfInvolution(L,h,wh,"SL");
        InitialiseGroup(C2 : UserWords := C2w, type := "no");
        ugens := UserGenerators(C) cat UserGenerators(C2);
        uwrds := Cw cat C2w;
      //now C is of type [A*;0B]
        C     := sub<Generic(G)|ugens>;
        C`UserGenerators := ugens;
        InitialiseGroup(C : UserWords:=uwrds, type := "no");
        return L,C,cb;
    end function;

  //find involution g=[II;0I], C=[A*;0B] and A=[A0;0I], B=[I0;0B]
    g,wg   := ConstructInvolutionEvenMain(G,"SL");

    H,C,cb := findSecondInvAndCent(G,g,wg);  
    A,B    := FormulaAB2(C,2,"SL");

    Aex    := ExtractGroup(A,[1..2] : type := "SL");
    Bex    := ExtractGroup(B,[3..4] : type := "SL");

    elA, wA, cbA := StandardGeneratorsSXEven(Aex,"SL"); //changed

//"first group ok, now second";

    elB, wB, cbB := StandardGeneratorsSXEven(Bex,"SL":debug:=true);
    
//"got elts...in solvesl4";	

    id     := Id(GL(2,F));
    elA    := [Generic(A)!DiagonalJoin(a,id):a in elA];
    elB    := [Generic(B)!DiagonalJoin(id,b):b in elB];
    wA     := Evaluate(wA,A`UserWords);
    wB     := Evaluate(wB,B`UserWords);
    cob    := Generic(H)!DiagonalJoin(cbA,cbB)*A`COB ;
    g      := elA[2]*elA[1]*elA[2]*elB[2];
    wg     := wA[2]*wA[1]*wA[2]*wB[2];
    H      := ApplyCOB(H, cob);

  //now find glue element in C and undo base change
    H2,C,cb2 := findSecondInvAndCent(H,g,wg);
    glu,glw  := LinearProblemSL4(H2,C);
    glu      := cb2^-1*glu*cb2;    
    elA[6]   := (elA[1]*glu*elB[1])^3;
    wA[6]    := (wA[1]*glw*wB[1])^3;
    elA[5]   := elA[6]^2;
    wA[5]    := wA[6]^2;
    cb       := cob*cb;
    elA[9]   := elA[2]*elA[2]^elA[5];
    wA[9]    := wA[2]*wA[2]^wA[5];

    

    return elA, wA, cb;
end function;


/*********************************************************************/
/* Helping function for SolveSLSU5
/*********************************************************************/
ObtainBasisSLSU5 := function (G, B, y, V,type : Limit := 3*Degree(V))
 
    K     := BaseRing(G);
  //obtain basis for V 
    I     := [GL(5, K) | ]; 
    wI    := []; 
    basis := [];
    nmr   := 0;
    dim   := Dimension(V);
  //since SU preserves a form, the dimension is half 
    if type eq "SU" then dim := dim div 2; end if;
    repeat
        a, wa := MyRandomWord(B);
        wa    := Evaluate(wa,B`UserWords);
        v     := y^a;
        nmr  +:= 1;
        S     := sub < V | basis>;
        u     := V! ((&cat[Eltseq (x): 
                 x in &cat[Eltseq(ExtractBlock(v,1,2,1,3))]])
                 cat 
                 (&cat[Eltseq (x): 
                 x in &cat[Eltseq(ExtractBlock(v,2,5,3,1))]]));
        if not u in S then 
            Append(~I, a); 
            Append(~wI, wa);
            Append(~basis, u); 
        end if;
        S := sub < V | basis>;   
    until Dimension(S) eq dim or nmr gt Limit;
    if nmr gt Limit then return false,_,_,_; end if;
    if type eq "SU" then
         for i in [1..#basis] do 
             Append(~basis,Zero(V)); 
             Append(~I,I[1]^0);
            Append(~wI,wI[1]^0);
         end for;
    end if;
    M := MatrixRing(GF(2),Degree(V)) ! &cat[Eltseq (x): x in basis];
    return true, M, I, wI;
end function;


/*********************************************************************/
/* Helping function for SolveSLSU5
/*********************************************************************/
LinearProblemSLSU5 := function (G, B, type)
    K   := BaseRing(G);
    k   := Degree (K);
    V   := VectorSpace(GF(2),6*k);
    nmr := 0;
    blk := ExtractGroup(B, [2..4] : type := type);
    repeat
        repeat 
          //construct element [I**;0I*;00I] by squaring y 
            if type eq "SL" or (type eq "SU" and #K ge 4097) then

                y, w := PullbackInvolution(G,B,[2..4],type:
                                        SmallerCorank := true,
                                        block         := blk);
                y := y^(2); w := w^2;
            else

                y,w := MyRandomWord(B);
                o   := Order(ExtractBlockNEW(y,[2..4]) : Proof := false)
                       ;
                       //*Order(y[1][1])*Order(y[5][5]);
                w   := Evaluate(w,B`UserWords);
                y   := Generic(G)!y^o;
                w   := w^o;

              //y,w := MyRandomWord(blk);
              //o   := Order(y : Proof := false);
              //w   := Evaluate(w,B`UserWords);
              //y   := B`COB*Evaluate(w,UserGenerators(G))*B`COB^-1;
              //y   := Generic(G)!y^o;
              //w   := w^o;

            end if;
            X   := ExtractBlock(y,1,2,1,3);
            Y   := ExtractBlock(y,2,5,3,1);
         //"here we are...", y,o,Rank(X), Rank(Y);
        until Rank (X) gt 0 and Rank (Y) gt 0;
     //find spanning basis for V consisting of conjugates of y
        flg, M, I, wI := ObtainBasisSLSU5(G, B, y, V, type);
        nmr := nmr + 1;
    until flg or nmr ge 5;
    if nmr ge 5 then error "could not obtain basis SLSU5"; end if;
    U        := UserGenerators(B);
    W        := B`UserWords;
    New      := []; 
    Word     := [];
    for i in [1..#U] do 
        hold  := U[i];
        whold := W[i];
        bb    := ExtractBlock(hold, 2,2,3,3);
        u     := V!((&cat[Eltseq(x): x in 
                 &cat[Eltseq(ExtractBlock (hold,1,2,1,3))]]) cat 
                 (&cat[Eltseq(x): x in 
                 &cat[Eltseq(bb^-1*ExtractBlock(hold,2,5,3,1))]]));
        flag, coords := IsConsistent(M, u);
        assert flag;
        coords       := [Integers ()! x : x in Eltseq (coords)];
        product      := &*[(y^I[i])^coords[i]: i in [1..#coords]];
        wproduct     := &*[(w^wI[i])^coords[i]: i in [1..#coords]];
      //now hold*product has both above-diagonal blocks cleared out
        New[i]  := hold * product;
        Word[i] := whold * wproduct;
    end for;
    return New, Word;
end function;


/*********************************************************************/
/* Input:   initialised group G=SU(5,2^q) or SL(5,2^q) (in std form)
/* Output:  stdGens of G and SLPS, base change matrix
/*********************************************************************/
SolveSLSU5 := function(G, type)
 

  //G:=MyConjugateToStandardCopy(makeSXEC(5,4,"SU"),"SU");
  //construct SX4 as subgroup and stdgens for SX4
    F            := BaseRing(G);
    H, rank, COB := ConstructSmallerSXEC(G, [4], type);
    K            := ExtractGroup(H, [1..4] : type := type);

  //bring everything to standard form
    if type eq "SU" then
        Knew, basf   := MyConjugateToStandardCopy(K,"SU");
        M            := MatrixAlgebra(F, 5);
        B            := Identity(M);
        InsertBlock (~B, basf, 1, 1);
        COB          := B*COB;
        K            := ApplyCOB(K,basf);
        fl, tmp      := UnitaryForm(ApplyCOB(G,COB));
        fl, i        := IsSquare(tmp[5][5]^-1);
        B            := Identity(M);
        B[5][5]      := i;
        COB          := B*COB;
    end if;  

  //"this is group",UnitaryForm(K);

    A,WA,CA := StandardGeneratorsSXEven(K,type:pos:="top"); 

  //Kttt := ApplyCOB(K,CA);
  //"new group",UnitaryForm(Kttt);
  //"but this is CA",CA;

  //"got this",A,CA;
  //assert A eq [CA*Evaluate(w,UserGenerators(K))*CA^-1 : w in WA]; 
  //"ok";

    WA      := Evaluate(WA,K`UserWords);
    A       := [Generic(G)!DiagonalJoin(a,Id(GL(1,F))):a in A];

    if type eq "SU" then 
        assert CA eq CA^0;
        cb := COB; 
    else
        M  := MatrixAlgebra(F, 5);
        B  := Identity(M);
        InsertBlock (~B, CA, 1, 1);
        cb := B*COB;
    end if;


  //now centraliser of involution [110;010;00I]  
    I  := A[2];
    I  := Generic(G)!(cb^-1*I*cb);
    wI := WA[2];

  //centraliser contains SX3
    C, Cw := MyCentraliserOfInvolution(G, I, wI, type);
    InitialiseGroup(C : UserWords := Cw, type := "no");
  //Now C has the type [**;0*]
    C     := ApplyCOB(C, cb);

    V    := VectorSpace (F, 5);
    Brow := [V.1, V.3, V.4, V.5, V.2];
    CR   := GL(5, F) ! &cat[Eltseq(v): v in Brow];
    
    D    := MyDerivedSubgroupWithWords(C); 
 
  //Now D has type [1**;0**;001]
    D    := ApplyCOB(D, CR);

  //now clean up D to obtain SX3 as subgroup of G
  //that is, gens are of type [100;0*0;001]
    gens, W := LinearProblemSLSU5(G, D, type);
    gens    := [x^2: x in gens];
    W       := [w^2: w in W];

  //SX3 as subgroup of SX5
    D := sub<Generic(G) | gens>;
    D`UserGenerators  := gens;
    InitialiseGroup(D : UserWords := W);

  //solve SU3
    K           := ExtractGroup(D, [2..4] : type := type);
    K`UserWords := W;
   
    if type eq "SU" then
        flag, form  := UnitaryForm(K); 
        f           := form[3][3];
        assert f eq 1;
      //if not f eq f^0 then
      //    flg, i    := IsSquare(f^-1);
      //    bas       := MatrixAlgebra(BaseRing(G),3)!Id(K);
      //    bas[3][3] := i;
      //    bas       := Generic(K)!bas;
      //    K         := ApplyCOB(K,bas);
      //    tmp       := Id(M);
      //    InsertBlock(~tmp,bas,2,2);
      //    bas       := tmp;
      //    "test form"; assert bas eq bas^0;
      //else
      //    bas       := Id(M);
      //end if;
    end if;

  //reduce number of generators in smaller copy
    newugens := [];
    newuw    := [];
    i        := 1;
    repeat
        Append(~newugens,UserGenerators(K)[i]);
        Append(~newuw,K`UserWords[i]);
        i := i+1;
        t := WhichType(sub<Generic(K)|newugens>);
    until t cmpeq "SU" or t cmpeq "SL";
    K`UserGenerators := newugens;
    K`SLPGroup       := SLPGroup(#newugens);
    K`UserWords      := newuw;
 
    B, WB, CB   := StandardGeneratorsSXEven(K,type:pos:="top");
    WB          := Evaluate(WB,K`UserWords); 

    assert CB eq CB^0;   
  //cb := bas*cb;

  //contruct cycle and bottom generators
    M      := MatrixAlgebra(F, 5);
    b      := Identity(M);
    InsertBlock(~b,B[5],3,3);
    A[5]   := b*A[5];
    WA[5]  := WB[5]*WA[5];
    A[9]   := A[2]*A[2]^A[5];
    WA[9]  := WA[2]*WA[2]^WA[5];
    if type eq "SU" then
        b      := Identity(M);
        InsertBlock(~b,B[6],3,3);
        A[6]   := b;
        WA[6]  := WB[6]; 
        b      := Identity(M);
        InsertBlock(~b,B[7],3,3);
        A[7]   := b;
        WA[7]  := WB[7];    
    end if;

    return A, WA, cb;
end function;






/*********************************************************************/
/* Input:   initialised G=Sp(6,2^q) in stdform
/* Output:  stdGens of G and SLPS, base change
/*********************************************************************/
SolveSp6 := function(G,pos)

    cput    := Cputime();
    F       := BaseRing(G);
    A,B,m   := TwoSXECSp6(G); 
    SA      := ExtractGroup(A,[1..m] : type := A`type);
    SB      := ExtractGroup(B,[m+1..6] : type := B`type);
    idA     := Identity(SA);
    idB     := Identity(SB);

    eltA, wA, CBA := StandardGeneratorsSXEven(SA,"SL":pos:=pos);
    eltB, wB, CBB := StandardGeneratorsSXEven(SB,"O+":pos:="bottom");

    eltA  := [Generic(G)!DiagonalJoin(a,idB): a in eltA];
    eltB  := [Generic(G)!DiagonalJoin(idA,b): b in eltB];
    CBn   := Generic(G)!DiagonalJoin(CBA,CBB);
    wA    := Evaluate(wA,SA`UserWords);
    wB    := Evaluate(wB,SB`UserWords);
    CB    := CBn*A`COB; //note that A`COB = B`COB

    glue  := Generic(G)![0,0,1,0,0,0, 0,0,0,1,0,0, 1,0,0,0,0,0, 
                         0,1,0,0,0,0, 0,0,0,0,1,0, 0,0,0,0,0,1];
    elt   := eltA[1]*eltB[1]*eltB[4];
    wrd   := wA[1]*wB[1]*wB[4];
 
    bc    := BaseChangeInvolution(elt);
    elt   := bc*elt*bc^-1;
    glue  := bc*glue*bc^-1;
    H     := ApplyCOB(G,bc*CB);
    C,Cw  := MyCentraliserOfInvolution(H,elt,wrd,"SpO");
    InitialiseGroup(C : UserWords := Cw, type := "no");
 
    ugnew := [Generic(C)!u : u in UserGenerators(C)];
    ug    := [Generic(C)!u : u in UserGenerators(C)];
    Cc    := MakeCopyOfInitialisedGroup(C);
    
  //T     := CompositionTree(Cc);  
  //"new CT 7";
  //T   := CompositionTree(Cc : LeafPriorities := [1,2,3,4,5]); 
    T   := CompositionTree(Cc : LeafPriorities := [5,4,3,2,1]); 
    flG,w := CompositionTreeElementToWord(Cc,glue);
   
    if not flG then
      //if this fails, then A=[SX(4)0*; 0I0; 00SX(4)] does 
      //not have the full group [SX(4)00;0I0;00SX(4)] as subgrp
        error "Sp6:unfortunately we couldn't find glue element";
    end if;

  //pull back to element in A
    pos   := [Position(ugnew,Cc.i):i in [1..Ngens(Cc)]]; 
    map   := CompositionTreeNiceToUser(Cc);
    w     := Image(map,w);
    glue  := Generic(G)![0,0,1,0,0,0, 0,0,0,1,0,0, 1,0,0,0,0,0, 
                         0,1,0,0,0,0, 0,0,0,0,1,0, 0,0,0,0,0,1];

    vprint SXECcpu,1:"CPU time CompTree for glue Sp6 :",
                        Cputime(cput);
    w     := Evaluate(w,[C`SLPGroup.i : i in pos]);
    w     := Evaluate(w, C`UserWords);

    eltA[5] := eltB[5]*glue*eltA[5];
    wA[5]   := wB[5]*w*wA[5];
    eltA[4] := eltA[5]*eltB[4]*eltA[5]^-1;
    wA[4]   := wA[5]*wB[4]*wA[5]^-1;
    eltA[6] := eltA[5]*eltB[2]^eltB[1]*eltA[5]^-1;
    wA[6]   := wA[5]*wB[2]^wB[1]*wA[5]^-1;
    eltA[8] := eltA[1]*eltA[1]^eltA[5];
    wA[8]   := wA[1]*wA[1]^wA[5];

    return wA,CB;
end function;


/*********************************************************************/
/* Input:   Initialised G=OmegaPlus(6,2^q) in stdform
/* Output:  stdGens of G and SLPS, base change
/*********************************************************************/
SolveOp6 := function(G,pos)

    cput  := Cputime();
    F     := BaseRing(G);
    elt   := StandardGeneratorElements(F,6,"O+"); 
    H     := MakeCopyOfInitialisedGroup(G);
    ugH   := [Generic(H)!u : u in UserGenerators(H)];
    // f, K  := RecogniseAlternatingSquare(H);
    f, K  := RecogniseSmallDegree(H, "SL", 4, #F);
    assert f;
    // toDo  := [AlternatingSquarePreimage(H,e):e in elt];
    toDo  := [x where _,x := SmallDegreePreimage(H,e):e in elt];
    // K`UserGenerators := [Generic(K)!
    //                     AlternatingSquarePreimage(H,e):e in ugH];
    K`UserGenerators := [Generic(K)! k where _, k :=
                         SmallDegreePreimage(H,e):e in ugH];
    InitialiseGroup(K : type := "SL");
    ug    := [Generic(K)!u : u in UserGenerators(K)];
    Kc    := MakeCopyOfInitialisedGroup(K);
  //T     := CompositionTree(Kc); 
  //"new CT 8";
  //"call CT to this group",Kc;
    T   := CompositionTree(Kc:LeafPriorities:=[5,4,3,2,1]);// : LeafPriorities := [1,2,3,4,5]);
    wrds  := [];
    for e in toDo do
        flG,w := CompositionTreeElementToWord(Kc,e);
        assert flG;
        Append(~wrds,w);
    end for;
  //pull back to element in H
    pos   := [Position(ug,Kc.i):i in [1..Ngens(Kc)]];
    map   := CompositionTreeNiceToUser(Kc);
    wrds  := [Image(map,w):w in wrds];
    vprint SXECcpu,1:"CPU time CompTree for SL4 in SolveSp6:",
                        Cputime(cput);
 
    wrds  := Evaluate(wrds,[K`SLPGroup.i : i in pos]);
    return wrds, Id(G);
end function;


/*********************************************************************/
/* Input:   Initialised G=OmegaMinus(6,2^q) in stdform
/* Output:  StdGens of G and SLPS, base change
/*********************************************************************/
SolveOm6 := function(G,pos)
    



    cput     := Cputime();
    F        := BaseRing(G);
    q        := #F;
  //note that G is standard copy!
  //we use that OmegaMinus(6,q) = ExtSquare(SU(4,q))
    stdGens  := StandardGeneratorElements(F,6,"O-");

  //write Ugens of G as Ugens for SU(4) so that words SU <-> words O-
    su       := SU(4,#F);
    suex     := ExteriorSquare(su);    
    _,suexsf := IsOverSmallerField(suex);
    InitialiseGroup(suexsf : type := "O-");
    t,cbmod  := MyConjugateToStandardCopy(suexsf,"O-");
    cbmod    := cbmod^-1;  
  
  //"quadforms",QuadraticForm(G),QuadraticForm(suexsf);

 
  //base change matrices
    cbmod    := GL(6,q^2)!cbmod;
    cbmodinv := cbmod^-1;
    cbsf     := suexsf`SmallerFieldChangeOfBasis;
    cbsf     := GL(6,q^2)!cbsf;
    cbsfinv  := cbsf^-1;
 
  //mappings  G <--> suex
    fromG2SUex := function(g)
        h := GL(6,q^2)!g;
        return cbsf*cbmod*h*cbmodinv*cbsfinv;
    end function;
    fromSUex2G := function(g)
        h := GL(6,q)!cbsfinv*g*cbsf; 
        return cbmod^-1*h*cbmodinv;
    end function;
    
    ug   := [fromG2SUex(g) : g in UserGenerators(G)];
    toDo := [fromG2SUex(g) : g in stdGens];

  //find preimage of g in suex in su
    P<a11,a12,a13,a14,a21,a22,a23,a24,a31,a32,a33,a34,a41,a42,a43,a44> 
         := PolynomialRing(BaseRing(suex),16);
    gP   := [[a11,a12,a13,a14],[a21,a22,a23,a24],
             [a31,a32,a33,a34],[a41,a42,a43,a44]];
    ord  := [[2,1],[3,1],[3,2],[4,1],[4,2],[4,3]];
    I    := [**];
    for i in ord do
        for j in ord do
            Append(~I,gP[i[1]][j[1]]*gP[i[2]][j[2]]+
                      gP[i[1]][j[2]]*gP[i[2]][j[1]]);
        end for;
    end for;

    fromSUex2SU := function(g)
        elt := Eltseq(g);
        J   := [];
        for i in [1..#elt] do Append(~J,I[i]+elt[i]); end for;
        J   := ideal<P|J>;
        Groebner(J);
        mat := Generic(su)![h : h in Variety(J)[1]];
        return mat;
    end function;

    ug   := [fromSUex2SU(g) : g in ug];
    toDo := [fromSUex2SU(g) : g in toDo];
 
    su`UserGenerators := ug;
    InitialiseGroup(su);
    
  //now call CT or RecogniseSU4
    ug  := [Generic(su)!u : u in UserGenerators(su)];
    H   := MakeCopyOfInitialisedGroup(su);
 
    vprint SXECcpu,2:"CPU time O-(6) Groebner bases:",Cputime(cput); 

    mapIt := function(m,els)
        wrds := [];
        idw  := m(els[1]^0)^0;
        for e in els do
            if e eq Id(H) then 
                Append(~wrds,idw); 
            else 
                Append(~wrds,m(e)); 
            end if;
        end for;
        return wrds, [Position(ug,H.i) : i in [1..Ngens(H)]];
    end function;

    recSU4 := true;
    if recSU4 then
        vprint SXECstdgens, 3: "      start recogniseSU for O-(6)";

          flag := false; 
          fcnt := 1;    
          while not flag or fcnt lt 4 do
             flag,_,_,m1,m2 := RecogniseSU4(H,Isqrt(#BaseRing(H)));
             fcnt := fcnt + 1;    
          end while;


      //f,_,_,m1,m2  := RecogniseSU4(H, Isqrt(#BaseRing(H)));
        if not flag then 
            H:Magma; error "RecogniseSU4 for O-(6) failed"; 
        end if;
        vprint SXECstdgens, 3: "      end recogniseSU for O-(6)";
      //"this is map",m1;
      //"recsu4, apply map";
        w, pos := mapIt(m1,toDo);
      //"done, now evaluate";
        w      := Evaluate(w,[su`SLPGroup.i : i in pos]);
      //"done";
         vprint SXECcpu,1:"CPU time RecSU4 for O-(6):",
                          Cputime(cput);
    else   
        vprint SXECstdgens, 3: "      start CompTree within O-(6)";
        prior := [i : i in [19 .. 1 by -1]];
        for i in [16..18] do prior[i] := 0; end for;
      //T   := CompositionTree(H : Priorities := prior);
      //"new CT 9";
      //T   := CompositionTree(H : Priorities := prior, LeafPriorities := [1,2,3,4,5]);
        T   := CompositionTree(H : Priorities := prior, LeafPriorities := [5,4,3,2,1]);
        w   := [];
        _,id := CompositionTreeElementToWord(H,Id(H));
        id   := id ^0;
        for e in toDo do
            if not e eq Id(H) then
                flg, wtmp := CompositionTreeElementToWord(H,e);
                assert flg;
                Append(~w,wtmp);
            else 
                Append(~w,id); 
            end if;
        end for;
        map := CompositionTreeNiceToUser(H);
      //"this is map",map;
      //"comptree, apply map";
        w   := [Image(map,e) : e in w];
      //"done, now evaluate";
        pos := [Position(ug,H.i) : i in [1..Ngens(H)]]; 
        w   := Evaluate(w,[su`SLPGroup.i : i in pos]);
      //"done";
        vprint SXECstdgens, 3: "      end CompTree within O-(6)";
        vprint SXECcpu,1:"CPU time CompTree SU4 for O-(6):",
                          Cputime(cput);
    end if;
    return w, Id(G);
end function;




/*********************************************************************/
/*********************************************************************/
/*
/*  VIII. CONSTRUCT STANDARD GENERATORS
/*
/*********************************************************************/
/*********************************************************************/




/*********************************************************************/
/* Prelim. function for RewriteToEOBStandardGenerators
/*********************************************************************/
SLNewBasis := function (H, B)
    F := BaseRing (H);
    d := Degree (H);
    V := VectorSpace (F, d);

    depth := [Depth (B[i]): i in [1..Nrows (B)]];
    Sign := [];
    for i in [1..#depth] do   
        Sign[i] := B[i][depth[i]] eq 1 select 1 else -1;
    end for;
    D := [Sign[i] * depth[i] : i in [1..#depth]]; 
    X := [];
    previous := 1;
    for i in [1..d] do
        X[i] := previous;
        if previous gt 0 then
            previous := -D[previous];
        else
            previous := D[-previous]; 
        end if;
    end for;
    Y := [];
    for i in [1..d] do
        if X[i] gt 0 then
            Y[i] := V.X[i];
        else
            Y[i] := -V.-X[i];
        end if;
    end for;
    N := &cat [Eltseq (v): v in Y];
    return GL(d, F) ! N;
end function;


/*********************************************************************/
/* Input:   input/output of StandardGeneratorsClassicalSXEven, type
/* Output:  standard generators as defined by 
/*          mgrp/classical/recognition/standard.m
/*          corresponding SLPs and change of base matrix
/*********************************************************************/
RewriteToEOBStandardGenerators := function(G,E,W,CB,type)
    d := Degree(G);
    if type eq "SL" then
         cb := CB^0;
         if d eq 2 then y := E[1]; w := W[1];
         elif d eq 3 then y := E[1]*E[5];  w := W[1]*W[5];
         elif d eq 4 then y := E[6]^-1; w := W[6]^-1;
         else
             x  := (E[5] * E[6])^-1;
             cb := SLNewBasis(G, x);
             y  := cb * x^-1 * cb^-1;
             w  := W[5] * W[6];
         end if;
         
         return [E[1], y, E[2], E[3]], [W[1],w,W[2],W[3]], cb*CB;
    elif type eq "SU" then
        if IsEven (d) and d gt 4 then
            x := E[5]^(d - 2);
            E[6] := E[6]^x;
            W[6] := W[6]^(W[5]^(d-2));
            E[7] := E[7]^x;
            W[7] := W[7]^(W[5]^(d-2));
            index := [1,5,2,3,4,6,7];
        elif d eq 3 and #BaseRing (G) eq 4 then
            E[4] := E[2]^2;
            W[4] := W[2]^2;
            index := [1,3,4,2,3,6,7];
        else
            index := [1,5,2,3,4,6,7];
        end if;
        return [E[i]: i in index], [W[i]: i in index], CB;
    elif type eq "Sp" then
        E[6] := E[6]^(E[5]^(d-2));
        W[6] := W[6]^(W[5]^(d-2));
        index := [1,5,2,3,4,6];
        return [E[i]: i in index], [W[i]: i in index], CB;
    elif type eq "O+" then
        index := [1,2,3,4,6,7,8,5];
        return [E[i]: i in index], [W[i]: i in index], CB;
    elif type eq "O-" then
        index := [1,2,3,4,5];
        return [E[i]: i in index], [W[i]: i in index], CB;
    end if;
end function;


/*********************************************************************/
/* Input:   classical group G=SX(d,2^n) in nat pres and char 2, type 
/* Output:  sdtgens, SLPs, base change
/* Internal Option: pos in {"top","bottom"} indicates 
/*                  whether all gens have to be constructed 
/*********************************************************************/
StandardGeneratorsSXEven := function(G, type : pos := 0, debug:=false)
    d     := Degree(G);
    F     := BaseRing(G);
    vprint SXECstdgens,1: "start StandardGensEven in degree", d;
 
    vprint SXECstdgens,1: "   HD -- nat rep call standardGeneratorsSXEven", type, Degree(G);


    if pos cmpeq 0 then 
        firstCall := true; 
        pos       := "top";
    else 
        firstCall := false; 
    end if;

  //do small degrees / cases directly   
  //note that there is no reduction to SU(9,2) but we have to 
  //handle SU(9,2) separately
    sml := type eq "SU" and #F eq 4 and d in [6,7,9];
    sml := sml or (G`type eq "SL" and #F eq 2 and d in [6,8]);
    if d le 5 or sml 
            or (G`type in ["Sp","O+","O-"] and d eq 6) 
            or (G`type eq "O-" and #F eq 4 and d in [8,10]) 
            or (#F eq 2 and d le 12 and G`type in ["Sp","O+","O-"])
          //can't reduce to OmegaPM(2,6):
            or (#F eq 2 and d eq 14 and G`type in ["O+","O-"])  then

        if firstCall then
            a,b,c := StandardGensSmallDegree(G,G`type : 
                                             posBl := "first",debug:=debug);
            Prune(~a); Prune(~b);
        else
            a,b,c := StandardGensSmallDegree(G,G`type : posBl:=pos);
        end if;      

        vprint SXECstdgens,1:"end StandardGensEven in degree", d;
      //"test small ",d,type;
      // if not a eq [c*Evaluate(w,UserGenerators(G))*c^-1 : w in b] then
      //     "ev was wrong!";
      //     "should be",a;
      //     "is",[c*Evaluate(w,UserGenerators(G))*c^-1 : w in b];
      //     "input was this group",G:Magma;
      //     assert 1 eq 2;
      //end if;
         return a,b,c;
    end if;

  //Construct top block and std gens recursively
    rank := SelectRanks(d,BaseRing(G),G`type);
    A, m := ConstructSmallerSXEC(G,rank,type); 
    SA   := ExtractGroup(A,[1..m] : type := A`type);
    idA  := Identity(SA);
    idB  := ExtractBlockNEW(Id(G),[1..d-m]);

  //bring it in standard form
    if not A`type eq "SL" then
        K,bas         := MyConjugateToStandardCopy(SA,A`type);
        bas           := Generic(G)!DiagonalJoin(bas,idB);
        A             := ApplyCOB(A,bas);
    end if;

    SA  := ExtractGroup(A,[1..m] : type := A`type);
    if type eq "Sp" then
        eltA, wA, CBA := $$(SA,type:pos := "bottom");
    else
        eltA, wA, CBA := $$(SA,type:pos := pos);
    end if;
   
    eltA          := [Generic(G)!DiagonalJoin(a,idB): a in eltA];
    wAold         := wA;
    wA            := Evaluate(wA,SA`UserWords);
    CBn           := Generic(G)!DiagonalJoin(CBA,idB);
    CBA           := Generic(G)!DiagonalJoin(CBA,idB);
    CB            := CBn*A`COB;

  //"now test first"; assert [CB*i*CB^-1 : i in Evaluate(wA,UserGenerators(G))] eq eltA;


  //check if direct inv is the same!
  //assert inv eq eltA[9];
    inv     := eltA[9];
    winvold := wAold[9];
    winv    := wA[9];

  //Bring involution in standard form and use TwoSXEC
    ICOB := BaseChangeInvolution(ExtractBlockNEW(inv,[1..m]));
    ICOB := Generic(G)!DiagonalJoin(ICOB,idB);
    A    := ApplyCOB(A,ICOB*CBA);
    inv  := ICOB*inv*ICOB^-1;
    A,B  := TwoSXEC(G,A,inv,winvold,winv,m,type);

    if not assigned A`type or not assigned B`type then
        vprint SXECstdgens,1: "degrees were",m,d-m;
        IsOrthogonalGroup(ExtractGroup(A,[1..m]));
        IsOrthogonalGroup(ExtractGroup(B,[m+1..d]));
        error "Type was not detected correctly; OmegaPlus problem (?)";
    end if;


  //now compute std gens in the second copy - 
  //do we have to switch the groups?
  //This happens when type is Sp and A has type O+
    if G`type in ["Sp"] then
        A    := ApplyCOB(A,CBA^-1*ICOB^-1);
        B    := ApplyCOB(B,CBA^-1*ICOB^-1);
        B, A := AdjustFormsOfTwoSXEC(G,A,B,m);
       
      //compute std gens
        SB   := ExtractGroup(B,[m+1..d] : type := B`type);
        eltB, wB, CBB := $$(SB,type:pos := pos);

        eltB := [Generic(G)!DiagonalJoin(idA,b): b in eltB];
        wB   := Evaluate(wB,SB`UserWords);
        CBB  := Generic(G)!DiagonalJoin(idA,CBB);
        CB   := CBA*CBB*B`COB;
        
      //swap blocks
        idm  := Id(GL(m,F));
        idmd := Id(GL(d-m,F));
        cbSp := Zero(MatrixAlgebra(F,d));
	InsertBlock(~cbSp,idm,d-m+1,1);
        InsertBlock(~cbSp,idmd,1,m+1);
        cbSp := GL(d,F)!cbSp;
        A    := ApplyCOB(A,cbSp);
        B    := ApplyCOB(B,cbSp);
        m    := d-m;
	tmp  := MakeCopyOfInitialisedGroup(B);
        B    := MakeCopyOfInitialisedGroup(A);
	A    := MakeCopyOfInitialisedGroup(tmp);
        eltA := [cbSp*i*cbSp^-1 : i in eltA];
        eltB := [cbSp*i*cbSp^-1 : i in eltB];
        tmp  := eltA;
        eltA := eltB;
        eltB := tmp;
        tmp  := wA; 
	wA   := wB;
        wB   := tmp;
        CB   := cbSp*CB;
 
    else

        A    := ApplyCOB(A,CBA^-1*ICOB^-1);
        B    := ApplyCOB(B,CBA^-1*ICOB^-1);

        if not type eq "SL" then
            B, A := AdjustFormsOfTwoSXEC(G,A,B,m);
        end if;

      //compute std gens in second block
        SB    := ExtractGroup(B,[m+1..d] : type := B`type);
        eltB, wB, CBB := $$(SB,type:pos := "bottom");
        eltB  := [Generic(G)!DiagonalJoin(idA,b): b in eltB];
        wB    := Evaluate(wB,SB`UserWords);
        CBB   := Generic(G)!DiagonalJoin(idA,CBB);
        CB    := CBA*CBB*B`COB;

    end if; 




  //base change (scalar) to adjust form 
    if not type eq "SL" then 
        Gtmp   := ApplyCOB(G,CB);       
        if type eq "SU" then _,form := UnitaryForm(Gtmp);
        else _,form := SymplecticForm(Gtmp);
        end if; 
        f    := form[m+1][m+2];
        if not f eq f^0 then
            flg, i := IsSquare(f^-1);
            bas    := MatrixAlgebra(BaseRing(G),d)!Id(G);
            for j in [m+1..d] do bas[j][j]:=i; end for;
            bas    := Generic(G)!bas;
            CB     := bas*CB;
        end if;
    end if;

   //"now test second"; assert [CB*i*CB^-1 : i in Evaluate(wB,UserGenerators(G))] eq eltB;
   
   //"before glue";assert [CB*i*CB^-1 : i in Evaluate(wA,UserGenerators(G))] eq eltA;

  //now glue the cycles
    if type in ["SL","SU"] then
        eltA,wA,CB := GlueCycles(G,eltA,wA,eltB,wB,CB,type,m);
    elif SA`type eq "O+" and SB`type eq "O-" then
        eltA,wA,CB := GlueCyclesOMinus(G,eltA,wA,eltB,wB,CB,A`type,m);
    else //have "Sp" and "O+", or "O+" and "O+"
        eltA,wA,CB := GlueCyclesOPlus(G,eltA,wA,eltB,wB,CB,A`type,m);
    end if;

  //"after glue";assert [CB*i*CB^-1 : i in Evaluate(wA,UserGenerators(G))] eq eltA;



  //if type=SU and degree of is odd
  //then copy bottom elements x and y of eltB to eltA
    if type eq "SU" and IsOdd(Degree(SB)) then
        eltA[6] := eltB[6]; wA[6] := wB[6];
        eltA[7] := eltB[7]; wA[7] := wB[7];
    end if;
    vprint SXECstdgens,1: "end StandardGensEvenChar in degree", d;
 
  //If first call:
  //delete prelim. element for OmegaMinus as corresp. SLP is wrong
  //otherwise, delete temporary involution
  //If not first call: store new involution of large corank
    if firstCall then  
        Prune(~eltA); Prune(~wA); 
    elif not B`type eq "O-" then
        eltA[9] := eltA[9]*eltB[9];
        wA[9]   := wA[9]*wB[9];
    end if;

  a := eltA;
  b := wA;
  c := CB;
 //"std test end",d,type;
 //if not  a eq [c*Evaluate(w,UserGenerators(G))*c^-1 : w in b] then
 //    "ev was wrong!";
 //    "should be",a;
 //    "is",[c*Evaluate(w,UserGenerators(G))*c^-1 : w in b];
 //    "input was this group",G:Magma;
 //    assert 1 eq 2;
 //end if;

    return eltA,wA,CB;
end function;


/*********************************************************************/
/* Input:    finite classical matrix group in nat rep and char 2
/* Output:   sdtgens elts (EOB), SLPs wrds, base change CB
/* Optional: type is one of "SL", "SU", "Sp", "O+", "O-"
/*********************************************************************/
SolveClassicalEven := function(G : type := false, rewriteToEOB := true)


   vprint SXECstdgens,1: "HD -- CALL NAT REP SolveClassicalEven for", type, Degree(G);

  //check if the input is valid
    if not Type(G) eq GrpMat then
        error "group must be finite class. matrix group in nat rep";
    end if;
    d := Degree(G);
    F := BaseRing(G);
    if d eq 1 then error "degree must be greater than 1"; end if;
    if not IsFinite(F) or not #F mod 2 eq 0 then          
        error "field must be finite of characteristic 2";
    end if;
   //determine the type (if not given)
    if not type cmpeq false then
        if not type in ["SL", "Sp", "SU", "O+", "O-"] then
            error "illegal type";
        end if;
    else
        type := WhichType(G);
        if type cmpeq false then 
            error "SolveClassicalEven: cannot determine type"; 
        end if;
    end if;

    if d eq 2 and type in ["O+","O-"] then
        error "degree for Sp, O+, and O- must be at least 4";
    end if;

  //make sure the group will have the correct flags
    if assigned G`RandomProcess then delete G`RandomProcess; end if;
    if assigned G`SLPGroup then delete G`SLPGroup; end if;
    if assigned G`COB then delete G`COB; end if;
    if assigned G`UserWords then delete G`UserWords; end if;
    if assigned G`initialised then delete G`initialised; end if;

  //initialise group and start computation
    InitialiseGroup(G : type := type);
    E, W, CB := StandardGeneratorsSXEven(G, type);

  //"nat rep, test deg",d;
  //assert [CB^-1*i*CB : i in E] eq Evaluate(W,UserGenerators(G));
  
    if not assigned G`type then G`type := WhichType(G); end if;
    if rewriteToEOB then
        return RewriteToEOBStandardGenerators(G,E,W,CB,G`type);
    else
        return E,W,CB;
    end if;
end function;

