/* TESTING FUNCTIONS
/*******************
/*  There are two testing functions:
/*    (1) SXECtestInv:   testing the construction of an involution
/*    (2) SXECtestStdGens:   testing the construction of std gens
/*  Please see below for input and options
/*
/*  The function makeSXEC(n,q,type) returns a RandomConjugate of SX(n,q)
/*  with random UserGenerators.
/*
/*  The function "quickTestEOBGens" (at the bottom of this file) does
/*  some small checks and tests whether the result of SolveClassicalEven
/*  is correct (compared with /recognition/standard.m).
***********************************************************************/

import "StdGensEvenSX.m": InitialiseGroup, MyRandomWord, Corank, 
StandardGeneratorElements, SolveClassicalEven, StandardGenerators;


/*********************************************************************/
/* Input:  degree d, 2-power F, type SX
/* Output: random conjugate of SX(d,GF(F)) with random UserGens
/*********************************************************************/
makeSXEC := function(d,F,type)
    if   type eq "SL" then G := RandomConjugate(SL(d,F));
    elif type eq "SU" then G := RandomConjugate(SU(d,F));
    elif type eq "O+" and IsEven(d) then 
        G := RandomConjugate(OmegaPlus(d,F));
    elif type eq "O-" and IsEven(d) then 
        G := RandomConjugate(OmegaMinus(d,F));
    elif type eq "Sp"and IsEven(d)  then 
        G := RandomConjugate(Sp(d,F));
    else error "makeSXEC: wrong type or degree"; end if;

    if type eq "O+" and d eq 2 and F eq 2 then
        error "OmegaPlus(2,2) is trivial";
    end if;

  //to have a random process  
    InitialiseGroup(G : type:=type);
    gens := [Generic(G)|MyRandomWord(G:onlyElt:=true)];
    for i in [1..Random([3..5])+Ngens(G)] do
       g := Generic(G)!MyRandomWord(G:onlyElt:=true);
       Append(~gens,g); 
    end for; 
   
  //ensure that gen set is subset of gens
    pos := [];
    repeat 
        i := Random([1..#gens]);
        if not i in pos then Append(~pos,i); end if;
    until #pos eq Ngens(G);
    for j in [1..Ngens(G)] do 
        gens[pos[j]] := Generic(G)!G.j; 
    end for;
    
    H := sub<Generic(G) | gens>;
    H`UserGenerators := gens;
    InitialiseGroup(H : type := G`type);
    return H;
end function;


/*********************************************************************/
/* Input:  d,q,type,n 
/* Output: test SX(d,q) n times
/*
/* op.Par: sameGroup: use the same group for each of the
/*                    n tests
/*         vmode=[a,b,c] : SetVerbose mode for the test
/*                         a: SXECinv (construct inv.)
/*                         b: SXECstdgens (construct gens.)
/*                         c: SXECcpu (cpu time)
/*         check    : test the final results?
/*         silent   : no "ok" output
/*         smallCorank := computes only small corank inv.
/*********************************************************************/
SXECtestInv := procedure(d,q,type,n :sameGroup   := false, 
                                     vmode       := [0,0,0], 
                                     check       := true, 
                                     silent      := false,
                                     smallCorank := false)
   
    if Type(vmode) eq RngIntElt then vmode := [vmode,vmode]; end if;
    verb1 := GetVerbose("SXECcpu");
    SetVerbose("SXECcpu",vmode[3]);
    verb2 := GetVerbose("SXECinv");
    SetVerbose("SXECinv",vmode[2]);
    verb3 := GetVerbose("SXECstdgens");
    SetVerbose("SXECstdgens",vmode[1]);
    if sameGroup then  G := makeSXEC(d,q,type); end if;
    for i in [1..n] do
        if sameGroup then
            H := sub<Generic(G)|UserGenerators(G)>; 
            InitialiseGroup(H);
        else
            H := RandomConjugate(makeSXEC(d,q,type)); 
        end if;
        H`type := type;
        ct  := Cputime();
        g,w := InvolutionClassicalGroupEven(H : SmallCorank := smallCorank);
        "Nr.",i,type,"(",d,",",q,") Time:",Cputime(ct), " wlength",#w;
        if not silent and type eq "O-" then "Corank is ",Corank(g); end if;
        if check then
            slpflag := g eq Evaluate(w,UserGenerators(H));
            assert slpflag; 
            if not silent then "SLP ok"; end if;
            ordflag := Order(g) eq 2;
            assert ordflag; 
            if not silent then "order ok"; end if;
            if type in ["SL","SU"] and not smallCorank then
                crflag := (Corank(g) eq (d div 2));
                assert crflag;
                 if not silent then "corank ok"; end if;
            else
                if (d mod 4 eq 0 and not type eq "O-") and not smallCorank then
                    crflag := (Corank(g) eq (d div 2));
                    assert crflag;
                     if not silent then "corank ok"; end if;
                end if;
            end if;
        end if;
    end for;
    SetVerbose("SXECcpu",verb1);
    SetVerbose("SXECinv",verb2);
    SetVerbose("SXECstdgens",verb3);
end procedure;

/****
    repeat 
       SXECtestInv(Random([4..80 by 2]),
                   Random([2^i : i in [1..10]]),
                   Random(["SL","O+","Sp","O-","SU"]), 1); 
   until false;
****/   


/*********************************************************************/
/* Input:  d,q,type,n with type in ["SL","SU","Sp","O-","O+"] 
/*         and q=2^i
/* Output: test StdGens for SX(d,q) n times:
/*         computes gens and checks if elts are correct;
/*         by default, does not check SLPS (see options)
/*
/* op.Par: vmode=[a,b,c] : SetVerbose mode for the test
/*                         a: CIESXEC (construct inv.)
/*                         b: CSGSXEC (construct gens.)
/*                         c: CPUTIMESX (Cputime)
/*         check   : test the SLPs (without cycle)
/*         cycle   : test all SLPs
/*         rels    : checks int_StandardPresentationForSp/SU/SL
/*                   if this flag is active, then ONLY no other test
/*                   will be done; the reason is that the constructed
/*                   gens are rewritten to EOB gens
/*********************************************************************/
SXECtestStdGens := procedure(d,q,type,n : vmode := [0,0,0], 
                                         check  := false,
                                         cycle  := false, 
                                         silent := false,
                                         rels   := false)

    if Type(vmode) eq RngIntElt then vmode := [vmode,vmode]; end if;
    verb1 := GetVerbose("SXECinv");
    SetVerbose("SXECinv",vmode[1]);
    verb2 := GetVerbose("SXECstdgens");
    SetVerbose("SXECstdgens",vmode[2]);
    verb3 := GetVerbose("SXECcpu");
    SetVerbose("SXECcpu",vmode[3]);
    H    := RandomConjugate(makeSXEC(d,q,type)); 
    if cycle eq true then check := true; end if;
  //Since SU(2) = SL(2), take care of rewriting for this "external" testing 
    if d eq 2 and type eq "SU" then
      stdgens := [GL(2,q^2)!u: u in StandardGeneratorElements(GF(q),d,"SL")];
      Prune(~stdgens);
    else
      stdgens := StandardGenerators(BaseRing(H),d,type);
    end if;
    for i in [1..n] do
        ct    := Cputime();
        if not rels then
            a,b,c :=  SolveClassicalEven(H : rewriteToEOB := false);
        else
            a,b,c :=  SolveClassicalEven(H);
        end if;
        "Nr.",i,type,"(",d,",",q,") Time:",Cputime(ct),
                     ", Word lengths:",[#w:w in b];
        if not rels then
            flagsg := a eq stdgens;
            if not flagsg then "computed",a,"should be",stdgens; end if;
            assert flagsg;
            if check then
                if not silent then "Test SLPs of non-cycles:"; end if;
                cyc    := a[5];   cycw := b[5];
                a[5]   := a[5]^0; b[5] := b[5]^0;
                cinv   := c^-1;
                flagev := a eq [c*Evaluate(w,UserGenerators(H))*cinv: w in b];
                assert flagev;
                if cycle then
                    if not silent then "SLPs correct, now test cycle:"; end if;
                    flagc  := cyc eq c*Evaluate(cycw,UserGenerators(H))*cinv;
                    if not flagc then
                        "this is ev cycle",c*Evaluate(cycw,UserGenerators(H))*cinv;
                        assert flagc;
                    end if;
                    if not silent then "SLP of cycle is correct."; end if;
                else
                    if not silent then 
                        "SLPs correct, haven't checked cycle."; 
                    end if;
                end if;
            end if;
        end if;
        if rels and type in ["SL","SU","Sp"] then
            if   type eq "SL" then Q,R:=int_StandardPresentationForSL(d,q);
            elif type eq "SU" then Q,R:=int_StandardPresentationForSU(d,q);
            elif type eq "Sp" then Q,R:=int_StandardPresentationForSp(d,q); 
            end if;
            relwords := Evaluate(R,b);
            relelts  := Evaluate(relwords,UserGenerators(H));
            if not forall(rel){rel : rel in [1..#relelts] | Order(relelts[rel]) eq 1} then
                error "some relation is not trivial!!!";
            else
                if not silent then 
                    "presentation correct"; 
                end if;
            end if;
        end if;
        if i lt n then H := RandomConjugate(makeSXEC(d,q,type)); end if;
    end for;
  //if results then return H,a,b,c; else return "ok"; end if;
    SetVerbose("SXECinv",verb1);
    SetVerbose("SXECstdgens",verb2);
    SetVerbose("SXECcpu",verb3);
end procedure;


/************ TEST FUNCTION, please load manually

load "~/magma/mgrp/classical/recognition/standard.m";
quickTestEOBGens := function()

    for n in [2..10] do
        for q in [2,4,8,16] do
            G      := makeSXEC(n,q,"SL");
            E,W,CB := SolveClassicalEven(G);
            assert E eq [CB*Evaluate(w,UserGenerators(G))*CB^-1:w in W];
            assert E eq SLChosenElements(G);
            "SL",n,q,"ok";
        end for;
    end for;

   for n in [4..12 by 2] do
        for q in [4,8,16] do
            G      := makeSXEC(n,q,"Sp");
            E,W,CB := SolveClassicalEven(G);
            assert E eq [CB*Evaluate(w,UserGenerators(G))*CB^-1:w in W];
            assert E eq SpChosenElements(G);
            "Sp",n,q,"ok";
        end for;
    end for;

    for n in [4..12 by 2] do
        for q in [4,8,16] do
            G      := makeSXEC(n,q,"O+");
            E,W,CB := SolveClassicalEven(G);
            assert E eq [CB*Evaluate(w,UserGenerators(G))*CB^-1:w in W];
            assert E eq PlusChosenElements(G);
            "O+",n,q,"ok";
        end for;
    end for;

    for n in [4..12 by 2] do
        for q in [4,8] do
            G      := makeSXEC(n,q,"O-");
            E,W,CB := SolveClassicalEven(G);
            assert E eq [CB*Evaluate(w,UserGenerators(G))*CB^-1:w in W];
            assert E eq MinusChosenElements(G);
            "O-",n,q,"ok";
        end for;
    end for;

   
    for n in [2..10] do
        for q in [2,4,8] do
            if not (n eq 5 and q eq 8) then 
                G      := makeSXEC(n,q,"SU");
                E,W,CB := SolveClassicalEven(G);
                assert E eq [CB*Evaluate(w,UserGenerators(G))*CB^-1:w in W];
                assert E eq SUChosenElements(G);
                "SU",n,q,"ok";
            end if;
	end for;
    end for;
   
end function;

****************************************************/

