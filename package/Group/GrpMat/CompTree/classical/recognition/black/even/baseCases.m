freeze;

import "solveClassicalEven.m": SXEStandardGeneratorsEven,SXELieType,SXEInitGroup,SXECopyGroup,SXERandomWord, SXECentraliserOfInvolution, SXEgetSection, SXEcheckPresentation,SXEElementsToConstruct,SXEWhatPPD;


import "../../../classical.m": ClassicalConstructiveRecognitionNatural;


/***********************************************************/
/* solve SL4 black box
/* this function is ONLY called from outside, so first we 
/* have to create a fresh copy of the group and initialise it
/***********************************************************/
SXESolveSL4black := function(GG,F:lv:=1)

//get fresh copy and initialise it with my data structure
   G := sub<Generic(GG) | [GG.i : i in [1..Ngens(GG)]]>;
   SXEInitGroup(G:type:=<"SL",4,#F,2>);

   vprint evenSX, 2: "start SXESolveSL4black";
   rnt    := Cputime();
   
   if G`type eq "O+" then
      oldnp := G`natParams;
      G`type := "SL";
      G`natParams := <"SL",4,G`natParams[3],2>;
   else
      oldnp   := -1;
   end if;

   type := "SL";
   nP     := G`natParams; d := nP[2]; q := nP[3]; p := nP[4];

   H,m := SmallerClassicalGroup(G);
   eltA,wA := SXEStandardGeneratorsEven(H:lv:=lv+1);

   wA      := Evaluate(wA,H`UserWords);
   el      := eltA[1];
   wel     := wA[1];

   getGroup := function(G,H,el,wel)

     cnt := 0;
     repeat
         cnt  := cnt + 1;
         g,wg := SXERandomWord(G);
         h    := el^g;
         wh   := wel^ wg;
         gen  := [i^h : i in UserGenerators(H)] cat UserGenerators(H);
         wgen := [i^wh : i in H`UserWords] cat H`UserWords;
         L    := sub<Generic(G)|gen>;
         L`UserGenerators := gen;
         L`UserWords := wgen;
         HH2 := sub<Generic(G)| [i^h : i in UserGenerators(H)]>;
         HH2`UserGenerators := [i^h : i in UserGenerators(H)];
         HH2`UserWords := [i^wh : i in H`UserWords];

         t := SXELieType(L:char:=2,shouldBe:=<"SL",3,q,2>);
         if cnt mod 50 eq 0 then 
            if cnt gt 1000 then error "stop this..."; end if;
         end if;
         
      until t cmpeq <"SL",3,q,2>;
      SXEInitGroup(L : type := "SL", natParams := <"SL",3,q,2>); 
      return L, HH2, h,wh;
   end function;

 //first SL3, adjust basis
   A, HH2,Hel,Helw    := getGroup(G,H,el,wel);

  //std gens of second SL2 generating A=SL3
   eltH2 := [i^Hel : i in eltA];
   wH2   := [i^Helw : i in wA];

   Ac   := SXECopyGroup(A);
   
   gAc  := [Generic(Ac)| Ac.i : i in [1..Ngens(Ac)]];
   ugA  := [Generic(Ac)| u : u in UserGenerators(A)];

   flag := false; 
   fcnt := 1;    
   while not flag and fcnt lt 4 do
      flag,m1,m2,m3,m4,e,w := ClassicalConstructiveRecognition(Ac,"SL",3,q);
    //flag,m1,m2,m3,m4,e,w:=RecogniseSL3(Ac,q);
      fcnt := fcnt + 1;    
   end while;     
   if not flag then error "recsl3 failed"; end if;

   imH  := [Function(m1)(e) : e in eltA];

   Aim := Domain(m2);
   ev1 := [u[1] : u in Eigenvalues(imH[4]) | not u[1] eq 1];
   tmp := Eigenspace(imH[3],1);
   flg := exists(om){om : om in ev1 | Dimension(tmp meet Eigenspace(imH[4],om)) eq 1};
   V3  := tmp meet Eigenspace(imH[4],om);
   assert Dimension(V3) eq 1;
   v3  := Basis(V3)[1];
   v2  := v3*imH[1];
   V1  := (Eigenspace(imH[1],1) meet Eigenspace(imH[3],1)) meet Eigenspace(imH[4],1);
   assert Dimension(V1) eq 1;
   v1  := Basis(V1)[1];
   cob := Generic(Aim)!Eltseq([Eltseq(j) : j in [v1,v2,v3]]);

   todo := SXEElementsToConstruct("SL",3,q) cat [GL(3,q)![0,0,1, 1,0,0, 0,1,0]];
   todo := [cob^-1*i*cob : i in todo];
 
   todo := [Function(m2)(e) : e in todo];
   wrd  := [Function(m3)(e) : e in todo];

   pos  := [Position(ugA,g) : g in [Ac.i : i in [1..Ngens(Ac)]]];
   wrd  := Evaluate(wrd, [A`SLPGroup.i : i in pos]); //XXXX was Ac
   wrd  := Evaluate(wrd,A`UserWords);  
   std  := todo;
   wstd := wrd;
   
   inv  := std[3];  
   winv := wstd[3]; 
   fpf  := std[4];
   wfpf := wstd[4];

   C, Cw := SXECentraliserOfInvolution(G,inv,winv);
   K := SXEgetSection(C,fpf,wfpf,G,d,p,2,"SL");
   K`type := "SL";
   K`natParams := <"SL",2,q,2>;

   tmp  := UserGenerators(H) cat UserGenerators(K);
   B    := sub<Generic(G)|tmp>;
   B`UserGenerators := tmp;
   B` UserWords     := H`UserWords cat K`UserWords;
   t              := SXELieType(B : char :=2);
   assert  t cmpeq <"SL",3,q,2>;
   B`natParams := <"SL",3,q,2>;
   B`type      := "SL";
   SXEInitGroup(G);   

   Bc   := SXECopyGroup(B);
   gBc  := [Generic(Bc)| Bc.i : i in [1..Ngens(Bc)]];
   ugB  := [Generic(Bc)| u : u in UserGenerators(B)];

   flag := false; 
   fcnt := 1;    
   while not flag and fcnt lt 4 do
       flag,m1,m2,m3,m4 := ClassicalConstructiveRecognition(Bc,"SL",3,q);
     //flag,m1,m2,m3,m4 := RecogniseSL3(Bc,q);
       fcnt := fcnt + 1;    
   end while;  
   if not flag then error "recsl3 failed"; end if;

   imH  := [Function(m1)(e) : e in eltA];

   Bim := Domain(m2);
   ev1 := [u[1] : u in Eigenvalues(imH[4]) | not u[1] eq 1];
   tmp := Eigenspace(imH[3],1);
   flg := exists(om){om : om in ev1 | Dimension(tmp meet Eigenspace(imH[4],om)) eq 1};
   V3  := tmp meet Eigenspace(imH[4],om);
   assert Dimension(V3) eq 1;
   v3  := Basis(V3)[1];
   v2  := v3*imH[1];
   V1  := (Eigenspace(imH[1],1) meet Eigenspace(imH[3],1)) meet Eigenspace(imH[4],1);
   assert Dimension(V1) eq 1;
   v1  := Basis(V1)[1];
   cob2 := Generic(Aim)!Eltseq([Eltseq(j) : j in [v2,v3,v1]]);
   todo := [GL(3,q)![1,0,0, 0,0,1, 0,1,0]];
   todo := [cob2^-1*i*cob2 : i in todo];

   todo := [Function(m2)(e) : e in todo];
   wrd  := [Function(m3)(e) : e in todo];

   pos  := [Position(ugB,g) : g in [Bc.i : i in [1..Ngens(Bc)]]];
   wrd  := Evaluate(wrd, [B`SLPGroup.i : i in pos]); //XXXXX was Bc
   wrd  := Evaluate(wrd,B`UserWords);
   elt  := todo;

// EOB -- added this line to solve mutation problem 
   std := [Generic (Universe (std)) | s: s in std];
   std[2] := std[#std]*elt[1];
   wstd[2] := wstd[#std]*wrd[1];
   assert Order(std[2]) eq 4;


 //HD - adjusted this because words are not necessarily in G`SLPGroup
   for i in [5..11] do std[i] := Id(G); wstd[i] := wstd[1]^0; end for;

   std[10] := std[3]*std[3]^(std[2]^2); wstd[10]:=wstd[3]*wstd[3]^(wstd[2]^2);
   std[11] := std[4]*std[4]^(std[2]^2); wstd[11]:=wstd[4]*wstd[4]^(wstd[2]^2);

   vprint evenSXcpu,1: "runtime SXESolveSL4black is",Cputime(rnt);
   vprint evenSX, 2: "end SXESolveSL4black";

   if not oldnp cmpeq -1 then G`type := "SL"; G`natParams:= oldnp; end if;

   pos    := [Position([*G.i:i in [1..Ngens(G)]*],j ) : j in UserGenerators(G)];
 //careful to use WordGroup(GG) and NOT WordGroup(G)
 //this assumes that Ngens of G and GG still correspond
   nslp   := [WordGroup(GG).i : i in pos];
   wstd   := [Evaluate(u,nslp) : u in wstd];         

   vprint evenSXcpu,1: "runtime SXESolveSL4black is",Cputime(rnt);
   vprint evenSX,1: "end SXESolveSL4black with SLP lengths", [#i : i in wstd];

   return  [std[i] : i in [1..4]], [wstd[i] : i in [1..4]];

end function;




/****************************************************************************/
/* this function is ONLY called from outside, so first we 
/* have to create a fresh copy of the group and initialise it
/***********************************************************/
SXESolveSL5black := function(GG,F:lv:=1)

//get fresh copy and initialise it with my data structure
    G := sub<Generic(GG) | [GG.i : i in [1..Ngens(GG)]]>;
    SXEInitGroup(G:type:=<"SL",5,#F,2>);
    
    type := "SL";

    vprint evenSX,1: "start SXESolveSL5black";
    rnt  := Cputime();
    nP   := G`natParams;
    d    := nP[2];  q := nP[3];  p := nP[4];
    elt  := SXEElementsToConstruct("SL",d,q);
    H, m := SmallerClassicalGroup(G);
    assert m eq 4;
    sgH, wH := SXEStandardGeneratorsEven(H:lv:=lv+1);
    wH   := Evaluate(wH,H`UserWords);
    sgH  := Evaluate(wH,UserGenerators(G));
   
    inv  := sgH[3];
    winv := wH[3];
    fp   := sgH[4];
    wfp  := wH[4];
    C, Cw := SXECentraliserOfInvolution(G,inv,winv);
    k    := 3;
    K    := SXEgetSection(C,fp,wfp,G,d,p,3,"SL");

    K`natParams := <"SL",k,q,2>;
    Kc := SXECopyGroup(K);
    ug := UserGenerators(K);
    vprint evenSX, 2: "start composition tree in SolveSL5 for degree",k;

    CT := CompositionTree(Kc);

    _,m2,m3,m4  := CompositionTreeSeries(Kc);
    nr     := [i : i in [1..#m4] | Type(Domain(m4[i])) eq GrpMat and
                                         Degree(Domain(m4[i])) eq k];
    nr     := nr[1];
    slk    := Codomain(m2[nr]);
    m2     := Function(m2[nr]); 
    m4     := Function(m4[nr]); 
    m3     := Function(m3[nr]);
    cc     := sgH[2]^-2;
    sl2    := [sgH[1]^cc,sgH[3]^cc,sgH[4]^cc];
    sl1ims := [Generic(slk)|m2(j) : j in sl2];

    // XXXXXXXXXXXXXX
    // problem: m2 gives not the elts we want to construct, but
    //          sth twisted by central elements!
    //
    // correct orders of involutions

    for i in [1..2] do sl1ims[i] := sl1ims[i]^3; end for;
    if q gt 4 then 
        sl1ims[3] := sl1ims[3]^3; 
    else
        w := PrimitiveElement(GF(4));
        z := GL(3,q)!DiagonalMatrix([w,w,w]);
        f := exists(i){i : i in [0,1,2] |
             Dimension((Eigenspace(sl1ims[1],1) meet Eigenspace(sl1ims[3]*z^i,1)) 
                                                meet Eigenspace(sl1ims[2],1)) eq 1};
        if not f then error "sl5: couldn't adjust m2 map"; end if;
        sl1ims[3] := sl1ims[3]*z^i;
    end if;


   V3 := (Eigenspace(sl1ims[1],1) meet Eigenspace(sl1ims[3],1)) meet Eigenspace(sl1ims[2],1);
   assert Dimension(V3) gt 0;
   v3 := Basis(V3)[1];
   ev1 := [u[1] : u in Eigenvalues(sl1ims[3]) | not u[1] eq 1];  
   tmp := Eigenspace(sl1ims[2],1);
   flg := exists(om){om : om in ev1 | Dimension(tmp meet Eigenspace(sl1ims[3],om)) eq 1}; 
   V2  := tmp meet Eigenspace(sl1ims[3],om);
   v2  := Basis(V2)[1];
   v1  := v2*sl1ims[1];   

   cob := Generic(slk)!Eltseq([Eltseq(j) : j in [v1,v2,v3]]);

   want   := [GL(3,q)![1,0,0,0,0,1,0,1,0]];
   want   := [cob^-1*i*cob : i in want];
   WANT   := want;

   Knice  := CompositionTreeNiceGroup(Kc);
   rew,wr := CompositionTreeNiceToUser(Kc);
   want   := [m3(i) : i in want];
   wantw := [];
   for i in want do 
      flg,tw  := CompositionTreeElementToWord(Kc,i);
      assert flg;
      Append(~wantw,tw);
   end for;
   wantw  := Evaluate(wantw,wr);
   pos    := [Position(ug,Kc.j) : j in [1..Ngens(Kc)]];
   nslp   := [K`SLPGroup.i : i in pos]; 
   wantw  := Evaluate(wantw,nslp);         
   wantw  := Evaluate(wantw,K`UserWords);  

 
    done := false;
    i    := 1;
    
  //add prelim elts (instead of doing it in SL4)
    sgH[12] := sgH[2]^-1; wH[12] := wH[2]^-1;
    sgH[13] := sgH[2]^2; wH[13] := wH[2]^2;

    while not done and i le #want do 
      //now glue is (e1,e2)(f1,f2,eta w)
        glue   := want[i]*sgH[13]; 
        gluew  := wantw[i]*wH[13]; 
        i      := i+1; 
        tmp    := sgH;

      //assume that sgH[12] is [0100 0010 0001 1000]
      //our presentation assumes cycle has length 5...
        glue   := glue^3*sgH[12]^-1*glue^2;
        gluew  := gluew^3*wH[12]^-1*gluew^2;
        tmp[2] := glue;
        done := Order(glue) eq 5 and SXEcheckPresentation(type,tmp,5,q:justCheck:=true);

    end while;
    if not done and i gt #want then "SL5: couldn find glue; serioues problem!"; end if;
    sgH[2] := glue;
    wH[2]  := gluew;

    std    := sgH;
    wstd   := wH;
    pos    := [Position([*G.i:i in [1..Ngens(G)]*],j ) : j in UserGenerators(G)];
    nslp   := [WordGroup(GG).i : i in pos];
    wstd   := [Evaluate(u,nslp) : u in wstd];         
    
    vprint evenSXcpu,1: "runtime SXESolveSL5black is",Cputime(rnt);
    vprint evenSX,1: "end SXESolveSL5black with SLP lengths", [#i : i in wstd];

    return [std[i] : i in [1..4]], [wstd[i] : i in [1..4]];

end function;




