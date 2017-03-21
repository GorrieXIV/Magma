import "solveClassicalEven.m": SXEInitGroup, MySymmetricPower, MyPermGroup, MyTensor, MyExteriorPower,SXEcheckPresentation,SXEMakePretty, SXEExtractGroup, SXELieTypeNatRep,SXELieType,SXEonlyBlack,SXEIsNatRep;

/*********************************************************************/
/* input: type, d,q
/* output: initialised group type(d,q)
/* (for testing purposes)
/*********************************************************************/
intrinsic SXEMakeGroup (type, d, q : grey := false, black := false, proj := false)->Grp
{test function}
    vprint evenSX, 3: "start SXEMakeGroup";

    MyExteriorPower := function( G, t )
        M := GModule( G );
        N := ExteriorPower( M, t );
        G := ActionGroup( N );
        return G;
    end function;

    MySymmetricPower := function( G, t )
        M := GModule( G );
        N := SymmetricPower( M, t );
        G := ActionGroup( N );
        return G;
    end function;

    MyTensor := function(G)
        H := FrobeniusImage(G,1);
        g := [GL(d^2,#BaseRing(G))!KroneckerProduct(G.i,H.i) : i in [1..Ngens(G)]];
        G := sub<GL(d^2,#BaseRing(G))|g>;
        return G;
    end function;
 
    MyPermGroup := function( G )
        G := Codomain(PermutationRepresentation(G));
        return G;
    end function;

    if type eq "SL" then 
        G  := SL(d,q);
    elif type eq "SU" then
        G  := SU(d,q);
    elif type eq "Sp" then
        G  := Sp(d,q);
    elif type eq "O+" then
        G  := OmegaPlus(d,q);
    elif type eq "O-" then
        G  := OmegaMinus(d,q);
    end if;
    ug := [Generic(G)| u: u in UserGenerators(G)] cat [Generic(G)|Random(G):i in [1..5]];
    G  := sub<Generic(Parent(ug[1]))|ug>;
    if grey cmpeq true then grey := Random(["sym","ext","ten"]); end if;
    if grey cmpeq "sym" then
        G := MySymmetricPower(G,2);
    elif grey cmpeq "ext" then
        G := MyExteriorPower(G,2);
    elif grey cmpeq "ten" then
        G := MyTensor(G);
    end if;
    if black then
        G := MyPermGroup(G);
    end if;    
    natParams   := <type,d, q, Characteristic(GF(q))>;
    if proj then
       if natParams[1] eq "SL" then G := PSL(natParams[2],natParams[3]);
       elif natParams[1] eq "Sp" then G := PSp(natParams[2],natParams[3]);
       elif natParams[1] eq "SU" then G := PSU(natParams[2],natParams[3]);
       elif natParams[1] eq "O+" then G := POmegaPlus(natParams[2],natParams[3]);
       elif natParams[1] eq "O-" then G := POmegaMinus(natParams[2],natParams[3]);
       end if;  
    end if;
    natParams   := <type,d, q, Characteristic(GF(q))>;
    G`natParams := natParams;
    G`type      := type;
    SXEInitGroup(G);
    vprint evenSX, 3: "end SXEMakeGroup";
    return G;
end intrinsic;



/*********************************************************************/
/* input: matrix group
/* output: list of different reps for testing purposes
/*********************************************************************/
intrinsic SXEConstructReps (type,d,q)->[]{}

   MyDeltaRepresentation := function (G,e)
      F := BaseRing(G);
      d :=Degree (G);
      p := Characteristic (F);
      X := [G.i: i in [1..Ngens (G)]];
      Y := [FrobeniusImage (G.i, e): i in [1..Ngens (G)]];
      Z := [KroneckerProduct (X[i], Y[i]): i in [1..#X]];
      G:=sub<GL(d^2,F) | Z>;
      M:=GModule (G);
      factors:=CompositionFactors(M);
      dim, index:= Maximum([Dimension(x): x in factors]);
      M:=factors[index];
      return RandomConjugate(MatrixGroup(M));
   end function;

   MyOtherRepresentation := function (G, e)
      F := BaseRing (G);
      q := #F;
      d := Degree (G);
      M := GModule (G);
      U := Dual (M);
      H := ActionGroup (U);
      p := Characteristic (F);
      X := [H.i: i in [1..Ngens (G)]];
      Y := [FrobeniusImage (G.i, e): i in [1..Ngens (G)]];
      Z := [KroneckerProduct (X[i], Y[i]): i in [1..#X]];
      G := sub < GL (d^2, F) | Z>;
      M:=GModule (G);
      factors:=CompositionFactors(M);
      dim, index:= Maximum([Dimension(x): x in factors]);
      M:=factors[index];
      return RandomConjugate(MatrixGroup(M));
   end function;

   DifferentOnes := function (S, MyCompare)
      if #S le 1 then return S, [i : i in [1..#S]]; end if;
      D := [S[1]];
      for i in [2..#S] do
         if forall {j : j in [1..#D] | 
              MyCompare (S[i], D[j]) eq false}  then 
           Append (~D, S[i]);
        end if;
      end for;
      pos := [Position (S, D[i]) : i in [1..#D]];
      return D, pos;
   end function;


   G := SXEMakeGroup(type,d,q);

   M:=GModule(G);
   T := TensorProduct (M, M);
   T := TensorProduct (T, M);
   CF := CompositionFactors (T);
   N := [(SymmetricPower (M, i)): i in [2..5]] cat 
        [(ExteriorPower (M, i)): i in [2..4]]; 
   CF2 := &cat[CompositionFactors (x): x in N];
   T := TensorProduct (M, M);
   T := TensorProduct (T, T);
   CF3 := CompositionFactors (T);

   CF := CF cat CF2 cat CF3;
   CF := DifferentOnes (CF, IsIsomorphic);
   F := BaseRing (G);
   A := MyDeltaRepresentation (G, Degree (F) + 1);
   B := MyOtherRepresentation (G, Degree (F) + 2);
   
   reps := [ActionGroup (x): x in CF | Dimension (x) gt 1] cat [A, B];
   new  := [**]; 
   for j in reps do i:=j; i`type := type; i`natParams := <type,d,q,2>; Append(~new,i); end for;

   "finished constructing reps, got",[*[*Degree(i),BaseRing(i)*]: i in new*];

   return new;
end intrinsic;




/**********************************************************************/
/* a test function
/**********************************************************************/
intrinsic SXEtestStdGens (degs,qs,nr,type : grey  := false,
                                     black  := false,
                                     proj   := false,
                                     test   := true,
                                     vmode  := [0,0],
                                     rconj  := false,
                                     silent := false,
                                     seed   := false) -> MonStgElt

{test function}
    if silent then vmode := [0,0]; end if;
    "Have these flags (SXEonlyBlack)",SXEonlyBlack;
    if Type(vmode) eq RngIntElt then vmode := [vmode,vmode]; end if;
    verb1 := GetVerbose("evenSX");
    SetVerbose("evenSX",vmode[1]);
    verb2 := GetVerbose("evenSXcpu");
    SetVerbose("evenSXcpu",vmode[2]);
    first := true;
    ttype := type;
if type eq "O+" then ttype := "Omega+"; elif type eq "O-" then ttype := "Omega-"; end if;
    for d in degs do
       for q in qs do
           for i in [1..nr] do
               if not silent then
                  if grey cmpeq "ten" or grey cmpeq "ext" or grey cmpeq "sym" or black cmpeq true or proj cmpeq true then
                     "===========================================================================";
                     "-------(grey/black!)------------------------------ start test",type, d,q,"nr",i;
                  else
                     "===========================================================================";
                     "------------------------------------- start test",type, d,q,"nr",i;
                  end if;
                  "seed",GetSeed();
                  if first and not seed cmpeq false then 
                     SetSeed(seed[1],seed[2]);  "set seed to ",GetSeed();
                     first := false;
                  end if; 
                  G          := SXEMakeGroup(type,d,q : grey := grey, black := black, proj:=proj);
                  if proj then "group has type",Type(G); end if;
                  if rconj then G:=RandomConjugate(G); SXEInitGroup(G); end if;

                  rnt        := Cputime();                    

                  if IsEven(q) then
                     el, wr     := Internal_ClassicalSolveEven(G,ttype,d,q);
                  else 
                    
		    _, el, wr := Internal_ClassicalSolve(G,ttype,d,q);
                  end if;   
                  "wlengths",[#wr[i] : i in [1..Minimum(8,#wr)]];
                  "runtime",Cputime(rnt);

                  if test then
                     assert el eq Evaluate(wr,UserGenerators(G)); 
                     "evaluation OK";
                     assert SXEcheckPresentation(type,el,d,q);
                      "presentation OK";
                  end if;
              else
                
                  G := SXEMakeGroup(type,d,q : grey := grey, black := black);
                  if rconj then G:=RandomConjugate(G); SXEInitGroup(G); end if;
                  rnt        := Cputime();
                  if IsEven(q) then
                     el, wr     := Internal_ClassicalSolveEven(G,ttype,d,q);
                  else 
                     
		    _, el, wr := Internal_ClassicalSolve(G,ttype,d,q);
                  end if;   
                  t          := Cputime(rnt);
                  gb :=  grey cmpeq "ten" or grey cmpeq "ext" or black cmpeq true;
                  if test then
                     assert el eq Evaluate(wr,UserGenerators(G)); 
                     assert SXEcheckPresentation(type,el,d,q);
                  end if;
                 "Nr.",i,type,"(",d,",",q,"), nat-rep",not gb,", Time:",t, 
                 " wlength",[#wr[i] : i in [1..Minimum(8,#wr)]];
              end if;
           end for;
       end for;
    end for;
    SetVerbose("evenSX",verb1);
    SetVerbose("evenSXcpu",verb2);
    return "ok";
end intrinsic;






/****************************************************************************/
/* Test functions
/****************************************************************************/
intrinsic SXEtestSmallerGroup (degs,qs,nr,type : grey  := false,
                                           onlyBlack := false,
                                           black  := false,
                                           test   := true,
                                           silent := false,
                                           vmode  := [0,0]) ->MonStgElt
{test function}

    if Type(vmode) eq RngIntElt then vmode := [vmode,vmode]; end if;
    if silent then vmode := [0,0]; end if;
    verb1 := GetVerbose("evenSX");
    SetVerbose("evenSX",vmode[1]);
    verb2 := GetVerbose("evenSXcpu");
    SetVerbose("evenSXcpu",vmode[2]);
    for d in degs do 
       for q in qs do 
           p := Factorisation(q)[1][1];
           for i in [1..nr] do  
               "---- now test",type,d,q,"nr",i, "------------------------------------------"; 
               G   := SXEMakeGroup(type,d,q : grey := grey, black:=black);
               rnt := Cputime();
               H,m :=  SmallerClassicalGroup(G:onlyBlack:=onlyBlack); 
               "found degree",m,"in degree",d,"runtime",Cputime(rnt);
               if test then 
                   assert UserGenerators(H) eq Evaluate(H`UserWords,UserGenerators(G));
                   "evaluation OK";
                   if SXEIsNatRep(G) and not onlyBlack then
                      K  := SXEMakePretty(H);
                      K1 := SXEExtractGroup(K,[1..m]);
                      K2 := SXEExtractGroup(K,[m+1..d]);
                      assert Order(K2) eq 1;
                      if (type in ["Sp","O-"] and IsEven(q)) or type eq "O-" then 
                         ttype := "O+"; 
                      else 
                         ttype := type; 
                      end if;
                      tt := SXELieTypeNatRep(K1 :shouldBe := <ttype,m,q,p>);
                      if not tt cmpeq <ttype,m,q,p> then
                         "got this",tt,"try again:";
                          tt := SXELieTypeNatRep(K1 :shouldBe := <ttype,m,q,p>);
                          "got, order",tt,#K1,#Sp(m,q);
                          "lt of whole",LieType(H,p),#H;H:Magma;SXELieType(H:char:=p);
                          assert tt cmpeq <ttype,m,q,p>;
                       end if;
                      "nat rep ok; found ",tt;
                   else
                      if (type in ["Sp","O-"] and IsEven(q)) or type eq "O-" then 
                         ttype := "O+"; 
                      else 
                         ttype := type; 
                      end if;
                      tt := SXELieType(H :shouldBe := <ttype,m,q,p>);
                      if not tt cmpeq <ttype,m,q,p> then
                         "got this",tt,"try again:";
                          tt := SXELieType(H :shouldBe := <ttype,m,q,p>);
                          "got, order",tt,#H,#Sp(m,q);
                          "lt of whole",LieType(H,p),#H;H:Magma;SXELieType(H:char:=p);
                          assert tt cmpeq <ttype,m,q,p>;
                       end if;
                      "black rep ok, found ",tt;
                   end if;
               end if;
           end for;
       end for; 
    end for;
    SetVerbose("evenSX",verb1);
    SetVerbose("evenSXcpu",verb2);
    return "ok";
end intrinsic;




