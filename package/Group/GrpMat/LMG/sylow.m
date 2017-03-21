freeze;

import "sections.m": GetSolRad, GetPKer, GetSocleAct;
SylSub := function(G, p)
/* Get Sylow p-subgroup of a group using LMG style. */
  local GG, r, AP, IAP, KP, IKP, SP, ISP, RP, IRP, gens, rgens, OIAP, OIAPreps,
   RPN, cslen, socfacs, hasp, f, q, MakeNormRP, MakeNormSP, MakeNormKP, P, PP;

  if not assigned G`LMGNode`radPC then
    GetSolRad(G);
  end if;
  if not assigned G`LMGNode`pkerPC then
    GetPKer(G);
  end if;
  if not assigned G`LMGNode`Gtosocperm then
    GetSocleAct(G);
  end if;
  GG := Generic(G);
  r := G`LMGNode;

  cslen := #r`factortype;
  socfacs := [ i : i in [1..cslen] | r`factortype[i] eq 2 ];

  IAP := Sylow(r`socperm, p);
  OIAP := Orbits(IAP);
  OIAPreps := { o[1] : o in OIAP };

  //Now we start building up the Sylow subgroup from the bottom upwards
  //rgens will contain the generators that we will eventually need. 

  //start with radical
  IRP := Sylow(r`radPC, p);
  RPN := IsNormal(r`radPC,IRP);
  rgens := [ Generic(G) |  g @@ r`radtoPC : g in Generators(IRP) ];
  RP := sub< GG | rgens >; 

  if forall{ i : i in [1..cslen] |
                   r`factortype[i] eq 1 or r`factorord[i] mod p ne 0 } then
    //RP already Sylow p-subgroup
    return RP;
  end if;

  //We will want further generators to normalise RP and have order power of p,
  //so we write functions to achieve this.

  MakeNormRP := function(g)
    local Q, c;
    if not RPN then
      Q := sub< r`radPC | [ (x^g) @ r`radtoPC : x in Generators(RP) ] >;
      _, c := IsConjugate( r`radPC, Q, IRP );
      g := g * (c @@ r`radtoPC);
    end if;
    return g^(ord div p^Valuation(ord,p)) where ord := Order(g);
  end function;

  //Now socle factors. If any are not divisible by p, we will use a
  //Sylow 2-subgroup for the Frattini argument.
  SP:=[]; ISP:=[**];
  for i in [1..#socfacs] do
    f := socfacs[i];
    hasp := r`factorord[f] mod p eq 0;
    q := hasp select p else 2;
    ISP[i] := r`sfclass[i] select ClassicalSylow(r`ims[f],q)
                             else Sylow(r`ims[f],q);
    SP[i] := [ ((Generic(r`ims[f]))!(ISP[i].j)) @ Function(r`fromfacs[f]) :
    //SP[i] := [ (ISP[i].j) @ Function(r`fromfacs[f]) :
                                               j in [1..Ngens(ISP[i])] ];
    if hasp and i in OIAPreps then //need these generators for result
       for g in SP[i] do
         Append(~rgens, MakeNormRP(g) );
       end for;
    end if;
  end for;

  //And the function to normalise this
  MakeNormSP := function(g)
    local cgens, icgens, imnode, y, ww, imi, f, QI, c, ord, hasp, q;
    for i in [1..#socfacs] do
      cgens := [ x^g : x in SP[i] ];
      imi := i ^ (g @ r`Gtosocperm); //Q should be in socfacs[imi];
      f := socfacs[imi];
      hasp := r`factorord[f] mod p eq 0;
      q := hasp select p else 2;
      //have to strip cgens to get image in ims[f]
      icgens := [];
      for x in cgens do
        y := x;
        imnode := CompositionTreeFactorNumber( G, y ) - 1;
        assert r`factortype[imnode] le 2;
        while r`factortype[imnode] eq 1 do
          ww := (y^-1) @
              Function(r`tofacs[imnode]) @ Function(r`factoword[imnode]);
          y *:= Evaluate( ww, r`Y[imnode] );
          imnode := CompositionTreeFactorNumber( G, y ) - 1;
          assert r`factortype[imnode] le 2;
        end while;
        assert imnode eq f;
        y := y @ Function(r`tofacs[f]);
        ord := Order(y);
        Append(~icgens, y^(ord div q^Valuation(ord,q)) );
      end for;
      QI := sub< Generic(r`ims[f]) | icgens >;
/* next command is sometimes hanging, so bypass it if possible */
      if r`sfclass[imi] then
         flag := RandomSchreierBounded (r`ims[f], 200000 : Run:=200 );
         if flag then
           vprint LMG, 3: "      Using IsConjugate in Sylow";
           _, c := IsConjugate(r`ims[f], QI, ISP[imi]);
           vprint LMG, 3: "      Done";
         else
           vprint LMG, 3: "      Using ClassicalSylowConjugation in Sylow";
           c := ClassicalSylowConjugation(r`ims[f], QI, ISP[imi]);
           vprint LMG, 3: "      Done";
         end if;
      else
         _, c := IsConjugate(r`ims[f], QI, ISP[imi]);
      end if;
      g := g * (c @ Function(r`fromfacs[f]) );
    end for;
    return MakeNormRP(g);
  end function;

  //Now the PKer level
  IKP := Sylow(r`pkerPC, p);
  gens :=  [ MakeNormSP( g @@ r`pkertoPC ) : g in Generators(IKP) ];
  rgens cat:= gens;
  KP := sub< GG | gens >; 

  MakeNormKP := function(g)
    local Q, c;
    Q := sub< r`pkerPC | [ (x^g) @ r`pkertoPC : x in Generators(KP) ] >;
    _, c := IsConjugate( r`pkerPC, Q, IKP );
    return MakeNormSP( g * (c @@ r`pkertoPC) );
  end function;

  //finally the top level - we defined IAP earlier
  gens := [ MakeNormKP( g @@ r`Gtosocperm ) : g in Generators(IAP) ]; 
  rgens cat:= gens;

  P := sub< GG | rgens >;
  //Usually P is a p-group but occasionally not.
  //Use an order test to see, and recurse if not.
  PP := RandomProcess(P);
  for i in [1..100] do
    x := Factorisation(Order(Random(PP)));
    if #x gt 0 and (#x gt 1 or x[1][1] ne p) then
       vprint LMG,1: "Recursing in Sylow subgroup computation";
       //return $$(P, p);
       return LMGSylow(P, p);
    end if;
  end for;

  LMGInitialize(P : Verify := G`LMGNode`verified );
  if #FactoredOrder(P) gt 1 then
       vprint LMG,1: "Recursing (final) in Sylow subgroup computation";
       //return $$(P, p);
       return LMGSylow(P, p);
  end if;
  return P;
end function;
