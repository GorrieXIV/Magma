freeze;

/*
 * This file contains the functions to do the following:
 * Input: Almost simple group $G$ with Soc(G) = PSp(4,q), and the
 * prime power p^e. We assume e > 1, as PSp(4, p) was done as
 * a special case.
 * Output: Set of maximal subgroups of $G$, intersected with
 * Soc(G). Trivialities are not returned.
 *
 */

//function names:
//WhichGroup(group, d, q)
//GetImprims(q)
//GetL2q(q)
//SubfieldSp(d, p, e, f)
//S4qMaximals(group, q)

import "sympreds.m" : IsotropicStabSp, PointStabSp;
import "subfield.m" : SubfieldSp;
import "superfield.m" : GammaSp, GammaUMeetSp;
import "gl2.m": GSp, PGammaSp, AutPSp4;
import "psp4p.m" : MakeSpHomomGeneral;
import "sp4novelties.m": NoveltyReduct, NoveltySemilin, NoveltyImprims;

function WhichGroup(group, d, q)
  if d eq 1 then
    return Socle(group), 1;
  end if;
  fac:= Factorisation(q);
  e:= fac[1][2];

  assert d eq 2;
  psp:= Socle(group);
  assert #psp eq #PSp(4, q);
  socquot, f:= quo<group|psp>;
  if IsOdd(#socquot) then
    return psp, 2;
  end if;
  if not IsCyclic(socquot) then
    return psp, 0;
  end if;

  s2:= SylowSubgroup(group, 2);
  biggrp:= PSigmaSp(4, q);
  ns:= NormalSubgroups(biggrp: IndexLimit:= e div (#socquot));
  assert (#biggrp div ns[1]`order) eq (e div #socquot);
  s2sigma:= SylowSubgroup(ns[1]`subgroup, 2);
  cls_g:= Classes(s2);
  cls_sigma:= Classes(s2sigma);
  info_g:= [<cls_g[i][1], cls_g[i][2]>: i in [1..#cls_g]];
  info_sigma:= [<cls_sigma[i][1], cls_sigma[i][2]>: i in [1..#cls_sigma]];
  if info_g eq info_sigma then
    return psp, 2;
  else
    return psp, 0;
  end if;
end function;

/**********************************************************************/

/*
 * To make the 2nd group we use act as gens of gl on (e1, e2) 
 * and compensate on f1, f2, or swap the subspaces over. 
 */

function GetImprims(q)
    z:= PrimitiveElement(GF(q));

    g:= WreathProduct(Sp(2, q), Sym(2));
    bool, form:= SymplecticForm(g);
    //"form_g =", form;
    x:= GL(4, q)!CorrectForm(form, 4, q, "symplectic");
    imprim1:= g^x;

    newmat1:= GL(4, q)!DiagonalMatrix([z, 1, 1, z^-1]);
    newmat2:= GL(4, q)![-1, 1, 0, 0,
                    -1, 0, 0, 0, 
                     0, 0, -1, -1,
                     0, 0, 1, 0];
    newmat3:= GL(4, q)![0, 0, -1, 0,
                        0, 0, 0, -1,
                        1, 0, 0, 0,   
                        0, 1, 0, 0];
    imprim2:= sub<GL(4, q)|newmat1, newmat2, newmat3>;

    return imprim1, imprim2;
end function;


/******************************************************************/

function GetL2q(q)
    g:= SL(2, q);
    module:= GModule(g);	
    power:= TensorPower(module, 3); 
    indecs:= IndecomposableSummands(power);
    assert exists(newmod){x: x in indecs | Dimension(x) eq 4};
    group:= sub<GL(4, q)|ActionGenerators(newmod)>;

    bool, form1:= SymplecticForm(group);
    assert bool;
    x:= GL(4, q)!CorrectForm(form1, 4, q, "symplectic");
    newgroup:= group^x;

    return newgroup;
end function;

/*****************************************************************/


/* this seems to be in subfield.m
function SubfieldSp(d, p, e, f)
  assert IsPrime(p);
  assert e mod f eq 0;

  newgens:= [GL(d, p^e)!Sp(d, p^f).i : i in [1, 2]];

  if IsEven(p) or IsOdd(e div f) then
    return sub<GL(d, p^e)|newgens>;
  end if;

  z:= PrimitiveElement(GF(p^e));
  l:= d div 2;
  
  power:= (p^e-1) div (p^f-1);
  delta:= GL(d, p^e)!DiagonalMatrix([z^power:i in [1..l]]cat[1:i in [1..l]]);
  assert IsEven(power);
  scal_power:= power div 2;
  Append(~newgens, delta*GL(d, p^e)!ScalarMatrix(d, z^-scal_power));
  return sub<GL(d, p^e)|newgens>;
end function; 
*/

/*******************************************************************
*                   The main function                              *
********************************************************************/

forward MakeSp4EvenHomomGeneral;

function Sp4qMaximals(group, q : max:= true, Print:=0)

  //out eq  GCD(q-1,2):e;
  fac:= Factorisation(q);
  p:= fac[1][1]; e:= fac[1][2];
  assert #fac eq 1;
  assert e gt 1;
  d:= Gcd(Gcd(q-1, 2), e);

  soc, subgrp_copies:= WhichGroup(group, d, q);
  si := Index(group,soc);
  e2part := e mod 2 eq 0 select Factorisation(e)[1][2] else 0;
  si2part := si mod 2 eq 0 select Factorisation(si)[1][2] else 0;
  novelties := p mod 2 eq 0 and e2part+1 eq si2part;
  //that is when the graph automorphism of PSp(4,2^e) is present
  //and we get novelties.
  if Print gt 1 then "Novelties =", novelties; end if;
  
  if Print gt 1 then "subgrp_copies =", subgrp_copies; end if;

  if Print gt 1 then print "making standard group"; end if;
  sp:= Sp(4, q);
  gsp := GSp(4, q);
  z:= PrimitiveElement(GF(q));
  out_invol:= GL(4, q)!DiagonalMatrix([z, z, 1, 1]);
  apsp := q mod 2 eq 0 select AutPSp4(q) else PGammaSp(4, q);

  factor := hom< gsp->apsp | [apsp.i :  i in [1..Ngens(gsp)]] >;
  psp := sp @ factor;

  if Print gt 1 then "Setting up homomorphism"; end if;
  if p mod 2 eq 1 then
    homom, soc, group:=
     MakeSpHomomGeneral(group, 4, p, e, psp, apsp, factor : Print:=0);
  else 
    homom, soc, group:=
     MakeSp4EvenHomomGeneral(group, e, psp, apsp, factor : Print:=0);
  end if;

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psp | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);

  //get apsp right
  newgens := [ apsp | group.i @ homom : i in [1..Ngens(group)] ];
  subapsp := sub< apsp | newgens >;
  for g in Generators(apsp) do if not g in subapsp then
     Append(~newgens,g); subapsp := sub< apsp | newgens >;
  end if; end for;
  apsp := subapsp;

  maximals:= [];
  if not max then
    return homom, apsp, maximals, F, phi;
  end if;

  if Print gt 1 then "getting reducibles"; end if;
  if novelties then
    Append(~maximals, NoveltyReduct(q)@factor);
  else
    //Append(~maximals, Stabiliser(psp, 1));
    Append(~maximals, PointStabSp(4, q)@factor);
    Append(~maximals, IsotropicStabSp(4, q, 2)@factor);
  end if;

  if Print gt 1 then "getting imprimitives"; end if;
  if novelties then
    max1, max2 := NoveltyImprims(q);
    if q gt 4 then Append(~maximals, max1@factor); end if;
    Append(~maximals, max2@factor);
  else
    a, b:= GetImprims(q);
    Append(~maximals, a@factor);
    if IsOdd(q) then
      Append(~maximals, b@factor);
    end if;
  end if;

  if Print gt 1 then "getting semilinears"; end if;
  if novelties then
    Append(~maximals, NoveltySemilin(q)@factor);
  else
    Append(~maximals, GammaSp(4, q, 2)@factor);
    if IsOdd(q) then
      Append(~maximals, GammaUMeetSp(4, q)@factor);
    end if;
  end if;

  e_fac:= Factorisation(e);
  if Print gt 1 then "getting subfields"; end if;
  for x in e_fac do
    b:= x[1];
    if b eq 2 and subgrp_copies gt 0 then
      grp:= SubfieldSp(4, p, e, e div b);
      Append(~maximals, grp@factor); 
      if subgrp_copies gt 1 then
        Append(~maximals,(grp^out_invol)@factor);
      end if;
    elif b gt 2 then
      Append(~maximals,SubfieldSp(4,p,e,e div b)@factor);
    end if;
  end for;

  if IsEven(q) then
    if not novelties then
      if Print gt 1 then "getting orthogonals"; end if;
      Append(~maximals, SOPlus(4, q)@factor);
      sominus:= SOMinus(4, q);
      bool, form:= SymplecticForm(sominus);
      assert bool;
      mat:= CorrectForm(form, 4, q, "symplectic");
      Append(~maximals, (sominus^mat)@factor);
    end if;
    if IsOdd(e) then
      if Print gt 1 then "getting suzuki"; end if;
      suz:= ChevalleyGroup("2B", 2, q);
      Append(~maximals, suz@factor);
    end if;
  end if;

  //There is a maximal C_9 subgroup isomorphic to PSL(2, q) whenever
  //p \geq 5  
  if p gt 4 then 
    if Print gt 1 then "getting L(2, q)"; end if;
    a:= GetL2q(q);
    Append(~maximals, a@factor);
  end if;
  
  return homom, apsp, maximals, F, phi;
end function;

function PSp4qIdentify(group, q: max:=true, Print:=0)
    return Sp4qMaximals(group, q: max:=max, Print:=Print);
end function;

MakeSp4EvenHomomGeneral :=
                  function(group, e, psp, apsp, factor : Print:=0)
  local works, GtoSp, SptoG, mat, homom, ims,
    g, newgens, subsoc, subgp, pspgens, imgens, CG, ce, isc, h, socle;

  soc := Socle(group);
  /* Reduce number of generators of soc, and
   * rearrange generators of group to get those of soc coming first
   */
  d:=4; p:=2;
  repeat
    newgens := [ group | Random(soc), Random(soc) ];
    subsoc := sub<soc|newgens>; RandomSchreier(subsoc);
  until subsoc eq soc;
/*
  while subsoc ne soc do
    x:=Random(soc);
    while x in subsoc do x:=Random(soc); end while;
    Append(~newgens,x); subsoc := sub<soc|newgens>; RandomSchreier(subsoc);
  end while;
*/
  soc := subsoc;
  subgp := subsoc;
  for g in Generators(group) do
   if not g in subgp then Append(~newgens,g);
     subgp := sub< group | newgens >; RandomSchreier(subgp);
   end if;
  end for;
  group := subgp;

  works := false;
  while not works do
    //works, GtoSp, SptoG := RecogniseSp4Even(soc,p^e);
    //use Eamonn's new function
    works, GtoSp, SptoG := RecogniseSp4(soc,p^e);
  end while;

  pspgens := [];
  for  i in [1..Ngens(soc)] do
      mat := GtoSp(soc.i);
      Append(~pspgens,mat@factor);
  end for;
    //Now identify images of all generators of group in apsp.
  ims := pspgens;
  for i in [Ngens(soc)+1..Ngens(group)] do
      g := group.i;
      CG := apsp; ce := Id(apsp);
      for j in [1.. #pspgens] do
        mat := GtoSp(soc.j^g);
        isc, h := IsConjugate(CG,pspgens[j]^ce,mat@factor);
        if not isc then error "Conjugation error in Aut(PSp(d,q))"; end if;
        CG := Centraliser(CG,mat@factor);
        ce := ce*h;
      end for;
      Append(~ims,ce);
  end for;
  return hom< group -> apsp | ims >, soc, group;
end function;
