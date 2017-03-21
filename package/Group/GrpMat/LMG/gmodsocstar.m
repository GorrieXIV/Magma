freeze;

import "outers.m": GOMinusSO;
import "autinfo.m": AutTuple;
import "autinfo.m":  IdentifyOuterAutG;
/* We attempt to construct a homomorphism from G to a permutation group
 * isomorphic to G/SocleStar(G) for LMG group.
 */

/* We need to know the automorphism groups of the classical groups
 * We return presentations for these - we will use their regular permutation
 * representations eventually.
 */
AutSL := function(d,p,e)
  local fac, diag;
  diag := GCD(d,p^e-1);
  if d eq 2 then //no duality
    if e eq 1 then //no field
      return Group<x|x^diag>;
    end if;
    if diag eq 1 then return Group<y|y^e>; end if;
    return Group<x,y | y^e, x^diag, x^y = x^p >;
  else
    if e eq 1 then //no field
      if diag eq 1 then return Group<x|x^2>; end if;
      return Group<x,z | z^2, x^diag, x^z = x^-1 >;
    end if;
    if diag eq 1 then return Group<y,z | z^2,y^e,(z,y) >; end if;
    return Group<x,y,z | z^2, y^e, (z,y), x^diag, x^z = x^-1, x^y = x^p >;
  end if;
end function;

AutSU := function(d,p,e)
  local fac, diag;
  diag := GCD(d,p^e+1);
  if diag eq 1 then return Group<y|y^(2*e)>; end if;
  return Group<x,y | y^(2*e), x^diag, x^y = x^p >;
end function;

AutSp := function(d,p,e)
  local fac, diag;
  diag := GCD(2,p-1);
  if d ne 4 or IsOdd(p) then
    if e eq 1 then //no field
      return Group<x|x^diag>;
    end if;
    if diag eq 1 then return Group<y|y^e>; end if;
    return Group<x,y | y^e, x^diag, (y,x) >;
  end if;
  //our convention for outer aut of PSp(4,2^e) is that it squares into
  //field automorphism entry->entry^2
  return Group<y,z | z^2=y, y^e >;
end function;

AutO := function(d,p,e)
  local fac, diag;
  if e eq 1 then //no field
    return Group<x|x^2>;
  end if;
  return Group<x,y | y^e, x^2, (y,x) >;
end function;

AutOPlus := function(d,p,e)
  local fac, diag;
  if IsEven(p) then
    if e eq 1 then //no field
      if d eq 8 then return Group<x,t|x^2,(x*t)^2,t^3>; end if;
      return Group<x|x^2>;
    end if;
    if d eq 8 then return Group<x,y,t|y^e,x^2,(x*t)^2,t^3,(y,x),(y,t)>;
    end if;
    return Group<x,y | y^e, x^2, (y,x) >;
  end if;
  if d mod 4 eq 2 and p^e mod 4 eq 3 then //no spinor term component
    if e eq 1 then //no field
      return Group<z1,z2 | z1^2, z2^2, (z1,z2) >;
    end if;
    return Group<z1,z2,y | y^e, (y,z1), (y,z2), z1^2, z2^2, (z1,z2) >;
  end if;
  if e eq 1 then //no field
    if d eq 8 then
      return Group<z1,z2,z3,t | z1^2, z2^2, z3^2, (z2,z3)=z1, (z1,z3), (z1,z2),
             t^3, z3^t=z1, z1^t=z1*z3, (z2*t)^2 >;
    end if;
    return Group<z1,z2,z3 | z1^2, z2^2, z3^2, (z2,z3)=z1, (z1,z3), (z1,z2) >;
  end if;
  if d eq 8 then
    return Group<z1,z2,z3,y,t | y^e, (y,z1), (y,z2), (y,z3), z1^2, z2^2, z3^2,
      t^3, z3^t=z1, z1^t=z1*z3, (z2*t)^2,(t,y), (z2,z3)=z1, (z1,z3), (z1,z2) >;
  end if;
  return Group<y,z1,z2,z3 | y^e, (y,z1), (y,z2), (y,z3), z1^2, z2^2, z3^2,
                                               (z2,z3)=z1, (z1,z3), (z2,z2) >;
end function;

AutOMinus := function(d,p,e)
  local fac, diag;
  if IsEven(p) then
    if e eq 1 then //no field
      return Group<x|x^2>;
    end if;
    if IsOdd(e) then
      return Group<x,y | y^e, x^2, (y,x) >;
    end if;
    return Group<x,y | y^e=x, x^2, (y,x) >;
  end if;
  if d mod 4 eq 0 or p^e mod 4 eq 1 then //no spinor term component
    if e eq 1 then //no field
      return Group<z1,z2 | z1^2, z2^2, (z1,z2) >;
    end if;
    if IsOdd(e) then
      return Group<z1,z2,y | y^e, (y,z1), (y,z2), z1^2, z2^2, (z1,z2) >;
    end if;
    return Group<z1,z2,y | y^e=z1, (y,z1), (y,z2), z1^2, z2^2, (z1,z2) >;
            //z2 is the GO-SO automorphism
  end if;
  if e eq 1 then //no field
    return Group<z1,z2,z3 | z1^2, z2^2, z3^2, (z2,z3)=z1, (z1,z3), (z1,z2) >;
  end if;
  return Group<z1,z2,z3,y | y^e, (y,z1), (y,z2), (y,z3), z1^2, z2^2, z3^2,
                                               (z2,z3)=z1, (z1,z3), (z1,z2) >;
         //note e must be odd in this case
end function;

//For the identify triple functions, we express a triple as returned by
//AutTuple as an element of the relevant automorphism group.
//results are returned as sequence of generator exponent pairs

ITSL := function(t,d,p,e)
  w := PrimitiveElement(GF(p^e));
  lg := Log(w, Determinant(t[3]));
  dc := lg mod GCD(d,p^e-1);
  eg := 1; gg := 1;
  if GCD(d,p^e-1) ne 1 then eg +:= 1; gg +:= 1; end if;
  if e gt 1 then gg +:= 1; end if;
  if t[1] eq 0 then
     if t[2] eq 0 then
       if dc eq 0 then return []; end if;
       return [ <1,dc> ];
     end if;
     if dc eq 0 then return [ <eg,t[2]> ]; end if;
     return [ <eg,t[2]>, <1,dc> ];
  end if;
  if t[2] eq 0 then
     if dc eq 0 then return [ <gg,t[1]> ]; end if;
     return [ <gg,t[1]>, <1,dc> ];
   end if;
  if dc eq 0 then return [ <gg,t[1]>, <gg,t[2]> ]; end if;
  return [ <gg,t[1]>, <eg,t[2]>, <1,dc> ];
end function;

MatToQ := function(A,q)
// raise every element of matrix A to q-th power
   local B;
   B := MatrixAlgebra(BaseRing(A),Nrows(A))!0;
   for i in [1..Nrows(A)] do for j in [1..Ncols(A)] do
      B[i][j] := A[i][j]^q;
   end for; end for;
   return B;
end function;

ITSU := function(t,d,p,e)
  //make t[3] fix form
  isf, form := UnitaryForm(GU(d,p^e));
  formim := t[3] * form * MatToQ(Transpose(t[3]), p^e);
  for i in [1..d] do if form[1][i] ne 0 then
    scal := formim[1][i]/form[1][i];
    assert formim eq scal * form;
    break;
  end if; end for;
  isp, scalrt := IsPower(scal,p^e + 1); assert isp;
  t[3] *:= ScalarMatrix(d, scalrt^-1);

  w := PrimitiveElement(GF(p^(2*e)));
  lg := Log(w, Determinant(t[3]));
  assert lg mod (p^e - 1) eq 0;
  lg := lg div (p^e - 1);
  dc := lg mod GCD(d,p^e+1);
  eg := GCD(d,p^e+1) eq 1 select 1 else 2;
  if t[2] eq 0 then
     if dc eq 0 then return []; end if;
     return [ <1,dc> ];
  end if;
  if dc eq 0 then return [ <eg,t[2]> ]; end if;
  return [ <eg,t[2]>, <1,dc> ];
end function;

ITSp := function(t,d,p,e)
  if d eq 4 and p eq 2 then
    if t[1] eq 0 then
     if t[2] eq 0 then return []; end if;
     return [ <1,t[2]> ];
    end if;
    if t[2] eq 0 then return [ <2,t[1]> ];
     return [ <2,t[1]>, <1,t[2]> ];
    end if;
  end if;
  if IsOdd(p) then
    isit, form := SymplecticForm(Sp(d,p^e));
    g := t[3];
    formim := g * form * Transpose(g);
    for i in [1..d] do if form[1][i] ne 0 then
       scal := formim[1][i]/form[1][i];
       assert formim eq scal * form;
       break;
    end if; end for;
    dc:= IsSquare(scal) select 0 else 1;
    eg := 2;
  else
    dc := 0; eg := 1;
  end if;
  if t[2] eq 0 then
     if dc eq 0 then return []; end if;
     return [ <1,dc> ];
   end if;
  if dc eq 0 then return [ <eg,t[2]> ]; end if;
  return [ <eg,t[2]>, <1,dc> ];
end function;

ITO := function(t,d,p,e : gp:=GO )
  isit, form := SymmetricBilinearForm(gp(d,p^e));
  //make it fix the form
  g := t[3];
  formim := g * form * Transpose(g);
  for i in [1..d] do if form[1][i] ne 0 then
     scal := formim[1][i]/form[1][i];
     assert formim eq scal * form;
     break;
  end if; end for;
  isp, scalrt := IsSquare(scal); assert isp;
  g := g * ScalarMatrix(d, scalrt^-1);
  dc := SpinorNorm(GL(d,p^e)!g,form);
  if t[2] eq 0 then
     if dc eq 0 then return []; end if;
     return [ <1,dc> ];
   end if;
  if dc eq 0 then return [ <2,t[2]> ]; end if;
  return [ <2,t[2]>, <1,dc> ];
end function;

ITOPlus := function(t,d,p,e,comat)
  if p eq 2 then
    t1 := t[1];
    if d ne 8 or t1 eq 0 then return ITO(t,d,p,e : gp:=GOPlus); end if;
    t[1] := 0;
    t := ITO(t,d,p,e : gp:=GOPlus);
    gg := e eq 1 select 2 else 3;
    if t1 eq 3 then return [<gg,1>] cat t; end if;
    return [<gg,2>] cat t;
  end if;
  d8 := d mod 4 eq 0 or p^e mod 4 eq 1;
  eg := d8 select 4 else 3;
  dg1 := d8 select 3 else 2;
  gg2 := d8 select 2 else 1;
  t1 := t[1];
  if t1 ne 0 then
    t[1] := 0;
    t := $$(t,d,p,e,comat);
    gg := e eq 1 select eg else eg + 1;
    if t1 eq 3 then return [<gg,1>] cat t; end if;
    return [<gg,2>] cat t;
  end if;

  //here we have work to do
  ans := t[2] ne 0 select [ <eg,t[2]> ] else [];
  isit, form := SymmetricBilinearForm(GOPlus(d,p^e));
  g := t[3];
  formim := g * form * Transpose(g);
  for i in [1..d] do if form[1][i] ne 0 then
     scal := formim[1][i]/form[1][i];
     assert formim eq scal * form;
     break;
  end if; end for;
  isp, scalrt := IsSquare(scal);
  if not isp then
     Append(~ans, <dg1,1>);
     g := comat * g;
     formim := g * form * Transpose(g);
     for i in [1..d] do if form[1][i] ne 0 then
        scal := formim[1][i]/form[1][i];
        assert formim eq scal * form;
        break;
     end if; end for;
     isp, scalrt := IsSquare(scal); assert isp;
  end if;
  g := g * ScalarMatrix(d, scalrt^-1);
  if Determinant(g) ne 1 then
     Append(~ans, <gg2,1>);
     g := GOMinusSO(d,p^e,1) * g;
  end if;
  if d8 and SpinorNorm(GL(d,p^e)!g, form) eq 1 then
    Append(~ans, <1,1>);
  end if;
  return ans;
end function;

ITOMinus := function(t,d,p,e,comat)
  if p eq 2 then return ITO(t,d,p,e : gp:=GOMinus); end if;
  d8 := d mod 4 eq 2 and p^e mod 4 eq 3;
  eg := d8 select 4 else 3;
  dg1 := d8 select 3 else 2;
  gg := d8 select 2 else 1;
  //here we have work to do
  ans := t[2] ne 0 select [ <eg,t[2]> ] else [];
  isit, form := SymmetricBilinearForm(GOMinus(d,p^e));
  g := t[3];
  formim := g * form * Transpose(g);
  for i in [1..d] do if form[1][i] ne 0 then
     scal := formim[1][i]/form[1][i];
     assert formim eq scal * form;
     break;
  end if; end for;
  isp, scalrt := IsSquare(scal);
  if not isp then
     Append(~ans, <dg1,1>);
     g := comat * g;
     formim := g * form * Transpose(g);
     for i in [1..d] do if form[1][i] ne 0 then
        scal := formim[1][i]/form[1][i];
        assert formim eq scal * form;
        break;
     end if; end for;
     isp, scalrt := IsSquare(scal); assert isp;
  end if;
  g := g * ScalarMatrix(d, scalrt^-1);
  if Determinant(g) ne 1 then
     Append(~ans, <gg,1>);
     g := GOMinusSO(d,p^e,1) * g;
  end if;
  if d8 and SpinorNorm(GL(d,p^e)!g, form) eq 1 then
    Append(~ans, <1,1>);
  end if;
  return ans;
end function;

PermRepSum := function(G,reps)
/* reps should be a list of homomorphisms from group G to permutation
 * groups (subgroups of Sym(n_i)). The summed permutation representation
 * reps[1]+..resp[r] of degree n_1+n_2+..n_r is returned, together
 * with the image group.
 */
  local nreps, degrees, phi, cdphi, img, sumdeg, deg, im;
  nreps := #reps;
  degrees := [];
  sumdeg := 0;
  for j in [1..nreps] do
    phi:=reps[j];
    cdphi :=  Codomain(phi);
    degrees[j]:=Degree(cdphi);
    sumdeg +:= degrees[j];
  end for;
  deg:=sumdeg;

  //The codomain of the summed representation will be the direct product of the
  //codomains of the given maps.

  ImRep := function(g)
    local img, sumdeg, r;
    img:=[];
    sumdeg:=0;
    for j in [1..nreps]  do
      r := g @ reps[j];
      for k in [1..degrees[j]] do
        img[sumdeg+k] := sumdeg + k^r;
      end for;
      sumdeg +:= degrees[j];
    end for;
    return Sym(deg)!img;
  end function;

  im := sub< Sym(deg) | [ ImRep(G.i) : i in [1..Ngens(G)]] >;
  return map< Generic(G) -> im  | g :-> ImRep(g) >, im;

end function;

Gmodsocstar := procedure(G)
  local r, factortype, socperm, Gtosocperm, sfclass, fromfacs, tofacs, ims,
   cslen, socfacs, O, homs, oa, oi, opts, T, isc, g, sfno, sf, ai, sfc, gsfi,
   d, q, fac, p, e, imgp, injb, injt, m, im, wg, iwm, triv, o8plus, gaut;
  r := G`LMGNode;
  factortype := r`factortype;
  socperm := r`socperm;
  Gtosocperm := r`Gtosocperm;
  sfclass := r`sfclass;
  fromfacs := r`fromfacs;
  tofacs := r`tofacs;
  ims := r`ims;
  cslen := #factortype;
  socfacs := [ i : i in [1..cslen] | factortype[i] eq 2 ];
  O := Orbits(socperm);
  homs := [* *];
  for o in O do
    oa, oi := OrbitAction(socperm, o);
    //We will order the points on o to correspond to those in oi
    opts := [ i @@ oa : i in [1..#o] ];
    T := [ Generic(G) | Id(G)];
    for i in [2..#o] do
      isc, g := IsConjugate(socperm, opts[1], opts[i]);
      T[i] := g @@ Gtosocperm;
    end for;
    //construct target group for homomorphism
    sfno := socfacs[ o[1] ];
    sf := ims[sfno]; //the socle factor for this orbit
    if not assigned sf`AutInfo then
      ag := Sym(1);
    else
      ai := sf`AutInfo;
      sfc := sfclass[ o[1] ];
      if sfc then //classical type
        ai := sf`AutInfo;
        d := Dimension(sf);
        q := #BaseRing(sf);
        fac := Factorisation(q);
        p := fac[1][1]; e := fac[1][2];
        if ai`type eq "U" then e := e div 2; end if;
        vprint LMG,3: "socle factor of type",ai`type;

        case ai`type:
          when "L": ag := AutSL(d,p,e);
          when "U": ag := AutSU(d,p,e);
          when "S": ag := AutSp(d,p,e);
          when "O": ag := AutO(d,p,e);
          when "O+": ag := AutOPlus(d,p,e);
          when "O-": ag := AutOMinus(d,p,e);
        end case;
        ag := CosetImage(ag,sub<ag|>);
      else
        ag := ai`outautgp; 
        d:=0; p:=0; e:=0;  //not sure why that should be necessary!
      end if;
    end if;
    if #ag gt 1 then
       imgp, injb, injt := WreathProduct(ag, oi);
    else
      d:=0; p:=0; e:=0;
      imgp := oi; injb := 0; injt := 0; sfc := 0; ai := 0;
    end if;
    ImElt := function(g) //image of an element g in G under map to imgp
      local im, el, atup, gaut;
      //vprint LMG,3: "evaluating an image";
      if #ag eq 1 then
         return g @ Gtosocperm @ oa;
      end if;
      im := g @ Gtosocperm @ oa @ injt;
      for i in [1..#o] do
        el := (T[i] * g^-1) @ Gtosocperm @ oa;
        el := T[ 1^el ] * g * T[i]^-1; //should normalise socle factor
        genims :=
     [ ((sf.i @ Function(fromfacs[sfno]))^el) @ Function(tofacs[sfno]) :
                                                        i in [1..Ngens(sf)] ];
        if sfc then
          o8plus := ai`type eq "O+" and Dimension(sf) eq 8;
          if o8plus then
            gaut := ai`gaut;
            gsfi := [ gaut(sf.i) @ Function(fromfacs[sfno])
                     : i in [1..Ngens(sf)] ];
            genims1 := [ (x^el) @ Function(tofacs[sfno]) : x in gsfi ];
            gsfi := [ gaut(gaut(sf.i)) @ Function(fromfacs[sfno])
                     : i in [1..Ngens(sf)] ];
            genims2 := [ (x^el) @ Function(tofacs[sfno]) : x in gsfi ];
          else genims1:=[]; genims2:=[];
          end if;

          atup := AutTuple(sf, genims : genims1:=genims1, genims2:=genims2 );
//atup:Magma;
          case ai`type:
            when "L": a := ITSL(atup,d,p,e);
            when "U": a := ITSU(atup,d,p,e);
            when "S": a := ITSp(atup,d,p,e);
            when "O": a := ITO(atup,d,p,e);
            when "O+":a := ITOPlus(atup,d,p,e, ai`comat);
            when "O-":
                     if atup[2] ne 0 then
                        atup[3] := ai`cmat[atup[2]]^-1 * atup[3];
                     end if;
                     a := ITOMinus(atup,d,p,e, ai`comat);
          end case;
          gaut := Id(ag);
          for t in a do gaut *:= (ag.t[1])^t[2]; end for;
        else
          gaut := IdentifyOuterAutG(sf, genims);
        end if;
        im *:= gaut @ injb[i];
      end for;
      return im;
    end function;

    Append( ~homs, map< Generic(G)->imgp | g :-> ImElt(g) > );
  end for; //for o in O do

  //also need inverse map
  m, im := PermRepSum(G,homs);
  vprint LMG,3: "image of order",#im;
  wg := WordGroup(im); iwm := InverseWordMap(im);
  G`LMGNode`GtoGmodsocstar := map< Generic(G)->im | g :-> m(g),
                      g :-> Evaluate( iwm(g), [G.i : i in [1..Ngens(G)]] ) >;
  G`LMGNode`Gmodsocstar := im;
end procedure;
