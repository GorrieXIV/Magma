freeze;

import "spinor.m": InOmega;

/************************************************************************
 * ChangeMat returns either Tranpose(Frobenius(mat)) or
 * Transpose(mat), depending on whether we have a form s.t.
 * g*form*Transpose(g) = form or g * form*(Transpose(Frobenius(g)))
 * = form.
 */

ListMatToQ:= function(a, q)
// raise every element of matrix A to q-th power.
list:= Eltseq(a);
for i in [1..#list] do list[i]:= list[i]^q;
end for;
return list;
end function;

function ChangeMat(mat, type, d, p)
  if type cmpeq "unitary" then
    return Transpose(GL(d, p^2)!ListMatToQ(mat, p));
  else
    return Transpose(mat);
  end if;
end function;

ReduceOverFiniteField := function(L, q: 
                            special:=false, general:=false, normaliser:=false)
/* L should be "lattice record" with components:
 * G: A finite irreducible quasisimple 2-generator matrix group over Z
 * F: FreeGroup(2),
 * AI: list of automorphisms of G described by generator images given as
 *     words in F
 * q = prime power, special = true/false
 * Reduce G over GF(q) and find irreducible constituents of corresponding
 * module. Work out action of automorphisms on these constituents,
 * appending any new modules found to the list
 * Choose orbit representatives of this action, and for each orbit
 * append reduced group by any stabilizing automorphisms.
 *
 * By default, the subgroup of the relevant quasisimple group is returned.
 * If special is true (case O only), normaliser in SO is returned.
 * If general is true (cases L/U/O), normaliser in GL, GU, GO is returned.
 * If normaliser is true (cases Sp/U/O) normaliser in GL is returned.
 * Return list of resulting groups, one for each orbit.
 */

  local stuff, d, F, G, AI, Q, M, C, AC, na, nc, perms, phi, M2, i, new, AG,
               OAG, gens, a, gps, isit, iso, w, po, u, v, x, ox, f, ww, ff,
               sgens, sAG, co, rts, got, forms, form, rq, lv, quad, g,
               mat, tmat, CC;
  if normaliser then general:=true; end if;
  if general then special:=true; end if;
  G := L`G; AI := L`AI; F := L`F;
  d := Dimension(G);
  Q := sub< GL(d,q) | G.1, G.2 >;
  M := GModule(Q);
  C := Constituents(M);
  CC := [];
  for c in C do
    if not IsAbsolutelyIrreducible(c) then
      error "Constituents are not absolutely irreducible over finite field.";
    end if;
    //if Dimension(c) eq 1 then
      //"Module has a trivial constituent.";
    //else Append(~CC,c);
    if Dimension(c) ne 1 then Append(~CC,c);
    end if;
  end for;
  C := CC;
  AC := [ ActionGroup(c) : c in C ];
  modims := [];
  i := 1;
  while i le #C do
    modims[i] := [];
    phi := hom< F->AC[i] | AC[i].1, AC[i].2 >;
    for a in AI do
      M2 := GModule(Q,[phi(a[1]),phi(a[2])]);
      new := true;
      for j in [1..#C] do if IsIsomorphic(C[j],M2) then
        Append(~modims[i],j); new := false; break;
      end if; end for;
      if new then
        Append(~C,M2); Append(~AC,ActionGroup(M2)); Append(~modims[i],#C);
      end if;
    end for;
    i +:= 1;
  end while;

  nc := #C;
  na := #AI;
  perms := [ Sym(nc) | [modims[i][j] : i in [1..nc]] : j in [1..na] ];

  AG := sub< Sym(nc) | perms >;
  OAG := Orbits(AG);
  gps := [];
  w := PrimitiveElement(GF(q));
  for o in OAG do
    i := Representative(o);
    d := Degree(AC[i]);
    //test if the group fixes a form, and act accordingly.
    forms := ClassicalForms(AC[i]);
    case forms`formType:
    when "linear" :
      ww := general select w
            else w^((q-1) div GCD(q-1,d)); //power of w s.t. ww I_d has det 1
      gens := [ GL(d,q) | AC[i].j : j in [1..Ngens(AC[i]) ]];
    //find generators of subgroup of automorphism group stabilizing this module
      sgens := [];
      for j in [1..na] do if i^perms[j] eq i then
        Append(~sgens,j);
      end if; end for;
      for j in sgens do
        //Attempt to append this automorphism to AC[i];
        a:=AI[j];
        phi := hom< F->AC[i] | AC[i].1, AC[i].2 >;
        M2 := GModule(Q,[phi(a[1]),phi(a[2])]);
        isit, iso := IsIsomorphic(C[i],M2);
        if not isit then error "Bug!"; end if;
        det := Determinant(iso);
        isit, v := IsPower(det,d);
        if isit then
           iso *:= ScalarMatrix(GF(q),d,v^-1);
        elif not general then continue;
        end if;
        //We will try to make the order of iso as small as possible.
        //if general is true, we will sacrifice determinant 1 if necessary
        po, x := ProjectiveOrder(iso);
        ox := Order(x);
        if ox gt 1 then
          f := Factorisation(ox);
          ff := [ox div x[1]^x[2]: x in f]; //e.g. ox=180, ff=[45, 20, 36].
          _, co := ExtendedGreatestCommonDivisor(ff);
          for i in [1..#f] do
            u := x^(co[i]*ff[i]); //factor of x with order f[i][1]^f[i][2]
            rts := AllRoots(u,po);
            if rts ne [] then
               got := false;
               for v in rts do
                 if Log(v) mod ((q-1) div GCD(q-1,d)) eq 0 then
                     //v * I_d has det 1
                   iso *:= ScalarMatrix(GF(q),d,v^-1);
                   got:=true; break;
                 end if;
               end for;
               if general and not got then
                 iso *:= ScalarMatrix(GF(q),d,rts[1]^-1);
               end if;
            end if;
          end for;
        end if;
        Append(~gens,iso);
      end for;
      //finally adjoin scalars
      if (not general and GCD(q-1,d) ne 1) or (general and q gt 2) then
        Append(~gens,ScalarMatrix(GF(q),d, ww ));
      end if;
      Append(~gps, sub<GL(d,q) | gens> );
    when "unitary" :
      form := forms`sesquilinearForm;
      f := Factorisation(q); rq := f[1][1]^(f[1][2] div 2);
      ww := normaliser select w
            else general select w^(rq-1)
            else w^((rq-1)*((rq+1) div GCD(rq+1,d)));
                                //power of w^(rq-1) s.t. ww I_d has det 1
      gens := [ GL(d,q) | AC[i].j : j in [1..Ngens(AC[i]) ]];
    //find generators of subgroup of automorphism group stabilizing this module
      sgens := [];
      for j in [1..na] do if i^perms[j] eq i then
        Append(~sgens,j);
      end if; end for;
      for j in sgens do
        //Attempt to append this automorphism to AC[i];
        a:=AI[j];
        phi := hom< F->AC[i] | AC[i].1, AC[i].2 >;
        M2 := GModule(Q,[phi(a[1]),phi(a[2])]);
        isit, iso := IsIsomorphic(C[i],M2);
        if not isit then error "Bug!"; end if;
        //adjust by scalar to make iso fix form.
        scal := (iso * form * ChangeMat(iso,"unitary",d,rq) * form^-1)[1][1];
        isit, v := IsPower(GF(q)!scal,rq+1);
        iso := iso * ScalarMatrix(d,v^-1);
        //try to make determinant 1
        det := Determinant(iso);
        rts := AllRoots(det,d);
        got := false;
        for v in rts do if Log(v) mod (rq-1) eq 0 then
            iso *:= ScalarMatrix(GF(q),d,v^-1);
            got := true; break;
        end if; end for;
        if not general and not got then continue; end if;
        //We will try to make the order of iso as small as possible.
        //if general is true, we will sacrifice determinant 1 if necessary
        //if normaliser is true, we will sacrifice fixing form if necessary
        po, x := ProjectiveOrder(iso);
        ox := Order(x);
        if ox gt 1 then
          f := Factorisation(ox);
          ff := [ox div x[1]^x[2]: x in f]; //e.g. ox=180, ff=[45, 20, 36].
          _, co := ExtendedGreatestCommonDivisor(ff);
          for i in [1..#f] do
            u := x^(co[i]*ff[i]); //factor of x with order f[i][1]^f[i][2]
            rts := AllRoots(u,po);
            got := false;
            if rts ne [] then
               got := false;
               for v in rts do
                 if Log(v) mod ((rq-1)*((rq+1) div GCD(rq+1,d))) eq 0 then
                     //v * I_d has det 1 and is in GU
                   iso *:= ScalarMatrix(GF(q),d,v^-1);
                   got:=true; break;
                 end if;
               end for;
               if general and not got then
                 for v in rts do
                   if Log(v) mod (rq-1) eq 0 then
                       //v * I_d fixes form
                     iso *:= ScalarMatrix(GF(q),d,v^-1);
                     got:=true; break;
                   end if;
                 end for;
                 if normaliser and not got then
                   iso *:= ScalarMatrix(GF(q),d,rts[1]^-1);
                 end if;
               end if;
            end if;
          end for;
        end if;
        Append(~gens,iso);
      end for;
      //finally adjoin scalars
      if  general or GCD(rq+1,d) ne 1 then
        Append(~gens,ScalarMatrix(GF(q),d, ww ));
      end if;
      g := TransformForm(form, forms`formType);
      Append(~gps, sub<GL(d,q) | gens>^g );
    else
      form := forms`bilinearForm;
      if IsEven(q) and forms`quadraticForm cmpne false then
        quad := true;
        form := forms`quadraticForm;
      else quad := false;
      end if;
      tmat := TransformForm(form, forms`formType);
      gens := [ GL(d,q) | (AC[i].j)^tmat : j in [1..Ngens(AC[i]) ]];
    //find generators of subgroup of automorphism group stabilizing this module
      sgens := [];
      for j in [1..na] do if i^perms[j] eq i then
        Append(~sgens,j);
      end if; end for;
      if forms`formType eq "orthogonalplus" then
        dsq := d mod 4 eq 0 or (d mod 4 eq 2 and q mod 4 eq 1);
        sgn := 1;
      elif forms`formType eq "orthogonalminus" then
        dsq := d mod 4 eq 2 and q mod 4 eq 3;
        sgn := -1;
      else dsq := false; sgn := 0;
      end if;
      for j in sgens do
        //Attempt to append this automorphism to AC[i];
        a:=AI[j];
        phi := hom< F->AC[i] | AC[i].1, AC[i].2 >;
        M2 := GModule(Q,[phi(a[1]),phi(a[2])]);
        isit, iso := IsIsomorphic(C[i],M2);
        if not isit then error "Bug!"; end if;
        //try to adjust by scalar to make iso fix form.
        if quad then
          got := false;
          mat := iso * form * Transpose(iso);
          for i in [2..d] do for j in [1..i-1] do
           mat[j][i] +:= mat[i][j];
           if mat[j][i] ne GF(q)!0 and not got then
             scal := mat[j][i] * form[j][i]^-1;
             got := true;
           end if;
           mat[i][j] := 0*mat[i][j];
          end for; end for;
        else
          scal := (iso * form * Transpose(iso) * form^-1)[1][1];
        end if;
        isit, v := IsPower(scal,2);
        if isit then
          iso := iso * ScalarMatrix(d,v^-1);
        elif not normaliser then continue;
        end if;
        det := Determinant(iso);
        if det eq GF(q)!(-1) and IsOdd(d) then
           iso *:= ScalarMatrix(GF(q),d,GF(q)!(-1));
        elif not general and det ne GF(q)!1 then continue;
        end if;
        iso := tmat^-1 * iso * tmat;
        if not special then
         if (forms`formType eq "orthogonalplus" and not InOmega(iso,d,q,1)) or
            (forms`formType eq "orthogonalminus" and not InOmega(iso,d,q,-1))
           then
           if IsOdd(q) and not dsq then
             iso := -iso;
           else continue;
           end if;
         end if;
         if forms`formType eq "orthogonalcircle" and not InOmega(iso,d,q,0)
           then continue;
         end if;
        end if;
        //We will try to make the order of iso as small as possible.
        //if normaliser is true, we will sacrifice fixing form if necessary
        po, x := ProjectiveOrder(iso);
        ox := Order(x);
        if special and ox gt 1 then
          f := Factorisation(ox);
          ff := [ox div x[1]^x[2]: x in f]; //e.g. ox=180, ff=[45, 20, 36].
          _, co := ExtendedGreatestCommonDivisor(ff);
          for i in [1..#f] do
            u := x^(co[i]*ff[i]); //factor of x with order f[i][1]^f[i][2]
            rts := AllRoots(u,po);
            if rts ne [] then
               got := false;
               for v in rts do
                 if v eq GF(q)!(-1) and IsEven(d) and IsOdd(q) then
                     //v * I_d has det 1
                   iso *:= ScalarMatrix(GF(q),d,v^-1);
                   got:=true; break;
                 end if;
               end for;
               if normaliser and not got then
                 iso *:= ScalarMatrix(GF(q),d,rts[1]^-1);
               end if;
            end if;
          end for;
        end if;
        Append(~gens,iso);
      end for;
      //finally adjoin scalars
      if normaliser and q gt 2 then
        Append(~gens,ScalarMatrix(GF(q),d, w));
      elif (general and IsOdd(q)) or 
           (special and IsEven(d) and IsOdd(q)) or
           (forms`formType eq "symplectic" or (IsEven(d) and dsq)) then
               Append(~gens,ScalarMatrix(GF(q),d, GF(q)!(-1)));
      end if;
      Append(~gps, sub<GL(d,q) | gens> );
    end case;
  end for;

  return gps;
end function;
