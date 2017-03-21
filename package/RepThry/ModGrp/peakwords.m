freeze;
      t := Cputime(0);

modrepRF := recformat<
             field:  FldFin,
            irreds:  SeqEnum,
          condrecs:  SeqEnum,
        condirreds:  SeqEnum,
           condsub:  Grp,
          condgens:  SetIndx,
         absirreds:  SeqEnum,
          abscomps:  SeqEnum,
            cartan:  AlgMatElt,
         abscartan:  AlgMatElt,
            decomp:  ModMatRngElt,
              cdim:  SeqEnum,
              pdim:  SeqEnum,
          condpdim:  SeqEnum,
           abspdim:  SeqEnum,
               pis:  SeqEnum,
           autacts:  SeqEnum,
           galacts:  SeqEnum,
              pres:  GrpFP >;

// Dimenson of Nullspace of X:
null_dim := func<X | Nrows(X) - Rank(X)>;

PeakWord := function(G, M : cycle:=5000, pcomps := 0, condensation := false)
  //Find peak words for irreducible GF(q)G-module M
  //give up and start again if no luck after cycle tries
  local K, cdim, flag, e, ng, done, mats, g1, g2, e1, e2, newgens, nm,
        entry, newint, ct, totct, tct, dns, nz, mat, fac, nmat;
  assert IsIrreducible(M);
  vprint KGModule, 1:
   "Computing a peak word for irreducible module of dimension",Dimension(M);
  //G := Group(M);
  K := BaseRing(M);
  entry := [ t : t in G`modrepinfo | assigned t`field and t`field cmpeq K ][1];
  I := condensation select entry`condirreds else entry`irreds;
  for i in [1..#I] do
    if IsIsomorphic(M, I[i]) then ind:=i; break; end if;
  end for;

// "PeakWord"; "M:", M; "I:", I; "ind:", ind; zeit := Cputime();

  cdim := [];
  for i in [1..#I] do
    flag, _, e := IsAbsolutelyIrreducible(I[i]);
    cdim[i] := flag select 1 else e;
  end for;
  ng := Nagens(M);
  if pcomps cmpeq 0 then pcomps := [ true : i in [1..#I] ]; end if;
  
  tct:=0;
  repeat
    //"cycling";
    done := true;
    mats := [* [ ActionGenerator(I[i], j) : j in [1..ng] ] : i in [1..#I] *];
    //prepare word generator
    nm := ng;
    g1 := Random([1..nm]);
    g2 := nm eq 1 select g1 else Random([1..g1-1] cat [g1+1..nm]);
    e1 := condensation select 1 else Random([-1,1]);
    e2 := condensation select 1 else Random([-1,1]);
    for i in [1..#I] do
      Append( ~mats[i], mats[i][g1]^e1 * mats[i][g2]^e2 );
    end for;
    newgens := [ [e1*g1, e2*g2] ];
    nm +:= 1;
    newint := 2; //we will append a new group generators every newint choices
    ct := 0; totct:=0;
    while true do
      //get random group algebra element and see if it a peakword
      coeffs := [ Random(K) : i in [1..nm] ];
      mat := [* &+[ coeffs[k] * mats[i][k] : k in [1..nm] ] : i in [1..#I] *]; 
      fac := Factorisation(CharacteristicPolynomial(mat[ind]));
      for f in [ f : f in fac | Degree(f[1]) eq cdim[ind] ] do
        tct+:=1;
if 1 eq 1 then
	nmat_ind := Evaluate(f[1], mat[ind]);
        if null_dim(nmat_ind) eq 0 or null_dim(nmat_ind^2) ne cdim[ind] then
	    continue;
	end if;
	good := true;
	for i := 1 to #mat do
	    if i ne ind and pcomps[i] and
		null_dim(Evaluate(f[1], mat[i])) ne 0 then
		good := false;
		break;
	    end if;
	end for;
        if good then
          vprint KGModule, 1: "got peakword for this module.",tct,"tries.";
// "TIME:", Cputime(zeit); "poly:", f[1];
          return newgens, coeffs, f[1];
        end if;
else
        nmat := [* Evaluate( f[1], m ) : m in mat *]; 
        dns := [ null_dim(m) : m in nmat ];
        nz := [ i : i in [1..#I] | dns[i] ne 0 and pcomps[i] ];
        if nz eq [ind] and null_dim(nmat[ind]^2) eq cdim[ind] then
          vprint KGModule, 1: "got peakword for this module.",tct,"tries.";
// "TIME:", Cputime(zeit);
          return newgens, coeffs, f[1];
        end if;
end if;
      end for;
  
      totct +:= 1;
      if totct eq cycle then
        done := false; break;
      end if;
      ct +:= 1;
      if ct eq newint then
         //adjoin new group element
        g1 := Random([1..nm]);
        g2 := Random([1..g1-1] cat [g1+1..nm]);
        e1 := condensation select 1 else Random([-1,1]);
        e2 := condensation select 1 else Random([-1,1]);
        for i in [1..#I] do
          Append( ~mats[i], mats[i][g1]^e1 * mats[i][g2]^e2 );
        end for;
        Append(~newgens, [e1*g1, e2*g2] );
        nm +:= 1;
        ct := 0;
        newint +:= 1;
      end if;
    end while;
  until done;
end function;

EvaluateWord := function(M, gens, coeffs)
//evaluate word returned by PeakWords in module M
  local mats, ng, nm, need, t;
  mats := [ ActionGenerator(M, i) : i in [1..Nagens(M)] ];
  //decide which of the later matrices we really need.
  ng := #gens;
  nm := #mats;
  need := [ true : i in [1..ng] ];
  for k in [ng .. 1 by -1] do if coeffs[nm+k] eq 0 then
    need[k] := false;
    for l in [k+1..ng] do
      if need[l] and
         ( Abs(gens[l][1]) eq nm+k or Abs(gens[l][2]) eq nm+k ) then
        need[k] := true;
        break;
      end if;
    end for;
  end if; end for;
  for k in [1..ng] do if need[k] then
    t := gens[k];
    mats[nm+k] := mats[Abs(t[1])]^Sign(t[1]) * mats[Abs(t[2])]^Sign(t[2]);
  end if; end for;
  if forall{c : c in coeffs | c eq 0} then
    return 0*mats[1];
  end if;
  return &+ [ coeffs[i] * mats[i] :
                     i in [ k : k in [1..#coeffs] | coeffs[k] ne 0] ];
end function;

CartanMat:= function(IA)
  //IA must be a complete set of absolutely irreducible modules for a group
  //G over a finite field.
  local G, bc, cl, ci;
  vprint KGModule, 1: "Computing Cartan Matrix";
  G := Group(IA[1]);
  bc := [* BrauerCharacter(i) : i in IA *];
  cl := [ c : c in Classes(G) ];
  ci := MatrixAlgebra(Rationals(),#IA)!0;
  for i in [1..#IA] do for j in [1..#IA] do
    ci[i][j] := InnerProduct(bc[i], bc[j]);
  end for; end for;

 return Matrix(Integers(), ci^-1);
end function;

ModToQ := function(M,e)
  // replace entries of action matrices of M by images under Frobenius
  // automorphism x - x^(p^e), where M is over field of characteristic p
    local G;
    G := Group(M);
    return GModule(G,
    [ FrobeniusImage(m,e): m in [ActionGenerator(M,i): i in [1..Ngens(G)]]]);
end function;

intrinsic PIMComputeInfo(G::Grp, K::FldFin)
{Compute information for PIMs of G over K}
/* Compute irreducibles over K, absolutely irreducibles, Cartan matrix,
 * dimensions of projective indecomposables
 * Probably only works over standard copy GF(q) of field
 */
  local p, q, qq, entry, cdim, flag, e, abscomps, comps, C, rs, row, cartan, t;
  q := #K;
  assert K cmpeq GF(q);
  if not assigned G`modrepinfo then G`modrepinfo := [* *]; end if;
  for entry in G`modrepinfo do
     if assigned entry`field and entry`field cmpeq K then
      //information has already been computed
      return;
    end if;
  end for;
  t := Cputime(0);
  entry := rec< modrepRF | field:=K >;
//we can now use new functionality of IrreducibleModules
  I, IA, abscomps := IrreducibleModules(G, K);
  vprint KGModule, 2 : "Got irreducibles";
  entry`irreds := I;
  cdim := [1 : i in [1..#I] ]; 
  for i in [1..#I] do
    flag,_,e := IsAbsolutelyIrreducible(I[i]);
    if not flag then cdim[i] := e; end if;
  end for;
  entry`cdim := cdim;
/* 
  if forall{x: x in cdim | x eq 1} then
    IA := I;
    abscomps := [ [i] : i in [1..#I] ];
  //compute absolutely irreducible components of irreducibles
  else
*/
  if not forall{x: x in cdim | x eq 1} then
    qq := q^LCM(cdim);
//we want modules over common overfield
    for i in [1..#IA] do
      if Field(IA[i]) ne GF(qq) then
        IA[i] := GModule( G,
   [ Matrix( GF(qq), ActionGenerator(IA[i],j) ) : j in [1..Nagens(IA[i])] ] );
      end if;
    end for;
/*
    IA := IrreducibleModules(G, GF(qq));
    vprint KGModule, 2 : "Got absolute irreducibles";
    abscomps := [];
    for i in [1..#I] do
      comps := [];
      ME := GModule( G,
      [ Matrix( GF(qq), ActionGenerator(I[i],j) ) : j in [1..Nagens(I[i])] ] );
      C := Constituents(ME);
      for j in [1..#IA] do
        for c in C do
          if IsIsomorphic(c,IA[j]) then Append(~comps, j); break; end if;
        end for;
      end for;
      Append(~abscomps, comps);
    end for;
*/
  end if;
  entry`absirreds := IA;
  entry`abscomps := abscomps;
  vprint KGModule, 1 : "Time for irreducibles", Cputime(t);
  t := Cputime(0);
  C := CartanMat(IA);
  entry`abscartan := C;
  //calculate the Cartan matrix over K
  cartan := [];
  for i in [1..#I] do
    rs := &+[ Vector(C[k]) : k in abscomps[i] ];
    row := [];
    for j in [1..#I] do
      row[j] := rs[ abscomps[j][1] ];
      assert forall{k: k in abscomps[j] | rs[k] eq row[j]};
    end for;
    Append(~cartan, row);
  end for;
  cartan := Matrix(cartan);
  entry`cartan := cartan;
  vprint KGModule, 1 : "Time for Cartan matrix", Cputime(t);
  t := Cputime(0);
  
  entry`abspdim := Eltseq( Vector([Dimension(i): i in IA])*C ); 
  entry`pdim := Eltseq( cartan * Matrix(#I, 1, [Dimension(i): i in I] ) );
  assert &+[ entry`pdim[i] * Dimension(I[i]) div cdim[i] : i in [1..#I] ] eq #G;
  entry`pis := [];

/* automorphism group calculation often seems to make things worse!
  vprint KGModule, 1 :
   "Calculating action of group automorphisms on irreducible modules";
  A := AutomorphismGroup(G);
//now work aut action of Aut(G) on irreducibles
  perms := [ Sym(#I) | ];
  for i in [1..Ngens(A)] do
    if IsInner(A.i) then
      Append( ~perms, Id(Sym(#I)) );
    else
      perm := [];
      for j in [1..#I] do
        //Define and identity I[j]^A.i
        r := Representation(I[j]);
        im := GModule(G, [ r( G.k @ (A.i^-1) ) : k in [1..Ngens(G)]] );
        for k in [1..#I] do if IsIsomorphic(I[k], im) then
          Append(~perm,k);
          break;
        end if; end for;
      end for;
      Append( ~perms, Sym(#I)!perm);
    end if;
  end for;
  P := sub< Sym(#I) | perms > ;
  O := Orbits(P);
  iwm := InverseWordMap(P);
  entry`autacts := [];
  for o in O do
    for k in [2..#o] do
      flag, g := IsConjugate(P,o[1],o[k]); assert flag;
      entry`autacts[o[k]] :=
                    < o[1], Evaluate( iwm(g), [A.i : i in [1..Ngens(A)]] ) >;
    end for;
  end for;
  vprint KGModule, 2 : "Done";
*/
  entry`autacts := [];

//do similar thing for action of Galois automorphisms of K
  p := Factorisation(q)[1][1];
  e := Factorisation(q)[1][2];
  entry`galacts := [];
  if e gt 1 then
    //group is cyclic so only one generator!
    vprint KGModule, 1 :
     "Calculating action of field automorphisms on irreducible modules";
    perm := [];
    for j in [1..#I] do
      //Define and identity I[j]^alpha
      im := ModToQ(I[j],1);
      for k in [1..#I] do if IsIsomorphic(I[k], im) then
         Append(~perm,k);
         break;
      end if; end for;
    end for;
    P := sub< Sym(#I) | perm > ;
    if #P gt 1 then
      O := Orbits(P);
      for o in O do
        for k in [2..#o] do
          flag, g := IsConjugate(P,o[1],o[k]); assert flag;
          entry`galacts[o[k]] :=
                   < o[1], [i : i in [0..Order(P.1)-1] | g eq (P.1)^i][1] >;
        end for;
      end for;
    end if;
    vprint KGModule, 2 : "Done";
  end if;
  vprint KGModule, 1 : "Time for action calculations", Cputime(t);

  Append(~G`modrepinfo, entry);
end intrinsic;

ComputeInfo := PIMComputeInfo;

DecompositionMat := function(G, K);
  ComputeInfo(G,K);
  entry := [ t : t in G`modrepinfo | assigned t`field and t`field cmpeq K ][1];
  if assigned entry`decomp then return entry`decomp; end if;
  IA := entry`absirreds;
  bc := [ BrauerCharacter(i): i in IA];
  C:=CharacterTable(G);
  cl := Classes(G);
  psing := [ i : i in [1..#cl] | cl[i][1] mod Characteristic(K) ne 0 ];
  RC := Matrix([ [c[i]  : i in psing] : c in C ]);

  rbc := Matrix([ [b[i] : i in psing] : b in bc] );
  sol := Matrix( [ Solution(rbc, RC[i]) : i in [1..#cl] ] );
  sol:=Matrix(Integers(),sol);
  assert Transpose(sol) * sol eq entry`abscartan;
  entry`decomp := sol;
  pos := [ i : i in [1..#G`modrepinfo] |
     assigned G`modrepinfo[i]`field and G`modrepinfo[i]`field cmpeq K ][1];
  G`modrepinfo[pos] := entry;
  return sol;
end function;

ProjectiveIndecomposableDims := function(G, K)
  local entry;
  ComputeInfo(G,K);
  entry := [ t : t in G`modrepinfo | assigned t`field and t`field cmpeq K ][1];
  return entry`pdim;
end function;

CondensedIrreducibles := function(G,K : SS:=0)
// find subgroup and generators for condensed modules of irreducibles
  local pos, entry, I, p, S, cdim, H, R, gens, found, CI;
  ComputeInfo(G,K);
  pos := [ i : i in [1..#G`modrepinfo] |
     assigned G`modrepinfo[i]`field and G`modrepinfo[i]`field cmpeq K ][1];
  entry := G`modrepinfo[pos];
  if assigned entry`condirreds then return entry`condirreds; end if;
  I := entry`irreds;
  p := Characteristic(K);
  if SS cmpeq 0 then
    S := Subgroups(G);
    vprint KGModule, 1: "Computed subgroups of group";
    Sort( ~S, func<x,y | y`order - x`order > );
    SS := [s : s in S | s`order mod p ne 0 ];
  end if;
  //look for subgroup with faithful condensation on all irreducibles
  for s in SS do
    if s`order eq 1 then return []; end if;
    H := s`subgroup;
    found := true;
    for i in I do
      R := InductionCondensation(G,i,H);
      if Nrows(R`Image(G.0)) eq 0 then
         found:=false; break;
      end if;
    end for;
    if found then
      R := [InductionCondensation(G,i,H): i in I];
      vprint KGModule, 1: "Using subgroup for condensation of order", s`order;
      break;
    end if;
  end for;
  //Now find generators for condensed modules - may need more than for G
  gens := {@ G.i : i in [1..Ngens(G)] @};
  cdim := entry`cdim;
  found := false;
  repeat
    found := true;
    //CI := [ RModule( [r`Image(g) * r`Image(G.0)^-1 : g in gens] ) : r in R ]; 
    CI := [ RModule( [r`Image(g) : g in gens] ) : r in R ]; 
    for k in [1..#CI] do
      if not IsIrreducible( CI[k] ) or
        Dimension(EndomorphismRing(CI[k])) ne cdim[k] or
        exists{ t : t in [1..k-1] | IsIsomorphic( CI[t], CI[k] ) } then
          found := false;
          //add new generator
          repeat g:=Random(G); until not g in gens;
          Include(~gens,g);   
          break;
      end if;
    end for;
  until found;
//add a couple more for luck
/*
  repeat g:=Random(G); until not g in gens; Include(~gens,g);   
  repeat g:=Random(G); until not g in gens; Include(~gens,g);   
  repeat g:=Random(G); until not g in gens; Include(~gens,g);   
  repeat g:=Random(G); until not g in gens; Include(~gens,g);   
  repeat g:=Random(G); until not g in gens; Include(~gens,g);   
  repeat g:=Random(G); until not g in gens; Include(~gens,g);   
  repeat g:=Random(G); until not g in gens; Include(~gens,g);   
  CI := [ RModule( [r`Image(g) : g in gens] ) : r in R ]; 
*/
  //CI := [ RModule( [r`Image(g) * r`Image(G.0)^-1 : g in gens] ) : r in R ]; 
  entry`condrecs := R;
  entry`condirreds := CI;
  entry`condsub := H;
  entry`condgens := gens;
  entry`condpdim :=
     Eltseq( entry`cartan * Matrix(#I, 1, [Dimension(i): i in CI] ) );
  G`modrepinfo[pos] := entry;
  return CI;
end function;

MoreCondGens := procedure(G, K, n)
  vprint KGModule, 1 : "ADJOINING", n, "MORE CONDENSED GENERATORS";
  pos := [ i : i in [1..#G`modrepinfo] |
     assigned G`modrepinfo[i]`field and G`modrepinfo[i]`field cmpeq K ][1];
  entry := G`modrepinfo[pos];
  for i in [1..n] do
    repeat g:=Random(G); until not g in entry`condgens;
    Include(~entry`condgens,g);   
  end for;
  entry`condirreds := [ RModule( [r`Image(g) : g in entry`condgens] ) :
                                                      r in entry`condrecs ]; 
  G`modrepinfo[pos] := entry;
end procedure;

Update := procedure(G, ~entry, ind)
//We have just defined entry`pis[ind]
//Try to calculate some other proj indecomposables from this.
  local I, aa, r, D, dind, new, q, p, e, nind;

//first try group automorphisms.
  new := [ind];
  I := entry`irreds;
  r := 0;
  if IsDefined(entry`autacts, ind) then
    aa := entry`autacts[ind];
    if not IsDefined(entry`pis, aa[1]) then
      r := Representation(entry`pis[ind]);
      entry`pis[ aa[1] ] := GModule(G, [r(G.i @ aa[2]) : i in [1..Ngens(G)]] );
      Append(~new, aa[1]);
      vprint KGModule, 1 : "Deduced projective indecomposable number", aa[1];
    end if;
    ind := aa[1];
  end if;
  //r := Representation(entry`pis[ind]);
  for i in [1..#I] do
    if not IsDefined( entry`pis, i) and IsDefined(entry`autacts, i) then
      aa := entry`autacts[i];
      if aa[1] eq ind then
        if r cmpeq 0 then r := Representation(entry`pis[ind]); end if;
        entry`pis[i] :=
                   GModule(G, [r( G.i @ (aa[2]^-1) ) : i in [1..Ngens(G)]] );
        Append(~new, i);
       vprint KGModule, 1 :
  "Used automorphism group of G to deduce projective indecomposable number", i;
      end if;
    end if;
  end for;

//try Galois conjugates on newly defined entries
  q := #BaseRing(entry`irreds[1]);
  p := Factorisation(q)[1][1];
  e := Factorisation(q)[1][2];
  if e gt 1 then for nind in new do
    if IsDefined(entry`galacts, nind) then
      aa := entry`galacts[nind];
      if not IsDefined(entry`pis, aa[1]) then
        entry`pis[ aa[1] ] := ModToQ( entry`pis[nind], e-aa[2] );
        vprint KGModule, 1 :
 "Used field automorphism to deduce projective indecomposable number", aa[1];
      end if;
      ind := aa[1];
    end if;
    for i in [1..#I] do
      if not IsDefined( entry`pis, i) and IsDefined(entry`galacts, i) then
        aa := entry`galacts[i];
        if aa[1] eq ind then
          entry`pis[i] := ModToQ( entry`pis[ind], aa[2] );
         vprint KGModule, 1 :
 "Used field automorphism to deduce projective indecomposable number", i;
        end if;
      end if;
    end for;
  end for; end if;

//now try dual
  D := Dual(I[ind]);
  for i in [1..#I] do if IsIsomorphic(D,I[i]) then
    dind := i;
    break;
  end if; end for;
  if not IsDefined( entry`pis, dind) then
    entry`pis[dind] := Dual( entry`pis[ind] );
    vprint KGModule, 1 :
  "Used duality to deduce dual projective indecomposable number", dind;
    $$(G, ~entry, dind);
  end if;
  return;
end procedure;

IsPSoluble := function(G, p)
  if IsSoluble(G) then return true; end if;
  if p eq 2 then return false; end if;
  if #SolubleRadical(G) gt 1 then return $$( RadicalQuotient(G), p ); end if;
  if #Socle(G) mod p eq 0 then return false; end if;
  return $$( SocleQuotient(G), p );
end function;

forward ProjectiveIndecomposableD;
ProjectiveIndecomposableB :=function(M :
    S := 0, limdim:=20000, condensation:=false, update:=true )
//another method
  local G, K, p, flag, e, GG, g, w, f, mat, N, PM, H, pc, bc, SM, mrino,
        entry, I, pow, ind, d, pcomps, SS, t, CI, rdim, PC, v;
  //see if we already have it
//"limdim=",limdim;
  G := Group(M);
  K := BaseRing(M);
  ComputeInfo(G,K);
  mrino := [ i : i in [1 .. #G`modrepinfo] | assigned G`modrepinfo[i]`field and
                                           G`modrepinfo[i]`field cmpeq K ][1];
  entry := G`modrepinfo[mrino];
  I := entry`irreds;
  //locate M in list
  for i in [1..#I] do if IsIsomorphic(I[i], M) then
    ind := i; break;
  end if; end for;
  if IsDefined(entry`pis, ind) then
     return entry`pis[ind];
  end if;
  if entry`pdim[ind] eq Dimension(M) then
    entry`pis[ind] := M;
    G`modrepinfo[mrino] := entry;
    return M;
  end if;
  vprint KGModule, 1:
 "\nComputing projective indecomposable for module of dimension",Dimension(M);
  t := Cputime(0);
  p := Characteristic(K);
  if S cmpeq 0 then
    S := Subgroups(G);
    vprint KGModule, 1: "Computed", #S, "subgroups of group";
  end if;
  if IsPSoluble(G, p) and limdim eq 10 then //can induce from p-complement
    vprint KGModule, 1 : "p-soluble group. Inducing from p-complement";
    SS := [ s : s in S |
             s`order eq &*[f[1]^f[2] : f in FactoredOrder(G) | f[1] ne p] ];
    return ProjectiveIndecomposableD(M : S:=SS, limdim:=limdim, update:=update);
  end if;
  flag, _, e := IsAbsolutelyIrreducible(M);
  cdim := flag select 1 else e;
  bc := BrauerCharacter(M);

  Sort( ~S, func<x,y | y`order - x`order > );
  SS := [s : s in S | s`order mod p ne 0 ];
  if condensation then
    CI := CondensedIrreducibles(G,K : SS:=SS );
    if CI eq [] then
      vprint KGModule, 1 : "No condensation possible.";
      condensation:=false;
    end if;
  end if;
  entry := G`modrepinfo[mrino];
  for s in SS do
    H := s`subgroup;
    if Index(G,H) gt limdim then //try different method
      return ProjectiveIndecomposableD(M :
         limdim:=limdim, S:=S, condensation:=condensation, update:=update );
    end if;
    pc := PermutationCharacter(G,H);
    if InnerProduct(pc, bc) gt 0 then
      vprint KGModule, 1:  "Using subgroup of order",#H,"index",Index(G,H);
      vprint KGModule, 1: "Time to locate subgroup", Cputime(t);
      break;
    end if;
  end for;
  if condensation then
    t := Cputime(0);
    PC := PermutationCondensation(G, CosetAction(G,H), entry`condsub, K);
    vprint KGModule, 1:
      "Time to compute condensed permutation module setup", Cputime(t);
    vprint KGModule, 1: "Condensed module:", PC;
    t := Cputime(0);
    //id :=  PC`Image(G.0)^-1;
    //PM := RModule( [ PC`Image(g) * id : g in entry`condgens ] );
    PM := RModule( [ PC`Image(g) : g in entry`condgens ] );
    vprint KGModule, 1:
     "Time to compute generators of condensed permutation module of dimension",
                                             Dimension(PM),":",Cputime(t);
  else PM := PermutationModule(G,H,K);
  end if;
  t := Cputime(0);
  pdim := entry`pdim;
  pow := [ entry`cartan[i][i] : i in [1..#I] ];
  //now we figure out which consitutents we need to avoid in the peak words
  pcomps := [ InnerProduct( BrauerCharacter(I[i]), pc ) gt 0  : i in [1..#I] ];
  //we have also to avoid anything in the same block as one of these
  extend := true;
  while extend do
    extend := false;
    for i in [1..#I] do if pcomps[i] then
      for j in [1..#I] do if not pcomps[j] and (entry`cartan)[i][j] ne 0 then
        pcomps[j] := true;
        extend := true;
        break;
      end if; end for;
    end if; end for;
  end while;
  vprint KGModule, 2 : "irreducible constituents of this perm module:", pcomps;
  t := Cputime(0);
  if condensation then
    g,w,f := PeakWord(G, CI[ind] : pcomps:=pcomps, condensation:=true );
  else
    g,w,f := PeakWord(G, M : pcomps:=pcomps, condensation:=false );
  end if;
  vprint KGModule, 1 : "Time to find peakword", Cputime(t);
  t := Cputime(0);

  mat := EvaluateWord(PM, g, w);
  mat := Evaluate(f, mat);
  mat := mat^pow[ind];
  vprint KGModule, 1 : "raised matrix to power",pow[ind];
  vprint KGModule, 1 : "Time to raise matrix to power", Cputime(t);
  t := Cputime(0);
  N := Nullspace(mat);
  vprint KGModule, 1 : "Nullspace of dimension", Dimension(N);
  vprint KGModule, 1 : "Time to compute nullspace", Cputime(t);
  t := Cputime(0);
  rdim := condensation select entry`condpdim[ind] else entry`pdim[ind];
  ct := 0;
  repeat
    ct +:= 1;
    v := Random(N);
    SM := sub< PM | v >;
    vprint KGModule, 2 : "spun dimension:",Dimension(SM);
    vprint KGModule, 1 : "Time to spin", Cputime(t);
    t := Cputime(0);
    if condensation and ct eq 10 then
      if #entry`condgens gt 20 then
         "Something wrong - giving up!";
        return 0;
      end if;
      //may not have enough generators of condensed algebra
      vprint KGModule, 1 : "not getting module - need new algebra generators";
      MoreCondGens(G,K,4);
      return $$(M : S:=S, limdim:=limdim, condensation:=true );
    end if;
  until Dimension(SM) eq rdim;
  if condensation then
/*
  //check we have the right module
    if not IsIsomorphic( CI[ind], quo< SM | JacobsonRadical(SM) > ) then
      vprint KGModule, 1 : "wrong module - need new algebra generators";
      MoreCondGens(G,K,2);
      return $$(M : S:=S, limdim:=limdim, condensation:=true );
    end if;
    vprint KGModule, 1 : "Time to check condensed module correct", Cputime(t);
*/
    t := Cputime(0);
    SM := PC`UncondenseSpin(PM, v);
    vprint KGModule, 1 : "Time for uncondensing spin", Cputime(t);
  end if;
  entry`pis[ind] := SM;
  t := Cputime(0);
  if update then
    Update(G, ~entry, ind);
    vprint KGModule, 1 : "Time to update", Cputime(t);
  end if;
  G`modrepinfo[mrino] := entry;
  return SM;
end function;

TrySubgroup := function(M, H)
//see if the subgroup H of G has a projective indecomposable whose induction
//to G contains projective indecomposable corresponding to M.
  local G, K, entry, I, ind, bc, entryH, IH, ibc, CH, works, pc, pdim;
  G := Group(M);
  K := BaseRing(M);
  ComputeInfo(G,K);
  entry := [ t : t in G`modrepinfo | assigned t`field and t`field cmpeq K ][1];
  I := entry`irreds;
  //locate M in list
  for i in [1..#I] do if IsIsomorphic(I[i], M) then
    ind := i; break;
  end if; end for;
  bc := BrauerCharacter(M);
  ComputeInfo(H,K);
  entryH := [ t : t in H`modrepinfo | assigned t`field and t`field cmpeq K ][1];
  IH := entryH`irreds;
  ibc := [ Induction( BrauerCharacter(i), G ) : i in IH ];
  CH := entryH`cartan;
  works := 0;
  pdim := 0;
  for i in [1..#IH] do
    pc := &+[ CH[i][j]*ibc[j] : j in [1..#IH] ];
    if InnerProduct(pc, bc) gt 0 then
      vprint KGModule, 2:
         "Induction of projective indecomposable number",i,"of dimension",
           entryH`pdim[i], "works";
      if works eq 0 or entryH`pdim[i] lt entryH`pdim[works] then
        works := i;
        pdim := entryH`pdim[i];
      end if;
    end if;
  end for;
  return works, pdim;
end function;

ProjectiveIndecomposableD :=
        function(M : S:=0, condensation:=false, limdim:=20000, update:=true )
//get projective indecomposable of G corresponding to M using induction of
//projective indecomposable proj of subgroup of G
  local G, K, p, GG, g, w, f, mat, N, PM, H, pc, bc, SM, CH, pno, hi,
        entry, I, pdim, pow, ind, d, pcomps, entryH, IH, ibc, SW,
        bestdim, subno, projno, mrino, t, CI, rdim, PC, v;
  //see if we already have it
  G := Group(M);
  K := BaseRing(M);
  ComputeInfo(G,K);
  mrino := [ i : i in [1 .. #G`modrepinfo] | assigned G`modrepinfo[i]`field and
                                           G`modrepinfo[i]`field cmpeq K ][1];
  entry := G`modrepinfo[mrino];
  I := entry`irreds;
  //locate M in list
  for i in [1..#I] do if IsIsomorphic(I[i], M) then
    ind := i; break;
  end if; end for;
  if IsDefined(entry`pis, ind) then
     return entry`pis[ind];
  end if;
  t := Cputime(0);
  vprint KGModule, 1: "Trying inducing from subgroups";
  if S cmpeq 0 then
    S := Subgroups(G);
    vprint KGModule, 1: "Computed", #S, "subgroups of group";
  end if;
  Sort( ~S, func<x,y | y`order - x`order > );
  if condensation then
    p := Characteristic(K);
    SS := [s : s in S | s`order mod p ne 0 ];
    CI := CondensedIrreducibles(G,K : SS:=SS );
    entry := G`modrepinfo[mrino];
  end if;
  t := Cputime(0);
  bestdim:=0; subno:=0; projno:=0;
  for i in [1..#S] do
    H := S[i]`subgroup;
    hi := Index(G, H);
    if hi le 10 then continue; end if;
    if bestdim gt 0 and Index(G, H) ge bestdim then break; end if;
    vkgm := GetVerbose("KGModule");
    SetVerbose("KGModule",0);
    pno, pdim := TrySubgroup(M, H);
    SetVerbose("KGModule",vkgm);
    if pno ne 0 then
      vprint KGModule, 1: "Subgp no", i, "index", hi,
                                     "induced dimension", pdim*hi;
      if bestdim eq 0 or pdim * hi le bestdim then
        bestdim := pdim * hi; 
        subno := i;
        projno := pno;
      end if;
      if bestdim lt entry`pdim[ind] then
         //probably Brauer character problem
        "something wrong - trying again!";
         return $$(M : S:=S, condensation:=condensation, update:=update );
      end if;
      if (i ge 200 and bestdim le 200000) or
         (i ge 50 and bestdim le limdim) or
         (i ge 50 and bestdim le 2 * entry`pdim[ind]) or
           bestdim eq entry`pdim[ind] then break;
      end if;
    end if;
  end for;
  if bestdim eq 0 then error "Sorry, I can't seem to compute this one!"; end if;
  vprint KGModule, 1:
     "Time to find subgroup to induce", Cputime(t);
  t := Cputime(0);

// "HERE bestdim:", bestdim; "HERE entry`pdim[ind]:", entry`pdim[ind];

  if bestdim eq entry`pdim[ind] and condensation then
    vprint KGModule, 1 :
      "Projective indecomposable is induced - turning off condensation";
    condensation:=false;
  end if;

  H := S[subno]`subgroup;
  vprint KGModule, 1 :
    "Using induction of dimension", bestdim,
    "of a projective indecomposable of a subgroup of index",Index(G,H);
  entryH := [ t : t in H`modrepinfo | assigned t`field and t`field cmpeq K ][1];
  IH := entryH`irreds;
  ibc := [ Induction( BrauerCharacter(i), G ) : i in IH ];
  CH := entryH`cartan;
  pc := &+[ CH[projno][j] * ibc[j] : j in [1..#IH] ];
  proj := ProjectiveIndecomposableB( IH[projno] : update:=false );
  vprint KGModule, 1:
     "Time to find projective indecomposable of subgroup", Cputime(t);
  t := Cputime(0);
  if condensation then
    t := Cputime(0);
    PC := InductionCondensation(G, proj, entry`condsub);
    vprint KGModule, 1:
     "Time to compute condensed induced module", Cputime(t);
    t := Cputime(0);
    //id :=  PC`Image(G.0)^-1;
    //PM := RModule( [ PC`Image(g) * id : g in entry`condgens ] );
    PM := RModule( [ PC`Image(g) : g in entry`condgens ] );
    vprint KGModule, 1:
     "Time to compute generators of condensed induced module of dimension",
                                             Dimension(PM),":",Cputime(t);
    t := Cputime(0);
  else
      PM := Induction(proj, G);
  end if;
  pdim := entry`pdim;

  /*
  AKS (7/1/16): added "not condensation and" since PM is condensed
  module and result may match proper component of this.
  Example problem: PIM #3 (dim 1536) for 6L34d2a in char 2.
  */

  if not condensation and Dimension(PM) eq pdim[ind] then
    SM := PM;
  else
    pow := [ entry`cartan[i][i] : i in [1..#I] ];
    //now we figure out which consitutents we need to avoid in the peak words
    pcomps:= [ InnerProduct( BrauerCharacter(I[i]), pc ) gt 0  : i in [1..#I] ];
    //we have also to avoid anything in the same block as one of these
    extend := true;
    while extend do
      extend := false;
      for i in [1..#I] do if pcomps[i] then
        for j in [1..#I] do if not pcomps[j] and (entry`cartan)[i][j] ne 0 then
          pcomps[j] := true;
          extend := true;
          break;
        end if; end for;
      end if; end for;
    end while;
    vprint KGModule, 2 : "irreducible contituents of this module:", pcomps;
    if condensation then
      g,w,f := PeakWord(G, CI[ind] : pcomps:=pcomps, condensation:=true );
    else
      g,w,f := PeakWord(G, M : pcomps:=pcomps, condensation:=false );
    end if;
    vprint KGModule, 1: "Time to find peakword", Cputime(t);
    t := Cputime(0);
  
    mat := EvaluateWord(PM, g, w);
    mat := Evaluate(f, mat);
    mat := mat^pow[ind];

    vprint KGModule, 1 : "raised matrix to power",pow[ind];
    vprint KGModule, 1 : "Time to raise matrix to power", Cputime(t);
    t := Cputime(0);
    N := Nullspace(mat);
    vprint KGModule, 1 : "Time to compute nullspace", Cputime(t);
    vprint KGModule, 1 : "Nullspace of dimension", Dimension(N);
    rdim := condensation select entry`condpdim[ind] else entry`pdim[ind];
    ct := 0;
    repeat
      ct +:= 1;
      v := Random(N);
      SM := sub< PM | v >;
      vprint KGModule, 2 : "spun dimension:",Dimension(SM);
      vprint KGModule, 1 : "Time to spin", Cputime(t);
      t := Cputime(0);
      if ct eq 10 then
        if condensation then
          //may not have enough generators of condensed algebra
          vprint KGModule, 1:"not getting module - need new algebra generators";
          MoreCondGens(G,K,2);
          return $$(M : S:=S, condensation:=true, update:=update );
        end if;
        //probably a Brauer character error!
        vprint KGModule, 1:"not getting module - trying again";
        return 0;
      end if;
    until Dimension(SM) eq rdim;
    //check we have the right module
    if condensation then
/*
      if not IsIsomorphic( CI[ind], quo< SM | JacobsonRadical(SM) > ) then
        vprint KGModule, 1 : "wrong module - need new algebra generators";
        MoreCondGens(G,K,2);
        return $$(M : S:=S, condensation:=true );
      end if;
      vprint KGModule, 1 : "Time to check condensed module correct", Cputime(t);
*/
      t := Cputime(0);
ROUND_RAT := 4;
      //SM := PC`UncondenseSpin(PM, v: RankEstimate := Round(bestdim/ROUND_RAT));
      SM := PC`UncondenseSpin(PM, v);
      vprint KGModule, 1 : "Time for uncondensing spin", Cputime(t);
    end if;
  end if;
  entry`pis[ind] := SM;
  t := Cputime(0);
  if update then
    Update(G, ~entry, ind);
    vprint KGModule, 1 : "Time to update", Cputime(t);
  end if;
  G`modrepinfo[mrino] := entry;
  return SM;
end function;

ProjectiveIndecomposablesB := function(G, K: limdim:=20000,
                                                 condensation:=condensation)
//Get all projective indecomposable GF(p)G-modules
  local I, lg, lw, f, proj;
  ComputeInfo(G,K);
  entry := [ t : t in G`modrepinfo | assigned t`field and t`field cmpeq K ][1];
  I := entry`irreds;
  vprint KGModule, 1: "Dimensions of irreducible modules:",
         [Dimension(i):i in I];
  vprint KGModule, 1:
       "Dimensions of corresponding projective indecomposables:", entry`pdim;
  if forall{i : i in [1..#I] | Dimension(I[i]) eq entry`pdim[i]}
     then return I;
  end if;
  S := Subgroups(G);
  vprint KGModule, 1: "Computed subgroups of group";
  proj := [ ProjectiveIndecomposableB( I[i] : S:=S, limdim:=limdim,
                             condensation:=condensation ) : i in [1..#I] ];
  return proj;
end function;

PeakWordStat := function(M : cycle:=5000)
  //Find peak word for irreducible GF(q)G-module M
  //give up and stgart again if no luck after cycle tries
  local G, K, cdim, flag, e, ng, done, mats, g1, g2, e1, e2, newgens, nm,
        newint, ct, totct, dns, nz, mat, fac, nmat;
  assert IsIrreducible(M);
  G := Group(M);
  K := BaseRing(M);
  I := IrreducibleModules(G, K);
  for i in [1..#I] do
    if IsIsomorphic(M, I[i]) then ind:=i; break; end if;
  end for;

  cdim := [];
  for i in [1..#I] do
    flag, _, e := IsAbsolutelyIrreducible(I[i]);
    cdim[i] := flag select 1 else e;
  end for;
  ng := Ngens(G);
  
  ctt1:=0; ctt2:=0; ct1:=0; ct2:=0; cta:=0;

  repeat
    //"cycling";
    done := true;
    mats := [* [ ActionGenerator(I[i], j) : j in [1..ng] ] : i in [1..#I] *];
    //prepare word generator
    nm := ng;
    g1 := Random([1..nm]);
    g2 := Random([1..g1-1] cat [g1+1..nm]);
    e1 := Random([-1,1]);
    e2 := Random([-1,1]);
    for i in [1..#I] do
      Append( ~mats[i], mats[i][g1]^e1 * mats[i][g2]^e2 );
    end for;
    newgens := [ [e1*g1, e2*g2] ];
    nm +:= 1;
    newint := 3; //we will append a new group generators every newint choices
    ct := 0; totct:=0;
    while true do
      //get random group algebra element and see if it a peakword
      coeffs := [ Random(K) : i in [1..nm] ];
      mat := [* &+[ coeffs[k] * mats[i][k] : k in [1..nm] ] : i in [1..#I] *]; 
      fac := Factorisation(CharacteristicPolynomial(mat[ind]));
      ctt1 +:= 1;
      for f in [ f : f in fac | Degree(f[1]) eq cdim[ind] ] do
        ctt2 +:= 1;
        nmat := [* Evaluate( f[1], m ) : m in mat *]; 
        dns := [ null_dim(m) : m in nmat ];
        nz := [ i : i in [1..#I] | dns[i] ne 0 ];
        if ind in nz then
           ct1+:=1;
           if null_dim(nmat[ind]^2) eq cdim[ind] then
              ct2+:=1;
              if #nz eq 1 then cta+:=1; end if;
           end if;
        end if;
      end for;
      if ctt1 eq 100000 then return ctt1, ctt2, ct1, ct2, cta; end if;
  
      totct +:= 1;
      if totct eq cycle then
        done := false; break;
      end if;
      ct +:= 1;
      if ct eq newint then
         //adjoin new group element
        g1 := Random([1..nm]);
        g2 := Random([1..g1-1] cat [g1+1..nm]);
        e1 := Random([-1,1]);
        e2 := Random([-1,1]);
        for i in [1..#I] do
          Append( ~mats[i], mats[i][g1]^e1 * mats[i][g2]^e2 );
        end for;
        Append(~newgens, [e1*g1, e2*g2] );
        nm +:= 1;
        ct := 0;
        newint *:= 3;
      end if;
    end while;
  until done;
end function;

ProjCover := function(M)
//return projective cover P of M and map phi:P->M
  local G, K, J, entry, RQ, rho, IS, I, sno, pi, homs, pc, proj, B, N, h, JN;
  vprint KGModule, 1:
   "Computing projective cover of module of dimension", Dimension(M);
  G := Group(M);
  K := BaseRing(M);
  ComputeInfo(G,K);
  entry := [ t : t in G`modrepinfo | assigned t`field and t`field cmpeq K ][1];
  J := JacobsonRadical(M);
  RQ, rho := quo< M | J >;
  IS := IndecomposableSummands(RQ);
  //identify them
  I := entry`irreds;
  sno := [];
  for i in [1..#IS] do
    for j in [1..#I] do
      if IsIsomorphic(IS[i], I[j]) then
         sno[i] := j;
         break;
      end if;
    end for;
  end for;
  //compute required projective indecomposables and maps onto components
  pi := [];
  for i in [1..#I] do
    if Position(sno,i) ne 0 then
      vprint KGModule,2:  "computing projective indecomposable",i;
      pi[i] := ProjectiveIndecomposableB(I[i]);
    end if;
  end for;
  homs := [**];
  vprint KGModule,2: "getting projective homomorphisms";
  for i in [1..#IS] do
    N := sub< M | IS[i].1 @ Morphism(IS[i], RQ) @@ rho >;
    JN := N meet J;
    //is there a better way than this?
//printf "AHom: %o, %o\n", pi[sno[i]], N; time
    h := AHom( pi[ sno[i] ], N );
//h;
    repeat
      homs[i] := Random(h);
    until sub< N | Image(homs[i]), JN > eq N;
  end for;

  pc, _, proj := DirectSum( [ pi[sno[i]] : i in [1..#IS] ]);
  vprint KGModule,1: "projective cover has dimension",Dimension(pc);
  //work out images of basis elements under projection
  B := Basis(pc);
  ims := [];
  for b in B do
    Append(~ims, &+[ b @ proj[i] @ homs[i] : i in [1..#IS]] );
  end for;
  return pc, AHom(pc, M)!ims;
end function;

CohDim := function(M,k : sglimit:=100000)
  local G, gotpres, F, MF, P, phi;
  G := Group(M);
  if #G eq 1 then return 0; end if;
  K := BaseRing(M);
  ComputeInfo(G,K);
  gotpres := false;
  for t in G`modrepinfo do if assigned t`pres then
      F := t`pres; gotpres:=true; break;
  end if; end for;
  if not gotpres then
    F := FPGroup(G);
    Append( ~G`modrepinfo, rec< modrepRF | pres:=F > );
  end if;
  MF := GModule(F, [ActionGenerator(M,i) : i in [1..Nagens(M)] ] );
  if k le 1 then
    return CohomologicalDimension( CohomologyModule(F, MF), k );
  end if;
  P, phi := ProjCover( Dual(M) );
  if Dimension(Kernel(phi)) eq 0 then
    return 0;
  end if;
  return $$( Dual( Kernel(phi) ), k-1);
end function;

CohDims := function(M,k : sglimit:=100000)
  //list of cohomological dimensions from 1 to k
  local G, gotpres, F, MF, P, phi;
  G := Group(M);
  if #G eq 1 then return [0 : i in [1..k] ]; end if;
  K := BaseRing(M);
  ComputeInfo(G,K);
  gotpres := false;
  for t in G`modrepinfo do if assigned t`pres then
      F := t`pres; gotpres:=true; break;
  end if; end for;
  if not gotpres then
    F := FPGroup(G);
    Append( ~G`modrepinfo, rec< modrepRF | pres:=F > );
  end if;
  MF := GModule(F, [ActionGenerator(M,i) : i in [1..Nagens(M)] ] );
  cd := CohomologicalDimension( CohomologyModule(F, MF), 1 );
  vprint KGModule, 1 : "Dimension of H^1(G,M) is", cd;
  ans := [ cd ];
  if k eq 1 then
    return ans;
  end if;
  M := Dual(M);
  for n in [2..k] do
    P, phi := ProjCover(M);
    M := Kernel(phi);
    if Dimension(M) eq 0 then
      ans cat:= [ 0 : i in [n..k] ];
      return ans;
    end if;
    MF := GModule(F, [ActionGenerator(M,i) : i in [1..Nagens(M)] ] );
    vprint KGModule, 1 :
       "Calculating first cohomology of module of dimension", Dimension(M);
    cd := CohomologicalDimension( CohomologyModule(F, Dual(MF) ), 1 );
    Append(~ans, cd );
    vprint KGModule, 1 : "Dimension of H^",n,"(G,M) is", cd;
  end for;
  return ans;
end function;
