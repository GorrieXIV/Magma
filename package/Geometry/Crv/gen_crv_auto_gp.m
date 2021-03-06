freeze;

/**********************************************************************
 mch - 08/06 - Specialised edit of the GenericGroup code to generate
 automorphism groups of function fields as used for curve
 automorphism groups to generate the permutation group rep.
 The main speed up is in using
 indexed sets ("eltshash") of sequences of images of generators to
 represent the field morphisms. This hugely improves the speed of the
 look-up functions is_in_G and is_in_T over the GenericGroup version.
 At the end, the eltshash list is kept as a compact representation of
 the field morphisms and the actual list of all of the field morphisms
 in the group is discarded.

**********************************************************************/

autGrp := recformat<gen, Mult, elts, G, Gelts, eltshash, Id, seq>;

function gen_seq(F)
/* get sequence of field generators of F over the constant field */
    seq := [];
    F1 := F;
    while IsFinite(Degree(F1)) do
        seq cat:= [F!(F1.i) : i in [1..Ngens(F1)]];
	F1 := BaseField(F1);
    end while;
    Append(~seq,F!(F1.1));
    return seq;
end function;

is_in_G := function(a_gp, x)
    return [x(s): s in a_gp`seq] in a_gp`eltshash;
end function;

is_in_T := function(Th, x, seq)
  r := Index(Th,[x(s): s in seq]);
  if r eq 0 then
    return false,_;
  else
    return true, r;
  end if;  
end function;         


// AddGenerator together with GenericGroup acts as an interface to Dimino's
// algorithm.
function addGenerator(a_gp, gen)

  G := a_gp`G;

  if is_in_G(a_gp, gen) then
    return false, _;
  end if;   


  Append(~a_gp`gen, gen);
  if G cmpne 1 then 
    GG := AddGenerator(G);
    phi := hom<G -> GG | [GG.i : i in [1..#a_gp`gen-1]]>;
  else
    GG := FreeGroup(1);
    phi := map<Integers() -> GG | x:->GG.0>;
  end if;  
  GT := {@ phi(x) : x in a_gp`Gelts @};
  r := [ ];


  Cl :=  [ GG.0];
  cl := [a_gp`Id];
  seq := a_gp`seq;
  T := a_gp`elts;
  Th := a_gp`eltshash;
  if #T eq 0 then
    T := [a_gp`Id];
    Th := {@ [(T[1])(s) : s in seq] @};
  end if;  

  repeat
    t := cl[1]; 
    Remove(~cl, 1);
    tt := Cl[1]; 
    Remove(~Cl, 1);
    for si in [1..#a_gp`gen] do
      if tt*GG.si in GT then
        continue;
      end if;  
      s := a_gp`gen[si];
      p := a_gp`Mult(t, s);
      f, pos := is_in_T(Th, p, a_gp`seq);
      vprint GrpGen, 2: "(Dimino: using generator ", GG.si, ")";
      if not f then  
        vprint GrpGen, 3: "(Dimino: adding coset)";
        Append(~cl, p);
        Append(~Cl, tt*GG.si);
        for i in [1..#a_gp`elts] do
	  etmp := a_gp`Mult(a_gp`elts[i], p);
          Append(~T, etmp);
	  Include(~Th,[etmp(s): s in seq]);
          Include(~GT, phi(a_gp`Gelts[i])* tt*GG.si);
        end for;
      else
        Append(~r, GT[pos] = tt*GG.si);
      end if;
    end for;
  until #cl eq 0;
  
  a_gp`elts := T;
  a_gp`eltshash := Th;
  a_gp`G := quo<GG | r>;
  ChangeUniverse(~GT, a_gp`G);
  a_gp`Gelts := GT;

  return true, a_gp;
end function;

function find_inverses(Gelts)
// computes the sequence of indices of inverse elements of g as
// g runs through the indexed set Gelts of elements of G

    seq := [1..#Gelts];
    for i in [1..#Gelts] do
	if seq[i] eq i then //not inverse of earlier elt
	    j := Index(Gelts,Gelts[i]^-1);
	    if j ne i then
		seq[i] := j; seq[j] := i;
	    end if;
	end if;
    end for;
    return seq; 

end function;

// Computes the group generated by a set of automorphisms, gen, of
// function field F (over its constant field!). Returns this
// as a permutation group G along with AutCrvGroup data - the
// indexed sets Gelts, Aelts, invs, Fgens
//
// NB: This gives an isomorphism of the group of FUNCTION FIELD
// isomorphisms to G. As the corresponding CURVE ISOMORPHISMS
// have the composition structure of the FF iso group but with the
// order REVERSED, the isomorphism of the curve automorphism group
// to G works as long as we remember to swap each element of
// G and its inverse in Gelts. This is done after invs is computed.

intrinsic GenCrvGrpData(gen::SeqEnum, Id::Map : Mult := '*', bP1 := false) 
		-> GrpPerm, SetIndx, SetIndx, SeqEnum, SeqEnum
{Internal function}
  a_gp := rec<autGrp | Mult := Mult,  Id := Id>;

  F := Domain(gen[1]);
  Fseq := gen_seq(F);
  seq := (bP1 select [Fseq[2]] else Fseq);
  a_gp`seq := seq;

  // generate the first cyclic bit directly
  g := gen[1];
  hash := [g(s) : s in seq];
  while (#gen gt 1) and (hash eq seq) do
    Remove(~gen, 1);
    g := gen[1];
    hash := [g(s) : s in seq];
  end while;
  G := FreeGroup(1);
  gg := G.1;
  Gelts := [gg];
  elts := [g];
  eltsh := {@ hash @};
  while hash ne seq do
    gg := gg*G.1;
    g := Mult(g, gen[1]);
    hash := [g(s) : s in seq];
    Append(~Gelts, gg);
    Append(~elts, g);
    Include(~eltsh,hash);
  end while;
  go := Gelts[#Gelts];
  G := quo<G|go>;
  a_gp`G := G;
  a_gp`elts := elts;
  a_gp`eltshash := eltsh;
  a_gp`Gelts := {@ G| g : g in Gelts @};
  a_gp`gen := [gen[1]];
  Remove(~gen, 1);

  for i in gen do
    f, g := addGenerator(a_gp, i);
    if f then
      a_gp := g;
    end if;
  end for;

  // get nice permutation rep
  G := a_gp`G;
  ordG := #G;
  for i := NumberOfGenerators(G) to 1 by -1 do
    q,Gprm := CosetAction(G, sub<G|[G|G.j : j in [1..i-1]]>);
    if #Gprm eq ordG then break; end if;
  end for;

  // we can now just get rid of elts. Aelts <-> a_gp`eltshash
  delete a_gp`elts;
  Gelts := {@ q(g): g in a_gp`Gelts @};
  Aelts := a_gp`eltshash;
  G := Gprm;

  // compute invs and do g <-> g^-1 in Gelts
  invs := find_inverses(Gelts);
  Gelts := {@ Gelts[i] : i in invs @};

  return G,Gelts,Aelts,invs,Fseq;

end intrinsic;

