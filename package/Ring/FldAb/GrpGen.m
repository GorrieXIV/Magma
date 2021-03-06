freeze;

genGrp := recformat<gen, Mult, Eq, elts, G, Gelts, Id, q>;

is_in_G := function(genGrp, x)
  return exists{ y: y in genGrp`gen | genGrp`Eq(y, x)} or
         exists{ y: y in genGrp`elts | genGrp`Eq(y, x)};
end function;         

is_in_T := function(genGrp, T, x)
  r := exists(pos){ y: y in [1..#T] | genGrp`Eq(T[y], x)};
  if r then
    return r, pos;
  else
    return r, _;
  end if;  
end function;         

declare attributes GrpFP: GenericGroup;
declare verbose GrpGen , 3;

intrinsic FindGenerators(G::GrpFP) -> [ ]
{Finds a small number of generators in G}

  require assigned G`GenericGroup : "G must be a \"generic\" group";

  mp := G`GenericGroup`q;
  p := Codomain(mp);

  g := [ ];
  repeat
    m1, g1 := CosetAction(p, sub<p|g>);
    e := [ x: x in g1];
    _, pos := Maximum([Order(x) :x in e]);
    Append(~g, e[pos] @@ m1);
  until p eq sub<p|g>; 
  n := [ mp(x) : x in G`GenericGroup`Gelts];
  g := [G`GenericGroup`elts[Position(n, x)] : x in g];
  return g;
end intrinsic;

// AddGenerator together with GenericGroup acts as an interface to Dimino's
// algorithm.
intrinsic AddGenerator(G::GrpFP, gen:: .) -> BoolElt, GrpFP, Map
{Adds a new generator to a generic group}

  require assigned G`GenericGroup : "G must be a \"generic\" group";

  genGrp := G`GenericGroup;
  if is_in_G(genGrp, gen) then
    return false, _, _;
  end if;   

  vprint GrpGen, 1: "Adding generator ", 
                     #genGrp`gen +1, " to group of size ", #genGrp`Gelts; 

  Append(~genGrp`gen, gen);
  if genGrp`G cmpne 1 then 
    GG := AddGenerator(genGrp`G);
    phi := hom<genGrp`G -> GG | [GG.i : i in [1..#genGrp`gen-1]]>;
  else
    GG := FreeGroup(1);
    phi := map<Integers() -> GG | x:->GG.0>;
  end if;  
  r := [ ];

  Cl := [GG.0];
  cl := [genGrp`Id];
  T := genGrp`elts;
  if #T eq 0 then
    T := [ genGrp`Id ];
    genGrp`elts := T;
  end if;  
  GT := [phi(x) : x in genGrp`Gelts];

  repeat
    assert #cl eq #Cl;
    assert #T eq #GT;
    vprint GrpGen, 2: "(Dimino: classes to consider ", Cl, ")";
    t := cl[1]; 
    Remove(~cl, 1);
    tt := Cl[1]; 
    Remove(~Cl, 1);
    for si in [1..#genGrp`gen] do
      vprint GrpGen, 2: "(Dimino: using generator ", GG.si, ")";
      if tt*GG.si in GT then
        vprint GrpGen, 3: "Skipping due to trivial exclusion";
        continue;
      end if;  
      s := genGrp`gen[si];
      p := genGrp`Mult(t, s);
      f, pos := is_in_T(genGrp, T, p);
      if not f then  
        vprint GrpGen, 3: "(Dimino: adding coset)";
        Append(~cl, p);
        Append(~Cl, tt*GG.si);
        for i in [1..#genGrp`elts] do
          Append(~T, genGrp`Mult(genGrp`elts[i], p));
          Append(~GT, phi(genGrp`Gelts[i])* tt*GG.si);
        end for;
      else
        vprint GrpGen, 3: "(Dimino: adding relation ", GT[pos] = tt*GG.si, ")";
        Append(~r, GT[pos] = tt*GG.si);
      end if;
    end for;
    vprint GrpGen, 2: "(Dimino: group size is now ", #GT, ")";
  until #cl eq 0;
  
  vprint GrpGen, 1: ".. done, group size is now ", #GT;
  genGrp`elts := T;
  genGrp`G := quo<GG | r>;
  ChangeUniverse(~GT, genGrp`G);
  genGrp`Gelts := GT;
  genGrp`q := CosetAction(genGrp`G, sub<genGrp`G|>);

//GG`GenericGroup := genGrp;
  delete G`GenericGroup;
  genGrp`G`GenericGroup := genGrp; 

  mp := map<genGrp`G -> genGrp`elts |
         x :-> genGrp`elts[Position([genGrp`q(x*z^-1) 
                                : z in genGrp`Gelts], Codomain(genGrp`q).0)],
         y :-> genGrp`Gelts[Position([genGrp`Eq(y, z)
                                : z in genGrp`elts], true)]>;

assert #Domain(mp) eq #Codomain(mp);  
  return true, genGrp`G, mp;
end intrinsic;  

 
intrinsic GenericGroup(gen::[ ]:Mult := '*', Eq := 'eq', Id,
					Reduce := false) -> GrpFP, Map
{The generic group generated by gen and the given operations}
  r := rec<genGrp | Mult := Mult, Eq := Eq, gen := [ ], elts := [  ],
                   G := 1, Gelts := [ 1 ]>;

  if Id cmpeq true then
    vprint GrpGen, 1 : "Finding identity...";
    l := [gen[1]];
    g := gen[1];
    G := FreeGroup(1);
    Gelts := [ ];
    elts := [ ];
    gg := G.1;
    repeat
      go := g;
      Append(~Gelts, gg);
      Append(~elts, g);

      gg := gg*G.1;
      g := Mult(g, gen[1]);
    until Eq(g, gen[1]);
    vprint GrpGen, 1: "... done, group size is now ", #elts;
    Id := go;
    go := Gelts[#Gelts];
    G := quo<G|go>;
    r`G := G;
    r`elts := elts;
    r`Gelts := Gelts;
    r`gen := [gen[1]];
    Remove(~gen, 1);
    G := r`G;
  else
    require Eq(Mult(Id,Id),Id): "Id is not the identity"; // MW Aug 2015
    G := FreeGroup(1);
  end if;  

  r`Id := Id;

  // probably a memory-problem here....
  G`GenericGroup := r;

  for i in gen do
    f, g, m := AddGenerator(G, i);
    if f then
      G := g;
      M := m;
assert #G eq #Codomain(M);
    end if;  
  end for;

  if not assigned M then
    genG:= G`GenericGroup;
    genG`q := CosetAction(genG`G, sub<genG`G|>);

    G`GenericGroup := genG;
    delete G`GenericGroup;
    G`GenericGroup := genG; 

    M := map<genG`G -> genG`elts |
           x :-> genG`elts[Position([genG`q(x*(genG`G)!z^-1) 
                                  : z in genG`Gelts], Codomain(genG`q).0)],
           y :-> genG`Gelts[Position([genG`Eq(y, z)
                                  : z in genG`elts], true)]>;
   
  end if;

  if Reduce then        // get minimal presentation for G and rebuild genG
    genG := G`GenericGroup;
    gp,IM := Simplify(G);
    genG`gen := [M(Inverse(IM)(gp.i)): i in [1..NumberOfGenerators(gp)]];
    genG`Gelts := [IM(g) : g in genG`Gelts];
    genG`q := hom<gp->Codomain(genG`q) | [(genG`q)(Inverse(IM)(gp.i)) :
		i in [1..NumberOfGenerators(gp)]]>;
    genG`G := gp; 
    gp`GenericGroup := genG;
    G := gp;

    M := map<genG`G -> genG`elts |
           x :-> genG`elts[Position([genG`q(x*z^-1) 
                                  : z in genG`Gelts], Codomain(genG`q).0)],
           y :-> genG`Gelts[Position([genG`Eq(y, z)
                                  : z in genG`elts], true)]>;
   
  end if;

  return G, M;
end intrinsic;

