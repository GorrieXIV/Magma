freeze;

intrinsic RelationMatrix(G::GrpAb) -> Mtrx
  {The matrix defined by the relations in G}
  T := Relations(G);
  if #T eq 0 then
    return Matrix(Integers(), 0, Ngens(G), []);
  end if;
  R := [];
  for t in T do
    l := LHS(t);
    r := RHS(t);
    Append(~R, Eltseq(l-r));
  end for;
  return Matrix(R);
end intrinsic;

function TestOne(G, U, n)
  h := hom<G->G | [n*G.i : i in [1..Ngens(G)]]>;
  return h(U) eq U meet h(G);
end function;

// for free groups, neat = pure, a theorem, somewhere
// for arbitrary groups neat = pure iff torsion part is divisible or
// elementary(?):
// @article{0179.32601,
// author="Simauti, K.",
// title="{On Abelian groups in which every neat subgroup is a pure
// subgroup.}",
// language="English",
// journal="Comment. Math. Univ. St. Pauli ",
// volume="17",
// pages="105-110",
// year="1969",
// keywords="{group theory}",
// }
// example: G = C_8 x C_2, U = 2*G.1 + G.2
// is neat (2*G = C_4 = <2*G.1>, 2*U = <4*G.1>, U meet 2G = 4*G.1
// but not pure 4*G = <4*G.1>, 4*U = 0, U meet 4*G = 4*G.1
//
// purity and torsion implies direct summand. (Pruefer, Kulikoff)
// (book of Fuchs)
//
intrinsic IsPure(G::GrpAb, U::GrpAb) -> BoolElt
  {For an abelian group G with finite subgroup U, decide if U is pure in G.}
  // aka: isolated subgroups or serving subgroups
  require U subset G and IsFinite(U):
    "2nd argument must be a finite subgroup of the 1st";
  if not IsFinite(G) then
    return IsPure(TorsionSubgroup(G), U);
  end if;
  o := Exponent(G);
  d := &cat[ [p[1]^i : i in [1..p[2]]] : p in Factorisation(o)];
  return forall{n : n in d | TestOne(G, U, n)};
end intrinsic;

intrinsic IsNeat(G::GrpAb, U::GrpAb) -> BoolElt
  {For an abelian group G with finite subgroup U, decide if U is neat in G.}
  require U subset G:
    "2nd argument must be a subgroup of the 1st";
  if not IsFinite(G) then
    return IsNeat(TorsionSubgroup(G), U);
  end if;
  o := FactoredOrder(G);
  return forall{n : n in o | TestOne(G, U, n[1])};
end intrinsic;

intrinsic IsFree(G::GrpAb) -> BoolElt
  {Determine whether abelian group G is free abelian}
  return (not IsFinite(G) and #TorsionSubgroup(G) eq 1) or IsTrivial(G);
end intrinsic;

intrinsic IsInfinite(G::GrpAb) -> BoolElt
  {}
  return not IsFinite(G);
end intrinsic;

intrinsic IsMixed(G::GrpAb) -> BoolElt
  {}
  return not IsFinite(G) and not IsFree(G);
end intrinsic;

intrinsic IspGroup(G::GrpAb) -> BoolElt, RngIntElt
  {}
  if not IsFinite(G) or #G eq 1 then
    return false, _;
  end if;
  o := FactoredOrder(G);
  if #o eq 1 then
    return true, o[1][1];
  else
    return false, _;
  end if;
end intrinsic;

intrinsic '*'(k::RngIntElt, G::GrpAb) -> GrpAb, Map
  {}
  h := hom<G -> G | [k*G.i : i in [1..Ngens(G)]]>;
  return h(G), h;
end intrinsic;

intrinsic '+'(A::GrpAb, B::GrpAb) -> GrpAb
  {}
  C := CoveringStructure(A, B);
  return sub<C|A, B>;
end intrinsic;

// Old version of HasComplement was incorrect. Example:
// G:=AbelianGroup([2,2,4]);
// HasComplement(G,sub<G|G.1+G.3>);
// which crashed on a sanity check assertion.
//
// New code for HasComplement supplied by Derek Holt, 13 Dec 2012.
//
intrinsic HasComplement(G::GrpAb, U::GrpAb) -> BoolElt, GrpAb
{Computes, if possible, a complement to U in G, i.e. C, s.th. C meet U is
trivial and G = U+C}

    require IsFinite(G) : "Groups must be finite";
    require U subset G : "2nd group must be a subgroup of the 1st";

    if #U eq 1 then
	return true, G;
    end if;
    if #U eq #G then
	return true, sub<G|>;
    end if;
    if not IsPure(G, U) then
	return false, _;
    end if;

    Q, phi := quo< G | U >;

    compgens := [];
    Z := Integers();
    Qgens, ords := AbelianBasis(Q);
    U := sub<U|AbelianBasis(U)>;
    ngu := Ngens(U);
    ogu := [Order(U.i) : i in [1..ngu]];
    for j := 1 to #Qgens do
	Qgen := Qgens[j];
	ord := ords[j];
	iQgen := Qgen @@ phi;
	powgen := ord * iQgen;
	if powgen ne G.0 then
	    // need element u in U with ord * u eq powgen
	    powgen := U!powgen;
	    epg := Eltseq(powgen);
	    u := U![Z| epg[k] mod ogu[k] eq 0 select 0 else
		  (Zk!epg[k] div Zk!ord where Zk := Integers(ogu[k])) :
		    k in [1..ngu]];
	    assert ord * u eq powgen;
	    iQgen -:= u;
	end if; 
	Append(~compgens, iQgen);
    end for;

    V := sub< G | compgens >;
    assert sub<G|U, V> eq G;
    assert #(U meet V) eq 1;
    return true, V;
end intrinsic;

intrinsic Complement(G::GrpAb, U::GrpAb) -> GrpAb
  {Computes a complement for G in U}

  require IsFinite(G) : "Groups must be finite";
  require U subset G : "2nd group must be a subgroup of the 1st";
  require IsPure(G, U):
    "Second group has no complement in first";

  _, V := HasComplement(G, U);
  return V;
end intrinsic;

/*********************Chief series**************************************/
chief_series := function(G)
    assert ISA(Type(G), GrpAb);
    res := [G];
    curr := sub<G|[G.i:i in [1..Ngens(G)] | Order(G.i) gt 1]>;
    while #curr gt 1 do
        ord := Factorization(Order(curr.1));
        x := ord[1,1]*curr.1;
        if IsIdentity(x) then
            curr := sub<curr|[curr.i: i in [2..Ngens(curr)]]>;
        else
            curr := sub<curr|x, [curr.i: i in [2..Ngens(curr)]]>;
        end if;
        Append(~res, curr);
    end while;
    return res;
end function;

intrinsic ChiefSeries(G::GrpAb) -> SeqEnum
{A chief series for G}
    return chief_series(G);
end intrinsic;

intrinsic CompositionSeries(G::GrpAb) -> SeqEnum
{A composition series for G}
    return chief_series(G);
end intrinsic;
/*********************end Chief series**************************************/
              
