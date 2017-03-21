freeze;

intrinsic AutomorphismGroup(G :: GrpAb) -> GrpAuto
{The automorphism group of a finitely generated abelian group G}
  //generators of Aut(G) as in GAP function.
  local T, primes, primgens, tfgens, imgens, ep, lp, pg, epc, lpc, mpc,
        co, co1, co2, offs, max, A, ordag, genims, igenims;
  T := TorsionSubgroup(G);
  primes := [ f[1] : f in FactoredOrder(T) ];
  primgens := [];
  for p in primes do 
    Append( ~primgens, [ G | P.i : i in [1..Ngens(P)] ] where P := Sylow(G,p) );
  end for;
  tfgens := [ G.i : i in [1..Ngens(G)] | Order(G.i) eq 0 ];
  genims := [];
  igenims := []; //images under inverse automorphism
  ordag := 1;

  for pno in [1..#primes] do
    //append automorphisms of p-primary component
    p := primes[pno];
    ep := &cat[ primgens[i] : i in [1..pno-1] ];
    lp := &cat[ primgens[i] : i in [pno+1..#primes] ];
    pg := primgens[pno];
    //locate homogeneous components
    hcomp := [];
    for o in Sort(SetToSequence({ Order(g): g in pg })) do
      Append( ~hcomp, < Valuation(o,p), [ g : g in pg | Order(g) eq o ] > );
    end for;

    //automorphims moving just one component
    for cono in [1..#hcomp] do
      co := hcomp[cono];
      epc := &cat[ hcomp[i][2] : i in [1..cono-1] ];
      lpc := &cat[ hcomp[i][2] : i in [cono+1..#hcomp] ];
      if #co[2] gt 1 then
        Append(~genims, ep cat epc cat
                [ co[2][2], co[2][1] ] cat [ co[2][i] : i in [3..#co[2]] ] cat
                        lpc cat lp cat tfgens );
        Append(~igenims, ep cat epc cat
                [ co[2][2], co[2][1] ] cat [ co[2][i] : i in [3..#co[2]] ] cat
                        lpc cat lp cat tfgens );
        if #co[2] gt 2 then
          Append(~genims, ep cat epc cat
                    [ co[2][i] : i in [2..#co[2]] ] cat [co[2][1]]  cat
                        lpc cat lp cat tfgens);
          Append(~igenims, ep cat epc cat
                    [co[2][#co[2]]]  cat [ co[2][i] : i in [1..#co[2]-1] ] cat
                        lpc cat lp cat tfgens);
        end if;
        Append(~genims, ep cat epc cat
             [ co[2][1]+co[2][2] ] cat [co[2][i] : i in [2..#co[2]] ] cat
                        lpc cat lp cat tfgens );
        Append(~igenims, ep cat epc cat
             [ co[2][1]-co[2][2] ] cat [co[2][i] : i in [2..#co[2]] ] cat
                        lpc cat lp cat tfgens );
      end if;
      U,phi := UnitGroup( IntegerRing(p^co[1]) );
      for u in Generators(U) do
        Append(~genims, ep cat epc cat
       [ (Integers()!phi(u))*co[2][1] ] cat [co[2][i] : i in [2..#co[2]] ] cat
                        lpc cat lp cat tfgens );
        Append(~igenims, ep cat epc cat
       [ (Integers()!phi(-u))*co[2][1] ] cat [co[2][i] : i in [2..#co[2]] ] cat
                        lpc cat lp cat tfgens );
      end for;
      ordag *:= #GL(#co[2],p) * p^((co[1]-1) * #co[2]^2);
    end for;

    //automorphisms mixing two components
    for co1no in [1..#hcomp-1] do for co2no in [co1no+1..#hcomp] do
      co1 := hcomp[co1no]; co2 := hcomp[co2no];
      epc := &cat[ hcomp[i][2] : i in [1..co1no-1] ];
      mpc := &cat[ hcomp[i][2] : i in [co1no+1..co2no-1] ];
      lpc := &cat[ hcomp[i][2] : i in [co2no+1..#hcomp] ];
      //max := #co1[2] eq 1 and #co2[2] eq 1 select Min( co1[1], co2[1] ) - 1
       //                                    else 0;
      max := 0;
      offs := Max( 0, co2[1]-co1[1] );
      Append(~genims, ep cat epc cat
            [ co1[2][1] + p^offs * co2[2][1] ] cat
            [ co1[2][i] : i in [2..#co1[2]] ] cat
                    mpc cat hcomp[co2no][2] cat lpc cat lp cat tfgens );
      Append(~igenims, ep cat epc cat
            [ co1[2][1] - p^offs * co2[2][1] ] cat
            [ co1[2][i] : i in [2..#co1[2]] ] cat
                    mpc cat hcomp[co2no][2] cat lpc cat lp cat tfgens );
      offs := Max( 0, co1[1]-co2[1] );
      Append(~genims, ep cat epc cat hcomp[co1no][2] cat mpc cat
            [ co2[2][1] + p^offs * co1[2][1] ] cat
            [ co2[2][i] : i in [2..#co2[2]] ] cat lpc cat lp cat tfgens );
      Append(~igenims, ep cat epc cat hcomp[co1no][2] cat mpc cat
            [ co2[2][1] - p^offs * co1[2][1] ] cat
            [ co2[2][i] : i in [2..#co2[2]] ] cat lpc cat lp cat tfgens );
      ordag *:= p^( 2 * #co1[2] * #co2[2] * Min(co1[1],co2[1]) );
    end for; end for;
  end for;

  // fixing torsion generators
  if #tfgens gt 1 then
    Append(~genims, &cat primgens cat
        [ tfgens[2], tfgens[1] ] cat [ tfgens[i] : i in [3..#tfgens] ] );
    Append(~igenims, &cat primgens cat
        [ tfgens[2], tfgens[1] ] cat [ tfgens[i] : i in [3..#tfgens] ] );
    if #tfgens gt 2 then
      Append(~genims, &cat primgens cat
                [ tfgens[i] : i in [2..#tfgens] ] cat [tfgens[1]] );
      Append(~igenims, &cat primgens cat
                [tfgens[#tfgens]] cat [ tfgens[i] : i in [1..#tfgens-1] ] );
    end if;
    Append(~genims, &cat primgens cat
      [ tfgens[1]+tfgens[2] ] cat [tfgens[i] : i in [2..#tfgens] ] );
    Append(~igenims, &cat primgens cat
      [ tfgens[1]-tfgens[2] ] cat [tfgens[i] : i in [2..#tfgens] ] );
  end if;
  if #tfgens gt 0 then
    Append(~genims, &cat primgens cat
                [ -tfgens[1] ] cat [ tfgens[i] : i in [2..#tfgens] ] );
    Append(~igenims, &cat primgens cat
                [ -tfgens[1] ] cat [ tfgens[i] : i in [2..#tfgens] ] );
  end if;

  //mixing
  if #tfgens gt 0 then
    for pno in [1..#primes] do
      p := primes[pno];
      pg := primgens[pno];
      hcomp := [];
      for o in Sort(SetToSequence({ Order(g): g in pg })) do
        Append( ~hcomp, < Valuation(o,p), [ g : g in pg | Order(g) eq o ] > );
      end for;
      for co1no in [1..#hcomp] do
        co1 := hcomp[co1no];
        Append(~genims, &cat primgens cat
          [ tfgens[1] + co1[2][1] ] cat [ tfgens[i] : i in [2..#tfgens] ] );
        Append(~igenims, &cat primgens cat
          [ tfgens[1] - co1[2][1] ] cat [ tfgens[i] : i in [2..#tfgens] ] );
      end for;
    end for;
  end if;

  A := AutomorphismGroup( G, &cat primgens cat tfgens, genims, igenims );
  if #tfgens eq 0 then A`Order := ordag; end if;
  A`Group := G;
  A`InnerGenerators := [];

  return A;
end intrinsic;
