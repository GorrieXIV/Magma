freeze;

////////////////////////////////////////////////////////////////////// 
//  AutomorphismGroup for elliptic curves over general fields       //
//                                                                  //
//  Steve Donnelly, March 2009                                      //
//                                                                  //
//  (See Appendix A in Silverman's first book for the formulas)     //
////////////////////////////////////////////////////////////////////// 

// intrinsics 
// AutomorphismGroup(E) -> Grp, Map
// Automorphisms(E) -> SeqEnum[MapSch]

// This tries to be reasonably efficient, eg AutomorphismGroup 
// doesn't create MapSch's until the user asks for them.

// TO DO: create them as iso's, with inverse equations

debug := false;

function inverse_transformation(trans)
  u,s,t := Explode(trans);
  u2 := u^2;
  return [u2, u2*s, t + s^3]; 
end function;

// composition = trans1 then trans2

function compose2(trans1, trans2)
  if #trans1 eq 2 then
    // trans = [u,r] represents (x,y) :-> (u^2*x+r, u^3*y)
    u1,r1 := Explode(trans1);
    u2,r2 := Explode(trans2);
    return [u1*u2, u2^2*r1 + r2];
  else 
    // trans = [u,s,t] represents (x,y) :-> (u^2*x+s^2, y+u^2*s*x+t) 
    u1,s1,t1 := Explode(trans1);
    u2,s2,t2 := Explode(trans2);
    return [u1*u2, u2*s1 + s2, t1 + u2^2*s1^2*s2 + t2]; 
  end if;
end function;

function compose(seq) 
  assert #seq gt 0;
  ans := seq[1];
  for i := 2 to #seq do 
    ans := compose2(ans, seq[i]); 
  end for;
  return ans;
end function;

// work out the image of an element in a GrpPC, 
// given images of the generators and the identity

function trans(g, gens, id)
  seq := Eltseq(g); assert &and [e ge 0 : e in seq];
  word := &cat[ [gens[i] : j in [1..seq[i]]] : i in [1..#seq] ];
  if #word eq 0 then return id; end if;
  return compose(word);
end function;

intrinsic AutomorphismGroup(E::CrvEll) -> Grp, Map
{The group of automorphisms of the given elliptic curve E (automorphims of E 
 as a group variety, ie automorphisms of the projective curve that fix the 
 point at infinity).  Returned as an abstract group A, together with a map 
 sending elements of A to explicit automorphisms.}

  K := BaseRing(E);
  _<X,Y,Z> := PolynomialRing(K,3);
  a1,a2,a3,a4,a6 := Explode(Coefficients(E));
  j := jInvariant(E);

  if j ne 0 and j ne 1728 then 
    Aut := AbelianGroup([2]);
    Autmap := map< Aut -> PowerStructure(MapSch) |
                    a :-> (a eq Aut!0) select map< E->E | [E.1,E.2,E.3] : Check:=debug>
                                        else  map< E->E | [E.1, -E.2-a1*E.1-a3*E.3, E.3] : Check:=debug>
                  >;

  elif Characteristic(K) notin {2,3} then
    if j eq 1728 then
      bool, i := HasRoot(Polynomial([K| 1,0,1]));
      if bool then
        multipliers := [[1,1], [-1,i], [1,-1], [-1,-i]];
      end if;
    elif j eq 0 then
      bool, w := HasRoot(Polynomial([K| 1,1,1]));
      if bool then
        multipliers := [[1,1], [w,-1], [w^2,1], [1,-1], [w,1], [w^2,-1]];
      end if;
    end if;
    if not assigned multipliers then
      multipliers := [[1,1], [1,-1]];
    end if;

    // translate to simple Weierstrass form (phi : E -> EE, psi : EE -> E) 
    phi := [X + (a1^2/12 + a2/3)*Z, Y + a1/2*X + a3/2*Z, Z]; 
    psi := [X - (a1^2/12 + a2/3)*Z, Y - a1/2*X + (a1^3/24 + a1*a2/6 - a3/2)*Z, Z];
    if debug then assert Monomials(Evaluate(DefiningEquation(E),psi)) subset [Y^2*Z,X^3,X*Z^2,Z^3]; end if;
    phi := [Evaluate(f,[E.1,E.2,E.3]) : f in phi];

    Aut := AbelianGroup([#multipliers]);
    Autmap := map< Aut -> PowerStructure(MapSch) | 
                    a :-> map< E->E | [Evaluate(f, [m[1]*phi[1], m[2]*phi[2], phi[3]]) : f in psi] : Check:=debug>
                          where m is multipliers[idx] where idx is Eltseq(a)[1]+1 
                 >;

  elif Characteristic(K) eq 3 then  // j = 0
    // translate to simple Weierstrass form (phi : E -> EE, psi : EE -> E) 
    A4 := -a1*a3 + a4;
    A6 := a3^2 + a6;
    psi := [X, Y - a1/2*X - a3/2*Z, Z];
    phi := [E.1, E.2 + a1/2*E.1 + a3/2*E.3, E.3];
    if debug then assert Evaluate(DefiningEquation(E),psi) eq Y^2*Z - X^3 - A4*X*Z^2 - A6*Z^3; end if;

    // trans = [u,r] represents (x,y) :-> (u^2*x+r, u^3*y),
    // where u^4 = 1 and r^3 + A4*r + (1-u^2)*A6 = 0
    bool1, r1 := HasRoot(Polynomial([K| A4, 0, 1]));
    booli, i := HasRoot(Polynomial([K| 1, 0, 1]));
    if booli then
      booli, ri := HasRoot(Polynomial([K| -A6, A4, 0, 1]));
    end if;
    if bool1 and booli then 
      // full Aut group of order 12
      Aut :=  PolycyclicGroup< S,R,T | R^3, S^2 = T, T^2, R^S = R^2 >;
      S := Aut.1; R := Aut.2;
      gens := [ [i,ri], [1,r1], [-1,0] ]; id := [1,0];
      elt_list := [Aut| 1, R, R^2, S, R*S, R^2*S, S^2, R*S^2, R^2*S^2, S^3, R*S^3, R^2*S^3]; 
      trans_list := [trans(elt, gens, id) : elt in elt_list];
    elif bool1 then 
      Aut := AbelianGroup([6]);
      elt_list := [Aut| 0,1,2,3,4,5];
      trans_list := [[1,0], [-1,-r1], [1,r1], [-1,0], [1,-r1], [-1,r1]];
    elif booli then 
      Aut := AbelianGroup([4]);
      elt_list := [Aut| 0,1,2,3];
      trans_list := [[1,0], [i,ri], [-1,0], [-i,ri]];
    else 
      Aut := AbelianGroup([2]);
      elt_list := [Aut| 0,1];
      trans_list := [[1,0], [-1,0]];
    end if;
    Autmap := map< Aut -> PowerStructure(MapSch) | 
                    a :-> map< E->E | [Evaluate(f, subst) : f in psi] : Check:=debug> 
                          where subst is [t[1]^2*phi[1] + t[2]*phi[3], 
                                          t[1]^3*phi[2], 
                                          phi[3]]
                          where t is trans_list[idx] where idx is Index(elt_list,a)
                 >;
  elif Characteristic(K) eq 2 then  // j = 0
    // translate x :-> x + a2, to make a1 = a2 = 0 
    assert a1 eq 0;
    A3 := a3;
    A4 := a2^2 + a4;
    A6 := a2*a4 + a6;
    if debug then 
      assert Evaluate(DefiningEquation(E), [X+a2*Z,Y,Z]) eq
             Y^2*Z + A3*Y*Z^2 - X^3 - A4*X*Z^2 - A6*Z^3; 
    end if;

    // Transformation [u,s,t] denotes (x,y) :-> (u^2*x+s^2, u^3*y + u^2*s*x + t)
    // where u^3 = 1, s^4 + A3*s + (1-u)*A4 = 0, and t^2 + A3*t + s^6 + A4*s^2 = 0.
    // The full group of order 24 has the presentation below (isomorphic to SL(2,3)).
    // The centre has order 2, generated by [1,0,A3] = negation on E (note A3 is nonzero).
    // Subgroups that can arise are Z/2, Z/4, Q8 or Z/6.

    id := [1,0,0]; cc := [1,0,A3]; // trivial automorphisms +-1
    boolz3, z3 := HasRoot(Polynomial([K| 1,1,1]));
    if boolz3 then 
      // list all auts with u = z3 (if any)
      auts_z3 := [];
      for s in [tup[1] : tup in Roots(Polynomial([K| (1-z3)*A4, A3, 0, 0, 1]))] do 
        for t in [tup[1] : tup in Roots(Polynomial([K| s^6+A4*s^2, A3, 1]))] do
          Append(~auts_z3, [z3,s,t]); end for; end for;
      assert #auts_z3 in {0,2,8};
      if #auts_z3 eq 8 then  // full group of order 24
        Aut := PolycyclicGroup< d,a,b,c | d^3, a^2 = b^2 = c, c^2, b^a = b*c, a^d = b, b^d = a*b >;
        // take dd = element in auts_z3 of order 3 (note dd^2 = dd^-1 <==> t + s^3 = u^2*s^3)
        for ust in auts_z3 do 
          xx := t + z3*s^3 where _,s,t is Explode(ust); assert xx in {0,A3};
          if xx eq 0 then dd := ust; break; end if;
        end for;
        // take aa = any element of order 4 
        bool,s := HasRoot(Polynomial([K| A3,0,0,1])); assert bool;
        bool,t := HasRoot(Polynomial([K| A3^2+A4*s^2, A3, 1])); assert bool;
        aa := [1,s,t];
        ddi := inverse_transformation(dd);
        bb := compose([ddi,aa,dd]); // = aa^dd
        xx := compose([aa,ddi,bb,dd]); // = aa*bb^dd = bb or bb^-1
        assert xx[1] eq 1 and xx[2] eq bb[2] and (xx[3] eq bb[3] or xx[3] eq bb[3]+A3);
        if xx[3] eq bb[3] then 
          // replace a by a^-1 and b by b^-1 ==> the above relations hold
          aa[3] +:= A3; 
          bb[3] +:= A3; 
        end if;
        if debug then  // check the relations
          assert compose([cc,cc]) eq id;
          assert compose([aa,aa]) eq cc;
          assert compose([bb,bb]) eq cc;
          aabb := compose([aa,bb]);
          assert compose([aabb,aabb]) eq cc;
          assert compose([ddi,aa,dd]) eq bb;
          assert compose([ddi,bb,dd]) eq aabb;
        end if;
        gens := [dd, aa, bb, cc];
        elt_list := [x : x in Aut];
        trans_list := [trans(elt, gens, id) : elt in elt_list]; // TO DO: more efficiently?
      elif #auts_z3 eq 2 then  // Z/6
        Aut := AbelianGroup([6]);
        elt_list := [Aut| 0,1,2,3,4,5];
        // one of auts_z3 has order 6, the other has order 3
        g, g4 := Explode(auts_z3);
        g2 := compose([g,g]);
        if compose([g,g2]) eq id then 
          g4, g := Explode(auts_z3); // replace g by -g
        end if;
        g5 := g2; g5[3] +:= A3; // set g5 = -g2
        trans_list := [id, g, g2, cc, g4, g5];
      end if;
    end if;
    if not boolz3 or #auts_z3 eq 0 then  // all auts have u = 1
      // list all auts with u = 1, excluding the central elements +-1
      auts_1 := [];
      for s in [tup[1] : tup in Roots(Polynomial([K| A3, 0, 0, 1]))] do 
        for t in [tup[1] : tup in Roots(Polynomial([K| s^6+A4*s^2, A3, 1]))] do
          Append(~auts_1, [1,s,t]); end for; end for;
      assert #auts_1 in {0,2,6};
      if #auts_1 eq 6 then  // Q8 
        Aut := PolycyclicGroup< a,b,c | c^2, a^2=c, b^2=c, b^a = b*c >; 
        a := Aut.1; b := Aut.2; c := Aut.3;
        elt_list := [Aut| 1, a, b, a*b, c, a*c, b*c, a*b*c]; 
        // we can take any two non-inverse elements as a and b
        aa := auts_1[1]; 
        bb := auts_1[2];
        if aa[2] eq bb[2] then bb := auts_1[3]; end if;
        aabb := compose([aa,bb]);
        aacc := aa; aacc[3] +:= A3; // take inverses since a*c = a^-1 etc
        bbcc := bb; bbcc[3] +:= A3;
        aabbcc := aabb; aabbcc[3] +:= A3;
        trans_list := [id, aa, bb, aabb, cc, aacc, bbcc, aabbcc]; 
      elif #auts_1 eq 2 then  // Z/4
        Aut := AbelianGroup([4]);
        elt_list := [Aut| 0,1,2,3];
        trans_list := [id, auts_1[1], cc, auts_1[2]];
      else  // Z/2
        Aut := AbelianGroup([2]);
        elt_list := [Aut| 0,1];
        trans_list := [id, cc];
      end if;
    end if;
    Autmap := map< Aut -> PowerStructure(MapSch) | 
                    a :-> map< E->E | eqns : Check:=debug>
                          where eqns is [tr[1]^2*(E.1+a2*E.3) + tr[2]^2*E.3 + a2*E.3, 
                                         E.2 +tr[1]^2*tr[2]*(E.1+a2*E.3) + tr[3]*E.3, 
                                         E.3] 
                          // (composing on both sides by x :-> x+a2)
                          where tr is trans_list[idx] where idx is Index(elt_list,a)
                 >;
  end if; // Characteristic(K)

  if debug then 
    for g in Aut do _:= Autmap(g); end for;
  end if;

  return Aut, Autmap;
end intrinsic;

// The main reason for including Automorphisms is to override the one 
// for a general Crv (would be extra confusing to override inconsistently!)

intrinsic Automorphisms(E::CrvEll) -> SeqEnum
{A sequence containing the automorphisms of the given elliptic curve E
(automorphisms of E as a group variety, ie automorphisms of the projective
curve that fix the point at infinity)}
  Aut, Autmap := AutomorphismGroup(E);
  return [a @ Autmap : a in Aut];
end intrinsic;
