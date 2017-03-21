freeze;

/* 
Don Taylor
2 August 2012

  $Id: plesken.m 52911 2016-05-31 01:44:13Z allan $

(Installed and hacked by AKS somewhat.)
  
Given a finite group G and a field F, the linear span of the
elements g - g^-1 in the group algebra FG is closed under the
Lie bracket; this is the Plesken Lie algebra P(F,G) of G.

If alpha : G -> F is a linear character of G the Plesken Lie
algebra can be twisted by alpha to form the Marin Lie algebra
    M(F,G,alpha) with basis g - alpha(g)*g^-1,
*/

declare verbose Plesken, 3;


intrinsic PleskenLieAlgebra(F::Rng, G::Grp : Check := false) -> AlgLie
{Return the Plesken Lie algebra of G}

  basis := {@ {g,g^-1} : g in G | g^2 ne G!1 @};

  n := #basis;
  reducedBasis := {@ Rep(b) : b in basis @};
  vprint Plesken, 2 : "Found basis";
  T := [];
  for i := 1 to n-1 do
    g := reducedBasis[i];
    for j := i+1 to n do 
      h := reducedBasis[j];
      if g*h eq h*g then continue; end if;
      ndx := [0,0,0,0];
      val := [F|0,0,0,0];
      products := [g*h, (h*g)^-1, h*g^-1, h^-1*g ];
      for t := 1 to 4 do
        a := products[t];
        if a^2 ne G!1 then
          k := Index(basis,{a,a^-1});
          v := (a in reducedBasis) select F!1 else F!(-1);
          s := Index(ndx,k);
          if s ne 0 then
            val[s] +:= v;
          else
            ndx[t] := k;
            val[t] := v;
          end if;
        end if;
      end for; // t
      for s := 1 to #ndx do
        v := val[s];
        if v ne 0 then
          k := ndx[s];
          Append(~T,<i,j,k,v>);
          Append(~T,<j,i,k,-v>);
        end if;
      end for;  // s
    end for;  // j
  end for;  // i

  vprint Plesken, 2 : "Constructing the Lie algebra";
  vprint Plesken, 2 : #T, "structure constants";
  // if Check is true this could take a long time.
  return LieAlgebra< F, n | T : Rep := "Sparse", Check := Check >;

end intrinsic;


// The parameter alpha is a linear character G -> F.
intrinsic MarinLieAlgebra(F::Rng, G::Grp, alpha::Map : Check := false) -> AlgLie
{Return the Marin (i.e. twisted Plesken) Lie algebra of G with respect to the 
 homomorphism alpha from G to the multiplicative group of the field F}
  basis := {@ {g,g^-1} : g in G | g^2 ne G!1 or alpha(g) ne F!1 @};

  n := #basis;
  reducedBasis := {@ Rep(b) : b in basis @};
  vprint Plesken,2 : "Found basis";
  T := [];
  for i := 1 to n-1 do
    g := reducedBasis[i];
    ag := alpha(g);
    for j := i+1 to n do 
      h := reducedBasis[j];
      if g*h eq h*g then continue; end if;
      ndx := [0,0,0,0];
      val := [F|0,0,0,0];
      products := [g*h, (h*g)^-1, h*g^-1, h^-1*g ];
      ah := alpha(h);
      plus := [F| 1,ag*ah ,ag, ah];
      minus := [F| -ag*ah, -1, -ah,-ag];
      for t := 1 to 4 do
        a := products[t];
        if a^2 ne G!1 or alpha(a) ne F!1 then
          k := Index(basis,{a,a^-1});
          v := (a in reducedBasis) select plus[t] else minus[t];
          s := Index(ndx,k);
          if s ne 0 then
            val[s] +:= v;
          else
            ndx[t] := k;
            val[t] := v;
          end if;
        end if;
      end for; // t
      for s := 1 to #ndx do
        v := val[s];
        if v ne 0 then
          k := ndx[s];
          Append(~T,<i,j,k,v>);
          Append(~T,<j,i,k,-v>);
        end if;
      end for;  // s
    end for;  // j
  end for;  // i

  vprint Plesken,2 : "Constructing the Lie algebra";
  vprint Plesken,2 : #T, "structure constants";
  // if Check is true this could take a long time.
  return LieAlgebra< F, n | T : Rep := "Sparse", Check := Check >;

end intrinsic;




