freeze;

 /****************************************************************

    TWO DESCENT FOR ELLIPTIC CURVES OVER GLOBAL FUNCTION FIELDS
    (Currently some parts are only for F_p(t)).

                 Steve Donnelly, May 2006
                 Last modified: March 2010

  ****************************************************************

    TO DO NEXT: 
       * Probably not that hard to extend to general FldFun's
      
  ****************************************************************/


// A version of Roots that works over all series ring.
// When the characteristic is 0 or greater than the degree
// of the polynomial, this just calls Roots, and otherwise
// it calls Factorization.
// Same output syntax as for Roots.

function Roots_series_ring( pol, prec)   // -> [ Tup ]   (just like Roots)
   F<tt> := BaseRing(pol);
   char := Characteristic(F);
   if char eq 0 or char gt Degree(pol) then return Roots(pol, prec); end if;
   factn := Factorization(pol);
   ans := [ < -coeffs[1]/coeffs[2], fact[2] >  where coeffs:=Coefficients(fact[1])
          : fact in factn | Degree(fact[1]) eq 1 ];
   // Note: we're really cutting it fine with the current precision settings, 
   // not really enough to guarantee correctness!
   assert &and[ Valuation(Evaluate(pol,rt[1])) gt Min(20, prec-10) : rt in ans ];          
   return ans;
end function;


// A set of n places of F, with degrees as small as possible

function some_small_places(F, n : avoid:={} )   // -> SetEnum[PlcFunElt]
  places := []; 
  q := #ConstantField(F);
  max_avoid := Max([0] cat [Degree(pl) : pl in avoid]);
  for deg := 1 to 100 do
    if deg gt max_avoid and n - #places ge q^deg div 2 then 
      newplaces := Places(F, deg); 
      places cat:= [newplaces[i] : i in [1..N]] where N := Min(#newplaces, n-#places);
    else
      for i := 1 to Min( n-#places, q^deg div 2) do 
        _,pl := HasRandomPlace(F,deg); 
        if pl notin avoid and pl notin places then 
          Append(~places, pl); if #places ge n then break deg; end if;
        end if;
      end for;
    end if;
  end for;
  return places;
end function;


/**********************************************************************/

// Hacky functions for "rational reconstruction" 
// (not intended to be efficient for large precision).
// Now using the inbuilt map (after first reducing the precision
// to the requested precision, to save time).
// Everything else here is obselete.

function lift_residuefield_generator(pl, FtoFpl)
  F := Domain(FtoFpl);
  Fpl := Codomain(FtoFpl);
  k, Ftok := ResidueClassField(Ideal(pl));
  p := Characteristic(k);
  conjugates := [ (k.1)^(p^i) : i in [1..Degree(k)] ];
  for c in conjugates do
     liftc := c @@ Ftok;
     if LeadingCoefficient(liftc @ FtoFpl) eq k.1 then return F!liftc; end if;
  end for;
  print "No such element was found";
  return false;
end function;


// Given a map FtoFpl as returned by 
// > Fpl, FtoFpl := Completion(F, pl);
// where F is a FldFun and pl is a place of F,
// and given an element ser in Fpl,
// compute an element of F whose image under FtoFpl 
// agrees with ser, to relative precision prec.
// (If prec is larger than the relative precision of ser,
//  prec is reduced accordingly, and a warning is printed.)

function approximation_to_laurentseries( ser, pl, FtoFpl, prec)
  ser +:= O(Parent(ser).1^(3+prec+Valuation(ser))); // so that the reconstruction is only done
                                                    // to relative precision prec (to save time)
  ans := ser @@ FtoFpl;  
  //time  assert Valuation(ser-FtoFpl(ans)) ge prec + Valuation(ser);  // extremely slow!!
  return ans;
  
  // Obselete version:
  if prec gt RelativePrecision(ser)-1 then 
     prec := RelativePrecision(ser)-1;
     print "WARNING in approximation_to_laurentseries: reducing precision to", prec;
  end if;
  F := Domain(FtoFpl);
  Fpl := Codomain(FtoFpl);
  k, Ftok := ResidueClassField(Ideal(pl));
  g := lift_residuefield_generator(pl, FtoFpl);  // maps to k.1 mod pl, under FtoFpl
  assert LeadingCoefficient( FtoFpl(g) ) eq k.1;
  u := UniformizingElement(pl);
  u_lc := LeadingCoefficient(FtoFpl(u));
  u_lc_lift :=  &+[ Eltseq(u_lc)[i+1]*g^i : i in [0..Degree(k)-1] ];
  u := u/u_lc_lift;  // should have FtoFpl(u) = 1 mod pl^2
  assert LeadingCoefficient(FtoFpl(u)) eq 1;
  ans := F!0;  // stores the approximation to ser
  for i := 1 to prec do
     newser := ser-FtoFpl(ans);
     val := Valuation(newser);
     if val ge prec + Valuation(ser) then break; end if;
     const := Eltseq(newser)[1];
     assert Parent(const) eq k;
     liftedconst := &+[ Eltseq(const)[i+1]*g^i : i in [0..Degree(k)-1] ];
     ans +:= liftedconst * u^val;
  assert Valuation(ser-FtoFpl(ans)) ge i + Valuation(ser);
  end for;
  assert Valuation(ser-FtoFpl(ans)) ge prec + Valuation(ser);
  // Compare with the inbuilt map:
  assert Valuation( ans - ser@@FtoFpl, pl) gt 10;
  return ans;
end function;


/**********************************************************************/

// Functions related to finding local weak-Mordell-Weil groups


// For an extension A of some F, and a place pl of F,
// return a vector space representing (A tensor F_pl)*/squares,
// in other words the direct sum of (A_Pl*)/(A_Pl*)^2 for Pl above pl.
function localmodsquares(A, pl : debug:=false )
  F := BaseField(A);
  cubic := MinimalPolynomial(A.1);
  assert Degree(cubic) eq 3;
  p := Characteristic(A);
  OA := IsFinite(pl) select MaximalOrderFinite(A)
                      else  MaximalOrderInfinite(A);
  factpl := Factorization(ideal<OA | Ideal(pl) >);
  Pls := [ Place(factor[1]) : factor in factpl ];
  if #Pls eq 1 then return "onlyoneplace",_,_; end if;
  Sort( ~Pls, func< pl1,pl2 | RamificationDegree(pl1)- RamificationDegree(pl2) >);

  // Find uniformisers for the Pls ...
  // The uniformisers should have the following property (which is assumed by
  // the code for computing the images in Wpl of 2-torsion):
  // "For any subset of the Pls, if the product of local norms of the uniformisers
  // at those Pl has even valuation in Fpl, then in fact it is a square in Fpl."
  if &and[ RamificationDegree(Pl) eq 1 : Pl in Pls] then
     u := UniformizingElement(pl);
     Uniformisers := [ u : Pl in Pls ];
  else 
     assert RamificationDegree(Pls[2]) eq 2; 
     if not debug then Uniformisers := [ UniformizingElement(Pl) : Pl in Pls ];
     else
       t_0 := Cputime();
       vprint Selmer, 3: "Calling SafeUniformiser ... ";
       u1 := A! SafeUniformiser(Ideal(Pls[1]));
       u2 := A! SafeUniformiser(Ideal(Pls[2]));
       vprintf Selmer, 3: "    ... done with SafeUniformiser, time = %o sec\n", Cputime(t_0);
       
       // Adjust the uniformisers to satisfy the property stated above ... 
       // for this we need to compute a local norm for the ram. quad. extension.
       // We approximate this extension as a quadratic extension of F.
       prec_u := 3*Valuation(Discriminant(cubic), pl) + 100;  // generous precision in this one-off calc'n.
       newFpl, inj := Completion(F, pl : Precision:=prec_u );
       cubic_pl := Polynomial([ inj(c) : c in Coefficients(cubic) ]);
       /*
       // Work around using Roots (since our case is just degree 3):
       cubicroot := Roots(cubic_pl, prec_u-10 )[1][1];
       factor2 := cubic_pl div Polynomial([-cubicroot,1]);
       */
       fact_cubic := Factorisation(cubic_pl);
       assert #fact_cubic eq 2;
       exists(factor1){ factor[1] : factor in fact_cubic | Degree(factor[1]) eq 1 };
       exists(factor2){ factor[1] : factor in fact_cubic | Degree(factor[1]) eq 2 };
       cubicroot := Roots(factor1 : Precision:=prec_u-10 )[1][1];
       
       // lift factor2 to a poly over F, and lift the zero of factor1:
       // approximation_to_laurentseries is time consuming, 
       // therefore we use low precision which could be risky 
       cubicroot_approx := approximation_to_laurentseries(cubicroot,pl,inj,10);
       factor2_approx := Polynomial([ approximation_to_laurentseries(c,pl,inj,10)
                                    : c in Coefficients(factor2) ]);
       F2 := ext< F | factor2_approx >;
       AtoF2 := hom< A -> F2 | F2.1 >;  // not a hom, but Magma doesn't know this!
       AtoF := hom< A -> F | cubicroot_approx >;  // this approximates the injection A -> F_pl
                                                  // at the degree one place of A above pl.
       localnorm_of_u2 := Norm(AtoF2(u2));
       approx_u1 := AtoF(u1);
       assert Valuation(approx_u1, pl) eq 1 and Valuation(localnorm_of_u2, pl) eq 1;
       k, tok := ResidueClassField(Ideal(pl));
       while not IsSquare( inj(approx_u1*localnorm_of_u2) ) do
          // multiply by a nonsquare (from the constant field)
          nonsq := Random(ResidueClassField(Ideal(pl))) @@ tok;
          if nonsq eq 0 then continue; end if;
          u1 *:= nonsq;
          approx_u1 *:= nonsq;
       end while;
       Uniformisers := [u1, u2];
     end if; // debug 
     assert Valuation(Uniformisers[1], Pls[1]) eq 1 and Valuation(Uniformisers[2], Pls[2]) eq 1;
  end if;

  // Each Pl contributes a vector space of dimension 2 to Wpl:
  // the first slot is valuation, the second is Legendre symbol of the leading coeff.
  Wpl := VectorSpace( GF(2), 2*#Pls );
  maps := [];
  for Pl in Pls do
     u := Uniformisers[Index(Pls,Pl)];
     GFp, modPl := ResidueClassField(Ideal(Pl));
     Append( ~maps, map< A->GF(2) | a :-> Valuation(a,Pl) > );
     function map2(a, Pl, modPl, u)  // do it like this for easier debugging
       bits, mults := ProductRepresentation(a);
       amodPl := &*[Codomain(modPl)| modPl( bits[i] / u^Valuation(bits[i],Pl) )^mults[i] : i in [1..#bits]]; 
       return IsSquare(amodPl) select 0 else 1;
     end function;
     Append( ~maps, map< A->GF(2) | a :-> map2(a, Pl, modPl, u) > );
  end for;
  AtoWpl := map< A -> Wpl | a :-> Wpl! [a@mp : mp in maps] >;
  return Wpl, AtoWpl, Pls;
end function;


// For E defined over F, and a place pl of F,
// compute the local points E(F_pl)/2E(F_pl)
// as a subspace of Wpl. 
// EtoWpl is a map from F to Wpl.
// The function will only terminate if the subspace of Wpl
// generated by the points has the expected dimension.

function localEmod2E(E, pl, Pls, Wpl, EtoWpl, theta : Fast:=false, debug:=false )
  a1,a2,a3,a4,a6 := Explode(aInvariants(E));
  assert a1 eq 0 and a3 eq 0;
  F := BaseField(E);
  t := F! BaseField(F).1;
  p := Characteristic(F);
  k, Ftok := ResidueClassField(Ideal(pl));
  w := PolynomialRing(F).1;
  cubic := w^3+a2*w^2+a4*w+a6;
  GFp, modpl := ResidueClassField(Ideal(pl));
  u := UniformizingElement(pl);
  discval := Max(0,Valuation(Discriminant(cubic), pl));

  // Figure out the dimension of E(Fl)/2E(Fl) as a Z/2-module, 
  // which equals the dimension of E(Fl)[2]
  expecteddim := Dimension(Wpl) div 2 - 1;
  vprintf Selmer,2: "  Dimension of local E/2E should be %o.\n", expecteddim; 
  ImE := sub< Wpl | >;

  // figure out the image of E[2](Fpl) in Wpl
  // (when there is no 4-torsion, this should generate the whole image).
  prec := 30+2*discval;
  vprint Selmer,2: "  Try local 2-torsion:";
  Fpl, FtoFpl := Completion(F, pl : Precision:=prec);  
  cubic_pl := Polynomial([FtoFpl(c) : c in Coefficients(cubic)]);
  cubic_roots := [ crt[1] : crt in Roots_series_ring(cubic_pl, prec-10) ];
  assert [#cubic_roots, expecteddim] in {[0,0], [1,1], [3,2]};
  vprint Selmer,4: "    roots of cubic are ", cubic_roots;
  for xx in cubic_roots do
     // take a nearby point (since we cannot evaluate EtoWpl on 2-torsion)
     power := discval+10;  // must be larger than discval, but less than prec-discval
     if IsOdd(Valuation( Evaluate(cubic_pl, xx+Fpl.1^power) )) then power +:= 1; end if;
      assert Valuation(Fpl.1) eq 1;
      delta := Fpl.1^power;
      if not IsSquare( Evaluate(cubic_pl, xx+delta) ) then 
        // find a non-square in k:
        if Degree(k) gt 1 then nsq := PrimitiveElement(k);
        else for c := 2 to #k do if not IsSquare(k!c) then nsq := c; break; end if; end for;
        end if;
        assert not IsSquare(nsq);
        delta := nsq*delta;
        error if not IsSquare( Evaluate(cubic_pl, xx+delta) ),  
          "Something went wrong while trying to find a local point close to a 2-torsion point";
     end if;
     nearxx := approximation_to_laurentseries(xx+delta, pl, FtoFpl, 20+discval); 
     val_nearxx := Evaluate(cubic_pl, FtoFpl(nearxx));
     assert IsSquare( val_nearxx );
     ImE := sub< Wpl | Basis(ImE), Eltseq(EtoWpl(nearxx)) >; 
  end for;

  vprintf Selmer,2: "  2-torsion gives a %o dimensional subspace\n", Dimension(ImE);
  if Dimension(ImE) gt 0 then vprint Selmer,3: "Image so far is ", ImE; end if;
  error if Dimension(ImE) gt expecteddim, "Finding bogus local points at", pl;
  if not debug and Dimension(ImE) eq expecteddim then return ImE; end if;

  // Try 2^n torsion for n = 2, 3, ...
  Fast := Fast and Characteristic(k) gt 6; // only be Fast when Roots not Factorization will be used.
  prec := Fast select 10+discval
                else  20+discval;
  margin := Fast select 5 else 10;
  Fpl<tt>, FtoFpl := Completion(F, pl : Precision:=prec);  
  mult2_E := DefiningEquations(MultiplicationByMMap(E,2));
  mult2_x_num := Evaluate( mult2_E[1], [w,1,1]) div cubic; 
  mult2_x_den := Evaluate( mult2_E[3], [w,1,1]) div cubic; 
  n := 1;
  while Dimension(ImE) lt expecteddim and n lt 7 do
    n +:= 1;
    if n eq 2 then
      divpol2n := DivisionPolynomial(E, 2^n) div DivisionPolynomial(E, 2^(n-1));
      vprintf Selmer,2: "  Try local %o-torsion: \n", 2^n;
      vprintf Selmer,4: "     Division poly is %o\n", divpol2n;
      divpol2n_pl := Polynomial([FtoFpl(c) : c in Coefficients(divpol2n)]);
      roots2n := [ root[1] : root in Roots_series_ring(divpol2n_pl, prec-margin) 
                           | Valuation( Evaluate(cubic_pl,root[1]) ) le 10
                             and IsSquare( Evaluate(cubic_pl,root[1]) ) ];
      approx_roots2n := [ approximation_to_laurentseries(root,pl,FtoFpl,margin) : root in roots2n ];
    else
      // For higher 2^n torsion, try to divide each primitive 2^(n-1) torsion point by 2.
      vprintf Selmer,2: "  Try local %o-torsion: \n", 2^n;
      roots2n := [];
      for rt in approx_roots2n do  // the old one, so these are 2^(n-1) torsion points
        divpol_rt := mult2_x_num - rt*mult2_x_den;
        divpol_rt_pl := Polynomial([FtoFpl(c) : c in Coefficients(divpol_rt)]);
        newroots2n := [ root[1] : root in Roots_series_ring(divpol_rt_pl, prec-margin) ];
      if expecteddim eq 1 then 
         assert #newroots2n eq 2;  // inverse pair, we only need one of them
         Append( ~roots2n, newroots2n[1]);
      else
         // TO DO: do something in this case too, to cut down combinatorial explosion
         roots2n cat:= newroots2n;
      end if;
      end for;
      // the corresponding y-coords are automatically rational this time: 
      assert &and[ IsSquare(Evaluate( cubic_pl, root)) : root in roots2n ];
      approx_roots2n := [approximation_to_laurentseries(root,pl,FtoFpl,margin) : root in roots2n];
    end if;
    vprint Selmer,4:  "approx roots are ", approx_roots2n;
    assert #approx_roots2n gt 0; // because if there were no primitive 2^n torsion, 
                                 // then the 2^(n-1) torsion should have generated E/2E

    ImE := sub< Wpl | Basis(ImE), [EtoWpl(xx) : xx in approx_roots2n] >;

    vprintf Selmer,2: "  %o-torsion gives a %o dimensional subspace\n", 2^n, Dimension(ImE);
    if Dimension(ImE) gt 0 then vprint Selmer,3: "Image so far is ", ImE; end if;
    error if Dimension(ImE) gt expecteddim, "Finding bogus local points at", pl;
  end while;  
  if not debug then return ImE; end if;

  // Search for points in E(F_pl)
  // This code is used only in occasional cases (except as a check). 
  // In hard cases it was pretty useless anyway!!
  // TO DO (if we ever want to use it):
  //        i) do a search focused on E_0(K_v)
  //       ii) test some cases where (say) 8-torsion generates 
  //           but this code failed miserably to find generators.
  coeffdenomval := Max([0, -6*Valuation(a2,pl), -4*Valuation(a4,pl), -2*Valuation(a6,pl)]);
  numextrapts := 0;  // usual safety check: find a few extra points and make sure the dimension is still ok
  while Dimension(ImE) lt expecteddim or numextrapts lt 5 or debug and IsFinite(pl) and numextrapts lt 50 do 
    if Dimension(ImE) ge expecteddim then numextrapts +:= 1; end if;
    old := Dimension(ImE);  // used only for debug printing
    // Generate a random point in E(F_pl)
    foundpt := false;
    rand := Random(19);  // choose method: the new method is so much slower, so don't use it too often! 
    if rand eq 0 then     
       // "new method": try random y close to 0.
       // since there might not be any points close to 0, don't search forever ...
       for ntries := 1 to 30 do
         yyval := Random( 3*discval + 10 );
         repeat yy := u^yyval* &+[ Random(GF(p))*u^i : i in [0..5] ]; until yy ne 0;
         xxpol := w^3+a2*w^2+a4*w+a6-yy^2;
         xxprec := 2*Valuation(Discriminant(xxpol),pl) + 2*coeffdenomval + 2*yyval + 30;
                   // needs to be enough to tell whether xx-theta is a square ...
                   // The choice here is based on clearing denoms + Hensel's lemma.
         newFpl, inj := Completion(F, pl : Precision:=xxprec);
         xxpol_pl := Polynomial([inj(c) : c in Coefficients(xxpol)]);
         roots := Roots_series_ring(  xxpol_pl, xxprec-10 );
               // Using precision less that xxprec, to avoid some kind of stupidity from Roots
         foundpt := #roots gt 0;
         if foundpt then
           assert &and[ Valuation(Evaluate(xxpol_pl, rt[1])) gt xxprec-coeffdenomval-20 : rt in roots ];
           // now get the root back into F
           xx := approximation_to_laurentseries(roots[1][1], pl, inj, xxprec-10); 
           vprintf Selmer, 4: "new method found point xx = %o, Valuation = %o\n", 
                               xx, Valuation( xx^3+a2*xx^2+a4*xx+a6-yy^2, pl);
           break; 
         end if;
         if ntries eq 30 then 
            vprint Selmer, 4: "New method: looked for points with small y, but couldn't find any"; 
         end if;
       end for;
    end if;

    if not foundpt then  
       // try random x
       while true do
         randomint := 0; while Random(1) eq 1 do randomint +:= 1; end while;
         val := -2*randomint;
         xx := u^val* &+[ Random(GF(p))*u^i : i in [0..5] ];
         if Valuation(xx,pl) ge 0 then continue; end if; 
         cubicxx := xx^3+a2*xx^2+a4*xx+a6;
         valcubicxx := Valuation(cubicxx,pl);
         if IsOdd(valcubicxx) then continue; end if;
         rescubicxx := modpl( cubicxx/u^valcubicxx );
         foundpt := IsEven(valcubicxx) and IsSquare(rescubicxx); 
         // Note: since xx has neg valuation and the coefficients are integral,
         // the point can't reduce to a singular point, so is Hensel-liftable
         vprintf Selmer, 4: "old method found pt xx = %o\n", xx;
              //  and Valuation(yy^2-xx^3-a2*xx^2-a4*xx-a6,pl) lt (prec-20)*Min([0,val,minval]) 
              //        where minval := Min([Valuation(a,pl) : a in [a2,a4,a6]]); 
         if foundpt then break; end if;
       end while;
    end if;

    ImE := sub< Wpl | Basis(ImE), EtoWpl(xx) >;
    if Dimension(ImE) gt old then 
       vprintf Selmer,3: "  Found a %o dimensional subspace (expected %o)\n", 
                            Dimension(ImE), expecteddim;
       vprint Selmer,3: "ImE is now", ImE;
    end if;
    error if Dimension(ImE) gt expecteddim, "Finding bogus local points at", pl;
  end while;
  error if Dimension(ImE) ne expecteddim, "Couldn't find enough local points at", pl;
  return ImE;
end function;


/*******************************************************************************************/


intrinsic TwoSelmerGroup(E::CrvEll[FldFunG] : Fast:=false ) -> GrpAb, Map
{The 2-Selmer group of an elliptic curve defined over a rational function field, 
as an abstract group, and map from this group to the standard etale algebra. 
The Fast option uses less precision in some of the local calculations 
(possibly too little!)}

  if assigned E`TwoSelmerGroup then 
    return E`TwoSelmerGroup[1], E`TwoSelmerGroup[2]; end if;
  
  F := BaseField(E);
  Eorig := E;
  Forig := F; 
  if Type(F) eq FldFunRat then  // change it into a FldFun
     F := ext< F | PolynomialRing(F)! [-1,1] >;
     E := BaseChange(E,F);
  end if;
  require Type(BaseField(F)) eq FldFunRat :
    "The base field must be either a rational function field, or an absolute extension of one";
  p := Characteristic(F);
  require p ne 0 : "Not implemented for curves over function fields of characteristic 0";
  require p ne 2 : "Not implemented for curves over function fields of characteristic 2";

  // Put E in "completed square" form
  // a1,a2,a3,a4,a6 := Explode(Coefficients(MinimalModel(E)));
  a1,a2,a3,a4,a6 := Explode(Coefficients(E));
  E := EllipticCurve([0,a2+a1^2/4,0,a4+a1*a3/2, a6+a3^2/4]);
  _,a2,_,a4,a6 := Explode(Coefficients(E));

  badplaces := BadPlaces(E);
  vprintf Selmer,1: "Using model E : %o\nE has bad reduction at %o\n", E, badplaces;
  badplaces_orig := [Forig| Generators(Ideal(pl))[1] : pl in badplaces];
  cps := [LocalInformation(Eorig,pl)[4] : pl in badplaces_orig];
  badplaces := [badplaces[i] : i in [1..#badplaces] | IsEven(cps[i])];
  vprintf Selmer,1: " with Tamagawa numbers %o,", cps;
  vprintf Selmer,1: " so the bad places for two-descent are %o\n", badplaces;

  // A is just F[x]/cubic(x)
  PolF := PolynomialRing(F);
  cubic := PolF.1^3 + a2*PolF.1^2 + a4*PolF.1 + a6;
  require IsIrreducible(cubic) : "Not yet implemented for curves with nontivial 2-torsion";
  A<theta> := ext< F | cubic >;
  badplacesA := &cat[ Decomposition(A,pl) : pl in badplaces ];
  vprintf Selmer,3: "The algebra is %o\n and the bad places split into %o\n of degrees %o\n", 
                     A, badplacesA, [ Degree(pl) : pl in badplacesA ];
  vprintf Selmer,3: "and ramification degrees %o\n", [RamificationDegree(pl) : pl in badplacesA];
  S := { Places(A) | pl : pl in badplacesA };
  // Compute the class group of A (modulo S-units) and figure out 
  // the corresponding elements of (A*)/(A*)^2, as elements of A
  // TO DO: is it more efficient to call SClassGroupExactSequence, or do SUnits first?
  vprintf Selmer,1: "\nComputing an S-class group of a genus %o curve ... ", Genus(A); vtime Selmer,1:
  Cl_S, Cl_StoDivA, DivAtoCl_S := SClassGroup(S);
  Cl_Stwotorsbasis := [ (Order(g) div 2)*g : g in Generators(Cl_S) 
                                          | m ne 0 and IsEven(m) where m := Order(g) ];
  classgroupguys := [];
  for g in Cl_Stwotorsbasis do 
     bool, a := IsSPrincipal(2*Cl_StoDivA(g), S);
     require bool: "Something is wrong with the class group elements";
     Append( ~classgroupguys, a);
  end for;

  // Put in units and S-units for bad places.
  vprintf Selmer,1: "Now computing S-units ... "; vtime Selmer,1:
  SUnits, SUtoA := SUnitGroup(S);
  AS2gens := classgroupguys cat [ SUtoA(su) : su in Generators(SUnits) ];
  vprintf Selmer,2 : "Full KS2 space has dimension %o\n", #AS2gens;

  S2E := VectorSpace( GF(2), #AS2gens );  
  S2EtoA := map< S2E -> A | s :-> &*[A| AS2gens[i] : i in [1..Dimension(S2E)] 
                                                   | Eltseq(s)[i] eq 1] >;
            // maybe should use SUtoA on the unit part of S2E ??
  
  // Take kernel of the norm:
  // The method is to use local reductions at several places 
  // (as well as valuations of bad places) to detect which norms are squares.
  // The point is that this way one has a homomorphism to work with, and 
  // therefore only need to compute values for the basis. 
  // If the new basis elements do not all have square norm, we repeat
  // the procedure, taking reductions at an enlarged set of places.
  used_places := InfinitePlaces(F);
  S2E_square := sub<S2E|0>; // the subspace generated by all square basis_norms found so far
  i := 0; 
  vprintf  Selmer,2: "Taking kernel of norm ... "; vtime Selmer,2:
  while true do
    i +:= 1;
    S2E_basis := Basis(S2E);
    basis_norms := [ Norm(s @ S2EtoA) : s in S2E_basis ];
    Include(~S2E_square, [S2E_basis[i] : i in [1..#S2E_basis] | IsSquare(basis_norms[i])] );
    if Dimension(S2E) eq Dimension(S2E_square) then break; end if;
    // IsSquare is relatively expensive, so test at enough places to have
    // a good chance of getting down to the right answer in this iteration.
    places := some_small_places(F, 2+#basis_norms : avoid:=used_places );
    used_places cat:= places;
    val_places := i eq 1 select Seqset(badplaces) else {};
    places0 := places;
    for pl in places0 do 
      if pl in val_places then Exclude(~places,pl); continue pl; end if;
      for ns in basis_norms do 
        if Valuation(ns,pl) ne 0 then 
          Include(~val_places,pl); Exclude(~places,pl); continue pl; end if;
      end for;
    end for;
    resmaps := [ resmap where _,resmap := ResidueClassField(Ideal(pl)) : pl in places ];
    VV := VectorSpace(GF(2), #val_places+#places);
    images_in_VV := [VV| [Valuation(b, pl) : pl in val_places] cat
                         [IsSquare(resmap(b)) select 0 else 1 : resmap in resmaps]
                       : b in basis_norms ];
    assert Basis(S2E) eq S2E_basis; // otherwise the next line is wrong
    S2EtoVV := hom< S2E -> VV | images_in_VV >;
    S2E := Kernel(S2EtoVV);
    if Dimension(S2E) eq Dimension(S2E_square) then break; end if;
  end while;
  vprintf Selmer,1: "After global computations, upper bound on Selmer rank is %o\n", Dimension(S2E);
 
  // LOCAL CONDITIONS
  // deal with the infinite place(s) last 
  // (and perhaps avoid dealing with them)
  badplaces_finite := [ pl : pl in badplaces | IsFinite(pl) ];
  Sort( ~badplaces_finite, func< pl1, pl2 | Degree(pl1)-Degree(pl2) >);
  badplaces_infinite := [ pl : pl in badplaces | not IsFinite(pl) ];
  
  for pl in badplaces_finite cat badplaces_infinite do 
     if Dimension(S2E) eq 0 then break; end if;
     vprintf Selmer, 1: "\nComputing local points at the place %o \n", pl;
     timeon := Cputime();
     // vector space over GF(2) representing (A tensor F_pl)* mod squares:
     Wpl, AtoWpl, Pls := localmodsquares(A, pl );
     vprint Selmer, 4: "Finished setting up the map A --> A_pl/(A_pl)^2";
     if Wpl cmpeq "onlyoneplace" then 
        vprint Selmer, 1: "The local condition is trivial (so don't search for local points)";
        continue;
     end if;

     // rescale E to have integral coefficients
     u := UniformizingElement(pl);
     E_int := E;
     scalingfactor := 1;
     while Min([ Valuation(c,pl) : c in Coefficients(E_int) ]) lt 0 
        do scalingfactor *:= u;
        E_int := EllipticCurve([0, u^2*a2, 0, u^4*a4, u^6*a6]) 
                 where  _,a2,_,a4,a6 := Explode(Coefficients(E_int));
     end while;
     E_inttoWpl := map< F -> Wpl | xx :-> (xx-scalingfactor^2*theta) @ AtoWpl >;
     assert Evaluate(w^3+a2*w^2+a4*w+a6,scalingfactor^2*theta) eq 0 
              where  _,a2,_,a4,a6 := Explode(Coefficients(E_int)) where w := PolF.1;
     if scalingfactor ne 1 then 
        vprintf Selmer, 3:  "Scaling by a factor %o to make E integral\n", scalingfactor;
     end if;
     ImE := localEmod2E(E_int, pl, Pls, Wpl, E_inttoWpl, scalingfactor^2*theta : Fast:=Fast );  
            // returns a subgroup of Wpl
     vprintf Selmer, 1: "Took %o sec to compute local points at %o\n", Cputime(timeon), pl;
  
     // Impose the local condition.
     WplmodImE, modImE := quo< Wpl | ImE >;
     vprint Selmer, 3: 
        "Images of generators of S2E in Wpl are", [s @S2EtoA @AtoWpl : s in Basis(S2E)];
     vprintf Selmer, 2: "Imposing local condition ... ";  vtime Selmer, 2:
     S2E := Kernel(hom< S2E -> WplmodImE | [s @S2EtoA @AtoWpl @modImE : s in Basis(S2E)] >);
     vprintf  Selmer,1: "Upper bound on Selmer rank is now %o\n", Dimension(S2E);
     if Dimension(S2E) eq 0 then break; end if;
  end for;  // pl in badplaces

  // Convert to a group ...
  S2Egroup := AbelianGroup([2 : i in [1..Dimension(S2E)]]);
  S2EgrouptoA := map< S2Egroup -> A | 
                            s :-> &+[Eltseq(s)[i]*Basis(S2E)[i] : i in [1..Dimension(S2E)]] @ S2EtoA >;
  Eorig`TwoSelmerGroup := <S2Egroup, S2EgrouptoA>;
  return S2Egroup, S2EgrouptoA;
end intrinsic;

function expand_product(x)
  prod, exp := ProductRepresentation(x);
  if #prod gt 1 then
    exp2 := [e mod 2 : e in exp];
    x := PowerProduct(prod, exp2); 
  end if;
  return x;
end function;

intrinsic TwoDescent(E::CrvEll[FldFunG]) -> SeqEnum[Crv], List
{Given a curve E over a function field, this represents the nontrivial elements in TwoSelmerGroup(E) 
 as hyperelliptic curves C : y^2 = quartic(x).  Returns a sequence containing these curves, and a list
 containing the corresponding maps C -> E.}
  F := BaseField(E);
  S, Smap := TwoSelmerGroup(E);
  Cs := [];
  CtoEmaps := [* *];
  for s in [s: s in S | s ne S!0] do 
    // Expand product reps by taking exp vector mod 2; seems massively better, 
    // even though this could in principal result in larger products 
    // TO DO: for a basis of S? (LLL basis to make product degree small)
    a := s @ Smap;
    a := expand_product(a);
    bool, sqrtNa := IsSquare(Norm(a));  assert bool;  sqrtNa := F!sqrtNa;
    L<theta>  := Parent(a);
    _<w0,w1,w2,w3> := PolynomialRing(L,4);
    /* TO DO!!  (Need to change the hard-coded formulae below)
    OL := MaximalOrderFinite(L);
    bas := Basis(&*[ t[1]^(t[2] div 2) : t in Factorization(a*OL) ]);
    w := bas[1]*w0 + bas[2]*w1 + bas[3]*w2;
    */
    w := w0+theta*w1+theta^2*w2;
    xminustheta := a*w^2;
    // extract coefficients of theta and theta^2
    mons := Monomials(xminustheta);
    coeffs := Coefficients(xminustheta);
    assert xminustheta eq &+[ coeffs[i]*mons[i] : i in [1..#mons]];
    coeff_of_theta := &+[ Eltseq(coeffs[i])[2]*mons[i] : i in [1..#mons]];
    coeff_of_theta_squared := &+[ Eltseq(coeffs[i])[3]*mons[i] : i in [1..#mons]];

    // the following is used for the covering map in the general case
    coeff_of_one := &+[ Eltseq(coeffs[i])[1]*mons[i] : i in [1..#mons]];
    eqns := [coeff_of_theta + w3^2, coeff_of_theta_squared];
    PF4<R,S,T,U> := PolynomialRing(F,4);
    ChangeUniverse( ~eqns, PF4);
    QI := Curve(Scheme( ProjectiveSpace(PF4), eqns));
    assert IsIsomorphic( E, Jacobian(GenusOneModel(QI)) );
    assert Evaluate( DefiningEquations(QI)[2], [0,0,0,U]) eq 0;
    n := Norm(theta); tr := Trace(theta); tr2 := Trace(theta^2); tr3 := Trace(theta^3);
    trm1 := Trace(1/theta); trm2 := Trace(1/theta^2);
    norm_w := w0^3 + n*w1^3 + n^2*w2^3 + (tr*tr2-tr3)*w0*w1*w2 +
              tr*w0^2*w1 + n*trm1*w0*w1^2 + tr2*w0^2*w2 + n^2*trm2*w0*w2^2 
                                            + n*tr*w1^2*w2 + n^2*trm1*w1*w2^2;
    c6,c4,c2 := Explode(Coefficients(DefiningPolynomial(L)));
    EE := EllipticCurve([F|0,c2,0,c4,c6]);
    bool, EEtoE := IsIsomorphic(EE,E);  assert bool;
    QItoEE := map< QI->EE | [Evaluate(coeff_of_one,[R,S,T,0]), 
                             sqrtNa*Evaluate(norm_w,[R,S,T,0])/U, U^2]>;
    
    PF3 := PolynomialRing(F,3);
    conic := Conic(ProjectiveSpace(PF3),  
                   Evaluate(coeff_of_theta_squared,[PF3.1,PF3.2,PF3.3,0]) );
    param := DefiningEquations(Parametrization(conic));
    for eqn in param do assert IsHomogeneous(eqn) and TotalDegree(eqn) eq 2; end for;
    quartic := Evaluate(coeff_of_theta, param cat [0]);

    model := GenusOneModel(-quartic);
    minmodel, trans := Minimise(model);
    sqrt_scaling, mat := Explode(Tuple(trans));
    
    // general way to get covering map
    C0 := HyperellipticCurve(model);
    C := HyperellipticCurve(minmodel);
    CtoC0 := map< C -> C0 | [mat[1,1]*C.1+mat[2,1]*C.3, C.2/sqrt_scaling, mat[1,2]*C.1+mat[2,2]*C.3] >;
    C0toQI := map< C0 -> QI | [Evaluate(eqn,[C0.1,C0.3]) : eqn in param] cat [C0.2] >;
    CtoE := CtoC0 * C0toQI * QItoEE * EEtoE;
    CtoE := Expand(CtoE);

    // get covering map from invariants (doesn't work in characteristic 3)
    /*
    if Characteristic(F) gt 3 then 
      C,E1,CtoE1 :=  nCovering(GenusOneModel(quarticmin));
      bool, E1toE := IsIsomorphic(E1,E);  assert bool;
      CtoE := Expand(CtoE1*E1toE);
    end if;
    */
    Append( ~Cs, C);
    Append( ~CtoEmaps, CtoE);
  end for;

  return Cs, CtoEmaps;  
end intrinsic;

