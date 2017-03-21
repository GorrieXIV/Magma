freeze;

/********************************************
*                                           *
*  Function(s) for ThreeSelmerGroup:          *
*     + LocalImageInSpecialCase             *
*                                           *
********************************************/

import "3selmer.m" : PrintBasis; 

// NOTES FROM THE GENERAL CASE, STILL NEED TO BE IMPLEMENTED HERE... 
// (s,t) = (x,y) and (s,t) = (x,-y), resp. The product of the images in
// these two components must be a cube. In the second component, the
// image is -(2t)^2 ~ (2t)^2, so we can take 2t as the image in the first
// component.
//
// If p is not 3, we can find the image from the Q_p-rational 3-power
// torsion.

function LocalImageInSpecialCase(V, mAS3, f, fnums, p, pids, sigma, tau, aInvs, 
                                 Klist1, Klist2, dim3tors)

  // + E is given by aInvs (over Q)
  // + V is a GF(3)-vector space representing A(S, 3), and 
  //   mAS3 : V -> A a map giving representatives mod cubes for the elements 
  // + f : (x,y) --> A, the descent map,
  //   and fnums is a sequence of numbers that determine the coefficients of f.
  // + Klist is a list of tuples <K, AAtoK> as in ThreeSelmerGroup,
  // + pids[i] are the prime ideals above p in the ith field K
                              
  Klist := Klist1 cat Klist2;
  AA := Codomain(mAS3);
  a1, a2, a3, a4, a6 := Explode(aInvs);

  // TO DO: figure out an intelligent precision
  prec := 200; // reducing this causes failures, not sure why
  vprintf Selmer,2: "\n(using %o-adic precision %o)\n", p, prec; 
  Q := Rationals();
  Qp := pAdicField(p, prec);
  Qp1 := pAdicField(p, Min(prec, 6)); // for verbose printing

  // For each pair (K, pid), get the map mW : K -> W, 
  // where the F_3 vector space W := Kv/Kv^3,
  // and package them together into a map
  // AA -> Vp := direct sum of the W's.
  Wtuples := [ [* *] : Ktup in Klist ];
  for i in [ i : i in [1..#Klist] ] do
      K, AAtoK := Explode(Klist[i]);
      Wtuples[i] := [* <W, mW> where W, mW := MakeModCubes(K, pid) : pid in pids[i] *];
  end for; 
  inds := [ i : i in [1..#Klist] | i le #Klist1 or IsOdd(i) ];
    // only one from each pair in Klist2
  Vp := KSpace(GF(3), &+[ Dimension(Wtup[1]) 
                        : Wtup in Wtuples[i], i in inds ]);
  AAtoVp := map< AA  -> Vp | 
                 aa :-> Vp! &cat[ Eltseq( (AAtoK*mW)(aa) ) 
                                     where AAtoK := Klist[i][2]
                                     where mW := Wtup[2]
                                : Wtup in Wtuples[i], i in inds ] >;

  dim1 := p eq 3 select dim3tors + 1 else dim3tors;
  vprintf Selmer, 2: "The local 3-torsion rank is %o\n", dim3tors;
  vprintf Selmer, 2: "Local image should have dimension %o\n", dim1;

  // Find the Qp-rational 3-torsion and its image in Vp
  E := EllipticCurve([a1,a2,a3,a4,a6]);
  div3 := DivisionPolynomial(E, 3);
  xs := [tup[1] : tup in Roots(div3, Qp)];
  tors3 := [];
  for x in xs do 
     ys := Roots(Polynomial([Qp| -x^3-a2*x^2-a4*x-a6, a1*x+a3, 1]));
     if #ys ne 0 then
        Append(~tors3, [Q!x, Q!ys[1][1]]); // one of each inverse pair
     end if;
  end for;
  error if 1+2*#tors3 ne 3^dim3tors, "Failed to compute local 3-torsion points";

  // TO DO: determine the required p-adic precision
// valdiscrim := Valuation(Discriminant(MinimalPolynomial(A.1)), p);
// depth3 := p eq 3 select 4 else 1;
  f0,fx,fy,fc := Explode(fnums);
  fvalBound := 20; 
/*  prec := 10 + Max( fvalBound + depth3 , valdiscrim );	
            // valdiscrim is the precision needed for factoring the polynomial,
            // depth3 is the # of p-adic significant figures needed
            //	to recognise cubes in the completions, 
            // fvalBound: we assume that there exist points P in E(Q_p)
            // 	such that f(P) is not divisible by p^fvalBound
            // 	(more precisely, by pid^(fvalBound*e(pid)) for any pid above p)
            // 	and if there are not, an error will result,
            // 10 is a safety margin.
  vprintf Selmer, 2: "p-adic precision at p = %o is %o\n", p, prec;
*/

  // WARNING: this gives up and returns zero for some 3-torsion points
  function ff(x, y) // sends a point (x,y) on E(AA) to Vp
     fAA := f(x, y);
     // if one slot is zero (which happens iff the point is 3-torsion),
     // or close to zero, then fill it in using the fact that
     // the product of all slots for which the field is Q_p 
     // should be trivial mod cubes.
     badslots := [* <i,pid> : pid in pids[i], i in [1..#Klist] 
                           | Valuation( AAtoK(fAA), pid) ge prec/2    
                                  where AAtoK := Klist[i][2] *];
     if #badslots eq 0 then
          return AAtoVp(fAA);
     elif #badslots gt 1 
          or RamificationDegree(pid)*InertiaDegree(pid) gt 1 
                          where pid := badslots[1][2] 
     then
          // don't use this point (TO DO: can the nonsplit case be handled?)
          return Vp!0;
     else 
          badi, badpid := Explode(badslots[1]);
          // fill in the bad slot
          otherdegree1slots := 
                [* <i, pid> : pid in pids[i], i in [1..#Klist]        
                           | RamificationDegree(pid)*InertiaDegree(pid) eq 1
                             and (i ne badi or pid ne badpid) *];
          otheranswers := 
            [ mW(AAtoK(fAA)) where mW := Wtuples[i][Index(pids[i],pid)][2]
                             where AAtoK := Klist[i][2]
                             where i := slot[1]
                             where pid := slot[2]
            : slot in otherdegree1slots
            | not IsEmpty(Wtuples[ slot[1] ]) ];
          missinganswer := [ - &+[w[i] : w in otheranswers] 
                           : i in [1..#Eltseq(otheranswers[1])] ];  
          return Vp! &cat[ (i eq badi and pids[i][j] eq badpid)
                            select missinganswer
                            else Eltseq( (AAtoK*mW)(fAA) ) 
                                    where AAtoK := Klist[i][2]
                                    where mW := Wtuples[i][j][2]
                         : j in [1..#Wtuples[i]], i in inds ];
                                    // inds takes the first of each pair from Klist2
     end if;
  end function;

  // image of 3-torsion in Vp 
  images := [ff(b[1], b[2]) : b in tors3];
  Wp := sub< Vp | images >;
  // subgroup of points that are possibly 3-divisible (generators of it would suffice)
  tors := [tors3[i] : i in [1..#tors3] | IsZero(images[i])];
  if IsVerbose("Selmer",2) and Dimension(Wp) gt 0 then
     printf "Local image of 3-torsion contains\n"; PrintBasis(Basis(Wp), 4);
  end if;

  if #tors gt 0 and Dimension(Wp) lt dim1 then
     m3 := DefiningEquations(MultiplicationByMMap(E, 3));
     xm3 := m3[1]/m3[3];
     num := Numerator(xm3);
     den := Denominator(xm3);
     Pol := Parent(num);
     // check y doesn't appear in the formula
     assert num eq Evaluate(num, [Pol.1,0,Pol.3]);
     assert den eq Evaluate(den, [Pol.1,0,Pol.3]);
     x := PolynomialRing(Rationals()).1;
     num := Evaluate(num, [x,0,1]);
     den := Evaluate(den, [x,0,1]);

     // the points in tors are primitive 3^e torsion points for which ff returns zero
     e := 1;
     while #tors gt 0 and Dimension(Wp) lt dim1 do
        e +:= 1;
        vprintf Selmer, 2: "Trying local 3^%o-torsion...\n", e;
        tors0 := tors;
        tors := [];
        happy := false;
        for T in tors0 do 
           pol := num - T[1]*den;
           for n := 0 to 5 do 
              try
                 nprec := 2^n*prec;
                 Qpn := pAdicField(p, nprec);
                 xs := [Q!r[1] : r in Roots(pol, Qpn)];
                 for x in xs do 
                    ys := Roots(Polynomial([Qpn| -x^3-a2*x^2-a4*x-a6, a1*x+a3, 1]));
                    if #ys ne 0 then
                       Append(~tors, [Q!x, Q!ys[1][1]]); // one of each inverse pair
                    end if;
                 end for;
                 happy := true;
               //happy := #tors gt 0; // could do this if ff always worked
              catch ERR 
                 vprintf Selmer, 2: "(need more precision than %o for roots)\n", nprec;
              end try;
              if happy then 
                 break n; 
              end if;
           end for; // n
           error if not happy, "Can't compute local torsion of order", 3^e;
        end for; // T
        images := [ff(b[1], b[2]) : b in tors];
        Wpnew := sub< Vp | images >;
        Wp := Wp + Wpnew;
        if IsVerbose("Selmer",2) and Dimension(Wpnew) gt 0 then
           printf "Local image of %o-torsion contains\n", 3^e; PrintBasis(Basis(Wp), 4);
        end if;
        tors := [tors[i] : i in [1..#tors] | IsZero(images[i])]; // 3-divisible subset of primitive 3^e torsion
     end while; // Dimension(Wp) lt dim1
  end if;

  // Find Qp-rational points on E and their images 
  // (same as in the general case, more or less)
  tries := 0;
  extra := 0;
  EXTRA := 0;
  if Dimension(Wp) lt dim1 or extra lt EXTRA then
     vprintf Selmer, 2: "Need additional generator\n";
     prec := 200; // fails badly if this is reduced, don't know why
     vprintf Selmer,2: "(using %o-adic precision %o)\n", p, prec; 
     Qp := pAdicField(p, prec); 
     Rp := Integers(Qp);
  end if;
  while Dimension(Wp) lt dim1 or extra lt EXTRA do	
    tries +:= 1;
    x := p^Random(-3,0)*Qp!Random(Rp);
    polb := a1*x + a3; polc := -(x^3 + a2*x^2 + a4*x + a6);
    flag, sqrt := IsSquare(polb^2 - 4*polc);
    if flag then
      y := Qp!((-polb + sqrt)/2);
      fval := f(Q!x, Q!y);
      // the point is okay if the value of f is not too close to 0 
      // 	in any of the local fields
      okay := true;
      for i in [1..#Klist] do
         K, AAtoK := Explode(Klist[i]);
         for pid in pids[i] do
           okay and:= 
             (Valuation( AAtoK(fval), pid) - coeffGCD)/RamificationDegree(pid) le fvalBound 
               where coeffGCD := Min([Valuation( AAtoK(f0*fcoeff) , pid) 
                                     : fcoeff in [fx,fy,fc]]);
         end for;
      end for;
      if okay then            // the point is definitely okay!
          vprintf Selmer, 3: "  Found point (%o, %o)\n", Qp1!x, Qp1!y;
          vprintf Selmer, 3: "    Check: v_%o(eqn(x,y)) = %o\n", p,
                                      Valuation(y^2 + polb*y + polc);
          if Dimension(Wp) ge dim1 then
              extra +:= 1;
          end if;
          im := ff(Q!x, Q!y);
          vprintf Selmer, 3: "   Image = %o\n", im;
          Include(~Wp, im);
          vprintf Selmer, 3: "   Dimension of image so far = %o\n", Dimension(Wp);
          error if Dimension(Wp) gt dim1,
              "Finding spurious local points at",p,
              "... try increasing p-adic precision in LocalImages\n";
      end if;
    end if;
  end while;
  if GetVerbose("Selmer") ge 2 then
    printf "Finished finding local points.\nBasis of local image:\n";
    PrintBasis(Basis(Wp), 3);
  end if;
  // Find inverse image in V
  homV := hom< V -> Vp | [ AAtoVp(mAS3(V.i)) : i in [1..Dimension(V)] ] >;
  images := [ homV(V.i) : i in [1..Dimension(V)] ];
  if GetVerbose("Selmer") ge 2 then
    printf "Images of basis elements of V:\n";
    PrintBasis(images, 3);
  end if;
  VpQ, epi := quo< Vp | Wp >;
  homVV := hom< V -> VpQ | [ epi(im) : im in images ] >;
  V1 := Kernel(homVV);
  if GetVerbose("Selmer") ge 2 then
    printf "Basis of inverse image in V:\n";
    PrintBasis(Basis(V1), 3);
  end if;
  return V1;
end function;

