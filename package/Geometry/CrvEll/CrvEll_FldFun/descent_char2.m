freeze;

/*********************************************************************

         DESCENT VIA 2-ISOGENIES FOR ELLIPTIC CURVES OVER 
           RATIONAL FUNCTION FIELDS OF CHARACTERISTIC 2
 
                  Steve Donnelly, April 2007

*********************************************************************/

forward FindSubspace;

debug_level := 0;
debug := debug_level gt 0;


// The 2-covering curve !!of E^Frob!! corresponding to c in K*/K^2
// (obtained by substituting cw^2 for x in E^Frob and rearranging)

function two_covering(E, c : return_map:=false)
   a1,a2,a3,a4,a6 := Explode(Coefficients(E));  assert a3 eq 0;
   Pr121 := ProjectiveSpace(BaseRing(E),[1,2,1]);   
   W:=Pr121.1; Y:=Pr121.2; Z:=Pr121.3;
   cov := Curve(Pr121, Y^2 + a1^2*c*W*Y*Z - c^3*W^4 - a2^2*c^2*W^2*Z^2 - (a1^2*a6*c+a4^2*c)*Z^4 );
   if debug then assert IsIrreducible(cov) and IsNonsingular(cov) and Genus(cov) eq 1; end if;
   if return_map then
      EFrob := EllipticCurve([a1^2,a2^2,a3^2,a4^2,a6^2]);
      cov_to_EFrob := map< cov -> EFrob | [c*W^2*Z, W*Y+a6*Z^3, Z^3] >;
      return cov, cov_to_EFrob;
   else
      return cov;
   end if;
end function;


// put E in the form y^2 + a1*x*y = x^3 + a2*x^2 + a6, and return a map E -> Enew
function a1a2a6form(E)
   a1,a2,a3,a4,a6 := Explode(Coefficients(E));  assert a1 ne 0;
   assert Characteristic(BaseRing(E)) eq 2;
   // translate to get rid of a3, a4
   aa2 := (a1*a2 + a3)/a1;
   aa6 := (a1^6*a6 + a1^5*a3*a4 + a1^4*a2*a3^2 + a1^4*a4^2 + a1^3*a3^3 + a3^4)/a1^6;
   Enew := EllipticCurve([a1,aa2,0,0,aa6]);
   xE := E.1/E.3; yE := E.2/E.3;
   E_to_Enew := map< E -> Enew | [ (xE-a3/a1), yE-(a1^2*a4 + a3^2)/a1^3, 1] :Check:=false>;
   return Enew, E_to_Enew;
end function;

// put E in the form y^2 + x*y = x^3 + a2*x^2 + a6, and return a map E -> Enew
function a2a6form(E)
   a1,a2,a3,a4,a6 := Explode(Coefficients(E));  assert a1 ne 0;
   assert Characteristic(BaseRing(E)) eq 2;
   // translate to get rid of a3, a4
   aa2 := (a1*a2 + a3)/a1;
   aa6 := (a1^6*a6 + a1^5*a3*a4 + a1^4*a2*a3^2 + a1^4*a4^2 + a1^3*a3^3 + a3^4)/a1^6;
   Enew := EllipticCurve([1,aa2/a1^2,0,0,aa6/a1^6]);
   xE := E.1/E.3; yE := E.2/E.3;
   E_to_Enew := map< E -> Enew | [ (xE-a3/a1)/a1^2, yE/a1^3-(a1^2*a4 + a3^2)/a1^6, 1] :Check:=false>;
   return Enew, E_to_Enew;
end function;


// Version of the intrinsic VectorSpace (for restricting scalars) that works for ModFld's over finite fields.
// Here 'k' is a subfield of BaseField(V), which must be a finite field.  
// Returned are a vector space W over k, and a map V -> W.
function VectorSpace_ModFld(V, k)  // ModFld, Fld -> ModTupFld, Map
   K := BaseField(V);
   assert ISA(Type(k),FldFin) and ISA(Type(K),FldFin);
   deg := Degree(K,k);
   W := VectorSpace(k, deg*Dimension(V));
   VtoW := map< V -> W | v :-> W! &cat[ Eltseq(c,k) : c in Eltseq(v)],
                         w :-> V! [K! [ww[i*deg+j] : j in [1..deg]] : i in [0 .. Dimension(V)-1]] 
                                 where ww is Eltseq(w) >;
   return W, VtoW;
end function;


function get_completion(list, pl)  // -> Kpl, toKpl    
// The 'list' is a list of tuples of the form [* <pl, toKpl>, ... *]
   for idx := 1 to #list do
      if IsIdentical( pl, list[idx][1]) then 
         toKpl := list[idx][2];
         return Codomain(toKpl), toKpl; end if; end for;
   Kpl, toKpl := Completion(FunctionField(pl), pl);  
   Append( ~list, <pl, toKpl>);
   return Kpl, toKpl;
end function;


// The class of f in K/Phi(K) where Phi(a)=a^2+a is the Artin-Schreier map.
// The class is represented by a sequence of GF(2) elements which when 
// padded with enough zeros yields an injective linear map K/Phi(K) -> V 
// (returned by local_Artin_Schreier_quotient below).
// This homomorphism is not canonical, in fact it depends on the choice of u 
// and of lifts r @@ res in the code below (this @@ had better be a linear map!).

function local_artin_schreier_class(f, pl, u, k, res, maxval : kabs:=0)
   n := - Valuation(f, pl);
   if n le -1 then return [GF(2)| ]; end if;
   error if n gt maxval, "Valuation of element is too negative";

   // peel off leading terms, from valuation -n to valuation 0
   ans := [GF(2)| ];
   for i := n to 0 by -1 do
      r := res( f*u^i );
      if i eq 0 then 
         // The image of the Artin-Schreier map GF(2^k) -> GF(2^k) : a :-> a^2+a 
         // equals the kernel of the trace GF(2^k) -> GF(2).
         ans := [Trace(r,GF(2))] cat ans;
      elif IsOdd(i) then
         // record the leading term (and remove it)
         if r ne 0 then f -:= (r @@ res)*u^-i; end if;
         if BaseField(k) cmpne GF(2) then r := kabs!r; end if;
         ans := Eltseq(r) cat ans;
      elif IsEven(i) and r ne 0 then
         // replace f by an equivalent element
         s := Sqrt(r);
         a := (s @@ res) * u^(-i div 2);
         f -:= a^2 + a;  // same artin schreier class
      end if; 
   end for;
   assert Valuation(f,pl) ge 0; // check that all negative powers got peeled off
   return ans;
end function;

function unpack_vector(v,k : kabs:=0)  // Vector, FldFin -> FldFinElt, [FldFinElt]
   // Break v into blocks of lengths 1, d, d, d, ...  
   // and return v[1], [k! block[1], k! block[2], ...] 
   // (omitting zeros at the end).
   d := Degree(k,GF(2));
   v := Eltseq(v);  v1 := v[1];  Remove(~v,1);
   if BaseField(k) cmpeq GF(2) then
      k_elts := [k| k! v[1+d*(j-1) .. d*j] : j in [1 .. #v div d] ];
   else
      k_elts := [k| k! kabs! v[1+d*(j-1) .. d*j] : j in [1 .. #v div d] ];
   end if;
   while not IsEmpty(k_elts) and k_elts[#k_elts] eq 0 do Prune(~k_elts); end while;
   return v1, k_elts;
end function;

function local_Artin_Schreier_quotient(K, pl, u, res, maxval)
// K=FldFun, pl=place, u=uniformizer, res = residue map K->k, 
// maxval = bound on -valuation of elements of K which the returned map should accept 
   assert Type(BaseField(BaseField(K))) eq FldFin and Characteristic(K) eq 2;
   k := Codomain(res);  
   if debug then 
      for i := 1 to Min(#k,100) do kk := Random(k); assert kk eq kk@@res@res; end for; end if;
   V := VectorSpace(GF(2), 1 + Degree(k)*Ceiling(maxval/2));
   if BaseField(k) cmpeq GF(2) then
      kabs := 0;
   else 
      kabs := ext<k|2>;
   end if;
   // find an element in k whose trace in GF(2) is 1, and lift it:
   repeat tt := Random(k); until Trace(tt,GF(2)) eq 1;
   tt := tt @@ res;
   toV := map< K -> V | f :-> class cat [0 : i in [#class+1..Dimension(V)]]
                              where class := local_artin_schreier_class(f,pl,u,k,res,maxval :kabs:=kabs),
                        v :-> v1*tt + &+[K| (coeffs[i]@@res)*u^-(2*i-1) : i in [1..#coeffs]]
                                   where v1, coeffs := unpack_vector(v,k :kabs:=kabs) >;
   return V, toV;
end function;


intrinsic TwoIsogenySelmerGroups(E::CrvEll[FldFunG]) -> GrpAb, GrpAb, Map, Map
{Given an ordinary elliptic curve E over a function field F_q(t) of even characteristic, 
this computes the Selmer groups associated to the separable isogeny E^Frob -> E and to the 
dual isogeny E -> E^Frob (induced by the Frobenius map)}
  
   if debug_level gt 0 then vprint Selmer,1: "  debug level =", debug_level; end if;

   K := BaseRing(E);
   if Type(K) eq FldFunRat then 
      K := ext< K | Polynomial([K| -1, 1]) >; E := BaseChange(E,K); end if;
   require Type(BaseField(K)) eq FldFunRat and Type(k) eq FldFin and Characteristic(k) eq 2 
                                               where k is BaseField(BaseField(K)) :
          "The base field should be (isomorphic to) a rational function field " *
          "over a finite field of characteristic 2";
   t := K! BaseField(K).1;
 
   vprint Selmer,1: 
     "\n  ************************  SEPARABLE ISOGENY STEP  **************************\n";

   origE := E;  origa1 := Coefficients(E)[1];
   minE, origE_to_minE := MinimalModel(origE);
   E, minE_to_E := a2a6form(minE);
   origE_to_E := Expand( origE_to_minE * minE_to_E);
   a1,a2,a3,a4,a6 := Explode(Coefficients(E)); assert a1 eq 1 and a3 eq 0 and a4 eq 0;
   vprint Selmer,2: "Working with 'Artin-Schreier' model of E =\n", E;
   EFrob := EllipticCurve([a1^2,a2^2,a3^2,a4^2,a6^2]);
   EE := MinimalModel(EllipticCurve([1,a2,0,a6,0])); 
   assert IsIsomorphic(EE, EFrob);  // these are both models of the isogenous curve
   // compute the dual isogeny EE -> E
   tors2, tors2_E := TwoTorsionSubgroup(EE);  assert #tors2 eq 2;
   T2 := tors2.1 @ tors2_E;
   E1, EE_E1 := IsogenyFromKernel(EE, Polynomial([BaseRing(EE)| -T2[1],1]) );
   Emin := MinimalModel(E);
   ok,E1_Emin := IsIsomorphic(E1, Emin);  assert ok;
  
             /***********    GLOBAL COMPUTATIONS    ************/

   // TO DO: still should think more about how to organise the bad places.
   //        For the separable step, only need BadPlaces(E) but for the 
   //        Frobenius step, maybe need the other stuff to be safe. 
   //        Note that we compute local points in this step and use them in the 
   //        Frobenius step ... definitely ought to delay the local points till needed.
   badplaces := BadPlaces(E) cat BadPlaces(minE) cat Poles(t) cat Zeroes(origa1);
   badplaces := Setseq(Seqset(badplaces));  // get nonsense if there are repetitions
   // Sort by degree, with (1/t) last among the degree 1 places ...
   sorting_order := func< pl | Degree(pl) + (IsFinite(pl) select 0 else 1/2) >;  
   Sort( ~badplaces, func<pl1,pl2 | sorting_order(pl1)-sorting_order(pl2)> );
 ASbadplaces := badplaces;
   locinfoE := [LocalInformation(E,pl) : pl in badplaces];
   
   // Kramer Prop. 2.5: non-split multiplicative places at which the discriminant 
   // has even valuation behave like good primes.  At other multiplicative places,
   // the local condition is the zero subgroup of the Artin-Schreier quotient.
   // TO DO: use this (for the moment, just check it)
   additive_places := [];
   good_mult_places := [];
   other_mult_places := [];
   for i := 1 to #badplaces do 
      tup := locinfoE[i];
      if ReductionType(tup[5]) ne "Multiplicative" then 
         Append(~additive_places, badplaces[i]);
      elif IsZero(tup[2]) or IsEven(tup[2]) and not tup[6] then
         Append(~good_mult_places, badplaces[i]);
      else 
         Append(~other_mult_places, badplaces[i]);
      end if; 
   end for;
   vprintf Selmer: "Bad places are %o\n", badplaces;
   vprintf Selmer: "Additive places are %o\n", additive_places;

   badnesses := [Max([ 0, -Valuation(a2,pl), Ceiling(-Valuation(a6,pl)/3) ]) : pl in additive_places];
   DK := DivisorGroup(K);
   bad_divisor := &+[DK| badnesses[i]*additive_places[i] : i in [1..#additive_places]];
   half_bad_divisor := &+[DK| Floor(badnesses[i]/2)*additive_places[i] : i in [1..#additive_places]];
   RR, RRtoK := RiemannRochSpace(bad_divisor);
   RR1, RR1toK := RiemannRochSpace(half_bad_divisor);
   if true or BaseField(RR) ne GF(2) then 
      RR, restrict_scalars := VectorSpace_ModFld(RR, GF(2));  // make the basefield GF(2)
      RRtoK := Inverse(restrict_scalars) * RRtoK;
      RR1, restrict_scalars1 := VectorSpace_ModFld(RR1, GF(2)); 
      RR1toK := Inverse(restrict_scalars1) * RR1toK;
   end if;
   RR1_ArtinSchreier_image_in_RR := 
       sub< RR | [(a^2+a) @@ RRtoK where a := RR1toK(b) : b in Basis(RR1)] >;
   V, RRtoV := RR / RR1_ArtinSchreier_image_in_RR;
   VtoK := Inverse(RRtoV) * RRtoK;

             /***********    LOCAL COMPUTATIONS    ************/

   TE,TEmap := TorsionSubgroup(E);
   TEFrob,TEFrobmap := TorsionSubgroup(EFrob);
   tE := Valuation(#TE,2);
   tEFrob := Valuation(#TEFrob,2);
   Selrank_lower_bound := tE - tEFrob + 1;  
   if debug then 
      assert #TE eq #DivisionPoints(E!0, 2*#TE);
      assert #TEFrob eq #DivisionPoints(EFrob!0, 2*#TEFrob); end if;
   error if tE gt 0  and 2^(tE-1)*TE.1@TEmap eq E!0
       or tEFrob gt 0 and 2^(tEFrob-1)*TEFrob.1@TEFrobmap eq EFrob!0 
       or Selrank_lower_bound lt 0,
       "There is a bug in TorsionSubgroup. \n" * 
       "PLEASE SEND THIS CURVE TO magma-bugs@maths.usyd.edu.au";

   // TO DO: Inefficient to call FormalGroup here, get the coeffs directly instead.
   coeffEE_E1 := Coefficients(FormalGroupHomomorphism(EE_E1, 5))[1]; 
   coeffE1_Emin := Coefficients(FormalGroupHomomorphism(E1_Emin, 5))[1];

   W := V; 
   vprint Selmer,1: "Initial upper bound on Selmer rank is", Dimension(W);
   error if Dimension(W) lt Selrank_lower_bound, 
        "Obtained contradictory bounds on the rank of the Selmer group";
   ASbases := [* *];
   completion_maps := [* *];
   for pl in badplaces do 
     if not debug and Dimension(W) eq Selrank_lower_bound then 
        vprint Selmer,1: "Selmer group is generated by 2-torsion on E \n" *
                         " (could skip local conditions at the remaining bad places)"; 
      //                 " (skipping local conditions at the remaining bad places)"; 
      //break;
      // TO DO: if we break here we have to set up a mechanism to fill in ASbases later
      //        (if they are needed in the Frobenius isogeny step)
     end if;
     vprint Selmer,1: "Applying local condition at", pl;
     Kpl, toKpl := Completion(K,pl : Precision:=50);  
     Append( ~completion_maps, <pl, toKpl>); // avoid repeated creation of these maps
     deg := Degree(pl);
     k, res := ResidueClassField(Ideal(pl));
     
     // What is dimension of E(Kv)/im(EE(Kv)) ??
     //   formal group quotient: order 2^(valuation of leading formal group coeff)
     //   2-torsion: contributes 2
     //   multiply this by component group ratio: (E/E0) / (EE/EE0)

     locdataE, Eminpl := LocalInformation(E, pl);
     locdataEE, EEminpl := LocalInformation(EE, pl);
     if IsFinite(pl) then
        val_formal := Valuation( coeffEE_E1, pl) + Valuation( coeffE1_Emin, pl);
     else
        // adjust for the fact that we weren't using minimal models at pl
        _, Emin_to_Eminpl := IsIsomorphic(Emin, Eminpl);
        _, EEmin_to_EEminpl := IsIsomorphic(EE, EEminpl); // EE was a minimal model
        val_transE := Valuation( Coefficients(DefiningEquations(Emin_to_Eminpl)[1])[1], pl);
        assert IsEven(val_transE);  val_transE div:= 2;
        val_transEE := Valuation( Coefficients(DefiningEquations(EEmin_to_EEminpl)[1])[1], pl);
        assert IsEven(val_transEE);  val_transEE div:= 2;
        val_formal := Valuation( coeffEE_E1, pl) + Valuation( coeffE1_Emin, pl)
                        - val_transE + val_transEE;
     end if;
     assert val_formal eq 0 or Valuation(a2,pl) lt 0 or Valuation(a6,pl) lt 0;
     dim_formal := Degree(k) * val_formal;  

     vprint Selmer,2: " Rank of quotient of formal groups =", dim_formal;
     error if dim_formal lt 0, "should dim_formal be negative ???";
     _,vE,_,cE,kodE,splitE := Explode(locdataE); 
     _,vEE,_,cEE,kodEE,splitEE := Explode(locdataEE); 
     assert splitE eq splitEE; 
     dim := dim_formal + 1 + Valuation(cE,2) - Valuation(cEE,2); 
     vprint Selmer,1: " Local Mordell-Weil group should have dimension", dim;  
     assert dim ge 0;
     
           /*********   FIND LOCAL POINTS at the place pl   *********/

     maxval := 1 + Max([0] cat [ -Valuation(aa,pl) : aa in [a2,a4,a6]]);
     u := UniformizingElement(pl);
     Vpl, toVpl := local_Artin_Schreier_quotient(K, pl, u, res, 10*maxval );
     localpts := sub< Vpl | >;
     counter := 0;  safety_counter := 0;
     while Dimension(localpts) lt dim or 
           debug and safety_counter lt Max(IsFinite(pl) select 1000 else 100, Min(10000,3/4*counter) ) do 
        counter +:= 1;
        if counter eq 3000*dim and safety_counter eq 0 then
           printf "WARNING: Taking a long time to find local points at %o\n" *
                  "        (expecting dimension %o and currently have dimension %o)\n", 
                                                  pl, dim, Dimension(localpts); end if;
        if Dimension(localpts) ge dim then safety_counter +:= 1; end if;
        val := Random( Min(maxval, Floor(1+counter/30)) );
        ww := u^Random([-val..4]) * &+[ (Random(k) @@ res)*u^i : i in [0..8]];
        if ww eq 0 then continue; end if;
        ff := ww + a2 + a4/ww + a6/ww^2;
        if Valuation(ff,pl) lt -10*maxval then continue; end if; // because image won't fit in Vpl
        
        if debug_level ge 3 then  // intensive checking of artin-schreier classes
           for xx in [ww+a2,ff] do 
            xxx := xx @toVpl @@toVpl;  assert (xx @toVpl) eq (xxx @toVpl); 
            if Valuation(xx,pl) le -50 then continue; end if;
            assert not IsIrreducible(Polynomial([Kpl| (xx-xxx)@toKpl,1,1]));
            assert IsIrreducible(Polynomial([Kpl| xx@toKpl,1,1])) eq ((xx @toVpl) ne 0);
           end for;
        end if;

        if IsZero(ff @ toVpl) then 
           if debug then assert toVpl(ww+a2) eq toVpl(a6/ww^2); end if;
           Include( ~localpts, toVpl(ww+a2), ~new_pt);
           if new_pt then vprint Selmer,2: "  ... now up to dimension", Dimension(localpts); end if;
        end if;
     end while;
     if Dimension(localpts) ne 0 then 
        vprintf Selmer,1: "  ... found points after %o tries\n", counter - safety_counter;
        vprint Selmer,2: Basis(localpts); end if;
     assert Dimension(localpts) eq dim; 
     Append( ~ASbases, [bb @@ toVpl : bb in Basis(localpts)] );

  // Check our results agree with the Kramer lemma
  if pl in good_mult_places then assert localpts eq sub< Vpl | Vpl.1 >;
  elif pl in other_mult_places then assert Dimension(localpts) eq 0; 
  end if;
   
     // Apply the local condition at the place pl:
     WtoVpl := hom< W -> Vpl | [ w @ VtoK @ toVpl : w in Basis(W)] >; 
     // ??? Is this not legal:  
     // Quot, Vpl_mod_localpts := quo< Vpl | localpts >;
     Quot, Vpl_mod_localpts := quo< Vpl | Basis(localpts) >;

     // Work-around for W := Kernel( WtoVpl * Vpl_mod_localpts );
     W := Kernel( hom< W -> Quot | [w @ WtoVpl @ Vpl_mod_localpts : w in Basis(W)]> );
     vprint Selmer,1: "==> Upper bound on Selmer rank is now", Dimension(W);
     error if Dimension(W) lt Selrank_lower_bound, 
          "Obtained contradictory bounds on the rank of the Selmer group";
   end for;  // pl in badplacesE 
   
   Sel_AS := AbelianGroup([2 : i in [1..Dimension(W)]]); 
   Sel_AS_map := map< Sel_AS -> K | s :-> (&+[W| ss[i]*W.i : i in [1..Ngens(Sel_AS)]]) @ VtoK
                                                where ss is Eltseq(s) >;

   vprint Selmer,1: 
     "\n  ************************  FROBENIUS ISOGENY STEP  **************************\n";

   E, minE_to_E := a1a2a6form(minE);  // maybe this is simpler to work with 
   origE_to_E := Expand( origE_to_minE * minE_to_E);
   a1,a2,a3,a4,a6 := Explode(Coefficients(E));  assert a3 eq 0 and a4 eq 0;
   assert &and[ pl in badplaces : pl in BadPlaces(E)];

   finitebadplaces := [pl : pl in badplaces | IsFinite(pl)];
   V := VectorSpace(GF(2), #finitebadplaces);
   VtoK_basis_images := [UniformizingElement(pl) : pl in finitebadplaces];
   VtoK := map< V -> K | v :-> &*[K| VtoK_basis_images[i]^vv[i] : i in [1..#vv]] 
                               where vv := ChangeUniverse(Eltseq(v), Integers()) >;

   if debug then for pl in finitebadplaces do 
      assert ideal<MaximalOrderFinite(K)| UniformizingElement(pl)> eq Ideal(pl); end for; end if;
   easybadplaces := [pl : pl in badplaces | Degree(pl) le 8];
   if debug_level ge 2 then   // test two_covering (in the trivial case)
      for c in [Random([K| 1, t^2, t^2+1, 1+1/t^2, t^2+1+1/t^2])] do 
       C2, C2toEE := two_covering(E, c : return_map);
       for pl in easybadplaces do 
        _,toKpl := get_completion(completion_maps, pl);
        assert IsLocallySolvable(C2, pl : completion_map:=toKpl); end for; end for; end if;

   // Apply local conditions
   W := V;
   for pl in badplaces do
      Kpl, toKpl := get_completion(completion_maps, pl);
      vprintf Selmer: "Applying local condition at %o\n", pl;

      // New method, using Artin-Schreier pairing:
      ASB := ASbases[idx] where idx is Index(ASbadplaces, pl);  
      VV := VectorSpace(GF(2), #ASB);
      Wbasis := [w @ VtoK : w in Basis(W)];
      pairing_map := hom< W->VV | [VV! [ArtinSchreierSymbol( asb@toKpl, w@toKpl) : asb in ASB] 
                                  : w in Wbasis] >;
      if debug_level ge 2 then  // check if Brauer-Severi's are locally solvable
         Pr2<X,Y,Z> := ProjectiveSpace(K,2); 
         for asb in ASB do for w in Wbasis do 
           symb := ArtinSchreierSymbol( asb@toKpl, w@toKpl);
           BS := Curve(Pr2, X^2 + X*Y + asb*Y^2 + w*Z^2);
           assert IsLocallySolvable(BS, pl : completion_map:=toKpl) eq (symb eq 0); 
         end for; end for;
      end if;
      W1 := Kernel(pairing_map);

      if debug then   // Old method (test local solubility of coverings)
         is_locally_trivial := map<V -> {true,false} |
                                   v :-> IsLocallySolvable( two_covering(E,v@VtoK), pl 
                                                               : completion_map:=toKpl ) >;
         assert W1 eq FindSubspace(W, is_locally_trivial);
      end if;

      W := W1;
      vprint Selmer: "==> Upper bound on Selmer rank is now", Dimension(W);
   end for;
   
   if debug_level ge 2 then 
      // Random testing
      for i := 1 to Dimension(W) do 
       repeat v := Random(W); until v ne 0;
       for pl in easybadplaces do 
        _,toKpl := get_completion(completion_maps, pl);
        assert IsLocallySolvable( two_covering(E,v@VtoK), pl : completion_map:=toKpl); 
      end for; end for;
      if #easybadplaces eq #badplaces then
      for i := 1 to Dimension(V) do v := Random(V); if v in W then continue; end if; 
       assert not &and[ IsLocallySolvable( two_covering(E, v@VtoK), pl : completion_map:=toKpl)
                           where _,toKpl := get_completion(completion_maps, pl)
                       : pl in badplaces]; end for; end if;
   end if;

   Sel_Frob := AbelianGroup([2 : i in [1..Dimension(W)]]); 
   Sel_Frob_map := map< Sel_Frob -> K | s :-> (&+[W| ss[i]*W.i : i in [1..Ngens(Sel_Frob)]]) @ VtoK
                                                where ss is Eltseq(s) >;
   return Sel_AS, Sel_Frob, Sel_AS_map, Sel_Frob_map;
end intrinsic;


intrinsic ReductionType(symbol::SymKod) -> MonStgElt
{Return "Good", "Multiplicative" or "Additive"}
   if symbol eq KodairaSymbol("I0") then 
      return "Good";
   elif symbol in {KodairaSymbol(s) : s in {"II","II*","III","III*","IV","IV*","I0*"}} then
      return "Additive";
   end if;
   n := 1;
   while true do
      if symbol eq KodairaSymbol("I" cat IntegerToString(n)) then
         return "Multiplicative";
      elif symbol eq KodairaSymbol("I" cat IntegerToString(n) cat "*") then
         return "Additive";
      end if;
      n +:= 1;
   end while;
end intrinsic;
 

intrinsic ArtinSchreierSymbol(a::RngElt, b::RngElt) -> RngIntElt
{The local symbol [a,b), where a and b are elements of a local ring
 (which must be a series ring over a finite field).
 The symbol takes values in Z/pZ where p is the characteristic.
 The symbol is 0 iff b is a norm from the Artin-Schreier extension given by x^p-x+a.}

   // The algorithm comes from Serre's 'Local Fields'. Here's what JP has to say:
   // For a,b in K = k((t)) where k is finite, one has
   //    [a,b) = [c,t) 
   // where c in k is the residue of the differential a*db/b,
   // and [c,t) is 1 <==> c = x^p-x for some x in k
   //                <==> Tr(c) = 0, where the trace is wrt k/F_p.
   
   K := Parent(a);
   p := Characteristic(K);
   if not Parent(b) eq K then 
      bool, b := IsCoercible(K,b);
      require bool: "The arguments must belong to the same local ring";
   end if;
   require ISA(Type(K),RngSer) : "The arguments must belong to a series ring";
   require Characteristic(K) gt 0: 
          "The arguments should be in a ring of positive characteristic";
   require Type(BaseRing(K)) eq FldFin: 
          "The arguments must belong to a series ring over a finite field";

   if not IsField(K) then 
      K := FieldOfFractions(K);
      a := K!a;  b := K!b;
   end if;

   // TO DO: reduce precision before doing the multiplications, since we only want one coefficient
   c := Coefficient( a*Derivative(b)/b, -1);
   return Integers()! Trace(c, GF(p));
end intrinsic;

/*
// We DON'T want this one as it will encourage repeated creation 
// of completions and completion maps, which is bad.
intrinsic ArtinSchreierSymbol(a::FldFunGElt, b::FldFunGElt, pl::Any) -> RngIntElt
{The local symbol [a,b) at the place pl, where a and b are elements of a function field
 (with finite base field).  The symbol takes values in Z/pZ where p is the characteristic.
 The symbol is 0 iff b is norm from the local Artin-Schreier extension given by x^p-x+a.}
 
   K := Parent(a);
   if not Parent(b) eq K then
      bool, b := IsCoercible(K,b);
      require bool: "The arguments must belong to the same ring";
   end if;
   require Characteristic(K) gt 0: "The arguments should be in a ring of positive characteristic";

   if Type(K) eq FldFunRat then  
      bool, pl := IsCoercible(pl, K);
      require bool: 
        "The third argument 'pl' should be an irreducible polynomial in the function field variable";
      K := ext< K | Polynomial([K| -1,1]) >;
      a := K!a;  b := K!b;
      pl := Zeros(K!pl)[1];
   elif Type(pl) ne Map then 
      require Type(pl) eq PlcFunElt : "The argument pl should be a function field place";
   end if;

   Kpl, toKpl := Completion(K, pl);
   ans := ArtinSchreierSymbol( a@toKpl, b@toKpl);

   return ans;
end intrinsic;
*/

/***************************************************************************************/

// Copied with slight change from the GF(3) case in 3selmer.m
// TO DO: Use quotients not sets to keep track of the known info

function FindSubspace(V, pred)
  // Given a GF(2)-vector space V and some predicate pred on V such that
  // the subset of elements satisfying pred is a subspace, find this subspace.

  // Divide the underlying set of V into three subsets:
  // - the elements known to satisfy pred
  // - the elements known not to satisfy pred
  // - the rest
  assert BaseRing(V) eq GF(2);
  vprintf Selmer, 3: "  FindSubspace, dim(V) = %o\n", Dimension(V);
  Syes := { V!0 };
  basis := [ V | ]; // a basis of Syes
  Sno := { V | };
  Srest := { V | v : v in V | v ne V!0 };
  while not IsEmpty(Srest) do
     // take some element of Srest and check if it satisfies pred
     vprintf Selmer, 3: "   #Syes = %o, #Sno = %o, #Srest = %o\n", #Syes, #Sno, #Srest;
  
     v := Random(Srest);
     vprintf Selmer, 3: "   Chose random element %o\n", v;
     if pred(v) then
        // found a new basis element
        vprintf Selmer, 3: "    v is in subspace\n";
        Append(~basis, v);
        Syesnew := { w+v : w in Syes };
        Syes join:= Syesnew;
        Snonew := { v1+v2 : v1 in Sno, v2 in Syesnew };
        Sno join:= Snonew;
        Srest diff:= Syesnew;
        Srest diff:= Snonew;
     else
        // can eliminate v and -v
        vprintf Selmer, 3: "    v is not in subspace\n";
        S0 := {v};
        Snonew := { v1+v2 : v1 in Syes, v2 in S0 };
        Sno join:= Snonew;
        Srest diff:= Snonew;
     end if;
  end while;
  vprintf Selmer, 3: "  Subspace has dimension %o\n", #basis;
  return sub< V | basis >;
  end function;
