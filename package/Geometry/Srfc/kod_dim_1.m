freeze;

///// Minimal models and elliptic fibrations for ////////////////
////        Kodaira dimension 1 surfaces             ////////////
////////////////  mch 11/2012 ///////////////////////////////////

import "kod_enr.m":h0;

function smallest_big_nK(K,d)

// finds the smallest n >= 2 s.t. n*K (K = inv sheaf)
// has h0(n*K) >= d. Returns n, n*K,n,h0(n*K)

    SaturateSheaf(~K);
    n := 2;
    Kn := TensorPower(K,2);
    h := h0(Kn); 
    if h lt d then
      repeat   
	n +:= 1;
	Kn := TensorProduct(Kn,K : Maximize := true);
	if &and[w gt 0 : w in ColumnWeights(FullModule(Kn))] then
	  continue;
	end if;
	h := h0(Kn);
      until h ge d;
    end if;

    return Kn,n,h;
    
end function;

/*
function minimise_by_adj(X)

    mp := 0;
    bmin := false;
    Y := X;
    K := CanonicalSheaf(Y);
    SaturateSheaf(~K);
    K2 := IntersectionPairing(K,K); 
    while K2 lt 0 do
      mp1,Y := DivisorMap(Twist(K,1)); //adjunction map
      mp1 := Restriction(mp1,Domain(mp1),Y);
      mp := (Type(mp) eq RngIntElt) select mp1 else Expand(mp*mp1);
      K := CanonicalSheaf(Y);
      K2 := IntersectionPairing(K,K);
    end while;
    if Type(mp) eq RngIntElt then 
      mp := IdentityMap(Y); bmin := true;
    end if;
    return Y,mp,K,bmin;

end function;
*/

function minimise_by_adj(X,bUseEff)

    mp := 0;
    bmin := false;
    bDiv := false;
    Y := X;
    K := CanonicalSheaf(Y);
    SaturateSheaf(~K);
    K2 := IntersectionPairing(K,K);
    if K2 lt 0 then
     // if K is effective, it can be quicker to work with a canonical
     // divisor and compute the new K and K2 by taking the image of D in |K|
     // under the adjunction map and removing the point images of blowdowns
     // of exceptional lines. The image of D and new K2 are quick to
     // compute. However, if we have to go further than one adjunction map,
     // it seems to be no quicker to compute the new K from the new D than
     // to compute it directly. It can be a big time saver for the
     // final adjunction map, though, if the final K is not needed to
     // compute an elliptic fibration map.
     if bUseEff and (h0(K) gt 0) then
	KD := SheafToDivisor(K);
	ID := KD`ideal;
	bDiv := true;
     end if; 
     while K2 lt 0 do
      mp1,Y := DivisorMap(Twist(K,1) : graphmap := true); //adjunction map
      mp1 := Restriction(mp1,Domain(mp1),Y);
      mp := (Type(mp) eq RngIntElt) select mp1 else Expand(mp*mp1);
      if bDiv then
	D1 := Image(Restriction(mp1,Scheme(Domain(mp1),ID),Y));
	Saturate(~D1);
	ID := EquidimensionalPart(Ideal(D1));
	delete D1;
	K2 := -(Integers()!Coefficient(HilbertPolynomial(ID),0));
	if K2 eq 0 then break; end if;
	K := DivisorToSheaf(Y,ID);
	Y`KX := K;
      else
	K := CanonicalSheaf(Y);
	K2 := IntersectionPairing(K,K);
      end if;
     end while;
    end if;
    if Type(mp) eq RngIntElt then 
      mp := IdentityMap(Y); bmin := true;
    end if;
    return Y,mp,bmin;

end function;

intrinsic MinimalModelKodairaDimensionOne(X::Srfc : CheckSing := false, Fibration := false)
		-> Map, Map
{ Computes and returns a birational map to a minimal model Y for
 non-singular ordinary projective surface X of Kodaira dimension one.
 If parameter Fibration is true (the default is false), also returns a fibration map from
 Y to a smooth curve C that presents Y as a (minimal) elliptic fibration over C. }

    if (not Fibration) and (assigned X`min_map) then return X`min_map; end if;
    if Fibration and (assigned X`min_map) then
	Y := Codomain(X`min_map);
	if assigned Y`fibre_map then
	  return X`min_map, Y`fibre_map;
	end if;
    end if;
    require IsOrdinaryProjective(X):
	"Argument X should be a surface in ordinary projective space";
    if CheckSing then
	require IsNonsingular(X):
		"Surface argument X should be non-singular";
    end if;

    bDone := false;
    if not Fibration then
	Y,mp := minimise_by_adj(X,true);
	X`min_map := mp;
    else
	if assigned X`min_map then
	  mp := X`min_map; Y := Codomain(mp); bDone := true;
	else	   
	  Y,mp := minimise_by_adj(X,false);
	  X`min_map := mp;
	end if;
    end if;
    if not (bDone or IsIdentical(X,Y)) then
	Y`K2 := 0; Y`K2m := 0;
	Y`kod_dim := 1; Y`min_map := IdentityMap(Y);
	if assigned X`pg then Y`pg := X`pg; end if;
	if assigned X`q then Y`q := X`pg; end if;
	if not assigned Y`Nonsingular then Y`Nonsingular := true; end if;
    end if;
    if not Fibration then
	return X`min_map;
    end if;

    if assigned Y`pg then
	pg := Y`pg;
    elif assigned X`pg then
	pg := X`pg; Y`pg := pg;
    else
	pg := h0(CanonicalSheaf(X)); X`pg := pg; Y`pg := pg;
    end if;
    if assigned Y`q then
	q := Y`q; chi := 1+pg-q;
	if not assigned X`q then X`q := q; end if;
    elif assigned X`q then
	q :=X`q; chi := 1+pg-q;
	Y`q := X`q;
    else
	chi := ArithmeticGenus(Y)+1;
	q := 1+pg-chi;
	Y`q := q; X`q := q;
    end if;
    //n,KYn,pg := smallest_big_nK(KY);
    KY := CanonicalSheaf(Y);
    SaturateSheaf(~KY);

    if q eq 0 then
	// C is genus 0 (with chi > 0) - need smallest multiple nKY of
	// KY with glob sections of dim >= 2 - will be for n =
	// 1,2,3,4 or 6
	if pg ge 2 then
	  K := KY;
	else
	  K := TensorPower(KY,2); //ok for pg = 1
	  if pg eq 0 then
	    if h0(K) lt 2 then
	      K1 := TensorProduct(K,KY : Maximize := true);
	      if h0(K1) lt 2 then
		K2 := TensorPower(K,2);
		if h0(K2) lt 2 then
		  K := TensorPower(K1,2);
		  assert h0(K) ge 2;
		else
		  K := K2;
		end if;
	      else
		K := K1;
	      end if;
	    end if;
	  end if;
	end if;
	mpC,C := DivisorMap(K);
	assert ArithmeticGenus(C) eq 0;
    elif chi gt 0 then
	// C of genus q > 0
	if q eq 1 then
	  // C is genus 1
	  if chi ge 3 then
	    K := KY;
	  else
	    K := TensorPower(KY,2);
	    if (chi eq 1) and (h0(K) lt 3) then
		K := TensorProduct(K,KY : Maximize := true);
	    end if;
	  end if;
	  mpC,C := DivisorMap(K);
	  assert (Dimension(Ambient(C)) ge 2) and 
			(ArithmeticGenus(C) eq 1);
	else // q>= 2
	  // here the divisor map of KY is onto a birational image
	  // of C unless C is hyperelliptic and chi <= 2 when the
	  // image may be non-sing rational. If image isn't IM to C
	  // then 2KY works in all cases.
	  if q+chi eq 3 then
	    C := ProjectiveSpace(BaseRing(X),1);
	  else
	    mpC,C := DivisorMap(KY);
	  end if;
	  if ArithmeticGenus(C) ne q then
	    KY2 := TensorPower(KY,2);
	    mpC,C := DivisorMap(KY2);
	    assert ArithmeticGenus(C) eq q;
	  end if;
	end if; 
    else //trickier chi = 0 case
	// q = pg+1, KX=f*(KC tensor L(D)) tensor (mult fibre bit) 
	// where f:X->C and D is a degree 0 divisor on C. If
	// if D ~ 0 then q = g(C) else q=g(C)+1
	if pg ge 2 then //g(C) >= 2 - 2*KX always works
	  K := TensorPower(KY,2);
	elif pg eq 1 then
	  //g(C) = 2, when n*KY works - n >= 2, or g(C)=1 when smallest 
	  // multiple of n*KY with h0(n*KY) ge 3 [n <= 6, here] works
	  n,K := smallest_big_nK(KY,3);
	  assert n le 6;
	else //pg=0
	  //most annoying case - g(C) = 0 or 1. If g(C)=1, need smallest
	  // mult of n*Ky with h0(n*KY)>=3 - again holds with n >= 6.
	  // however, if g(C)=0, in the worst case we need to go to
	  // n=42 to get h0(n*KY)>=2
	  n,K,h := smallest_big_nK(KY,1);
	  assert (n le 6) and (n ne 5);
	  if n eq 6 then //g(C) = 0 case
	    assert h eq 1;
	    n,K,h := smallest_big_nK(K,2);
	    assert (n in \[2,3,4,7]) and (h eq 2);
	  elif n eq 4 then //g(C)=0 case
	    assert h eq 1;
	    n,K,h := smallest_big_nK(K,2);
	    assert (n le 5) and (h eq 2);
	  elif n eq 3 then //g(C)=0 case
	    assert h eq 1;
	    n,K,h := smallest_big_nK(K,2);
	    assert (n le 4) and (h eq 2);
	  else //n=2, G(C) 0 or 1
	    if h eq 2 then
		K1 := TensorProduct(K,KY : Maximize := true);
		h1 := h0(K1);
		//h1 <= 1 => g(C)=0 and can use K
		if h1 ge 3 then
		  K := K1;
		elif h1 eq 2 then //n =4 fine for h >= 3
		  K := TensorPower(K,2);
		end if;
	    else
	    // h=1, g(C)=0 or 1. Try up to n=6 to get new
	    // h >= 3. If this fails, g(C)=0 and n=6 will do
		K1 := K; r := 2;
		while r lt 6 do
		  r +:= 1;
		  K1 := TensorProduct(K,KY : Maximize := true);
		  h1 := h0(K1);
		  if h1 ge 3 then break; end if;
		end while;
		assert h1 ge 2;
		K := K1;
	    end if;		  
	  end if;
	end if;
	mpC,C := DivisorMap(K);
	assert (ag eq pg) or (ag eq pg+1) where ag is ArithmeticGenus(C);
    end if;

    mpC := Restriction(mpC,Y,C);
    Y`fibre_map := mpC;
    return mp,mpC;

end intrinsic;
