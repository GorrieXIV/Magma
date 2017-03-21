freeze;
///////////////////////////////////////////////////////////////////
//  Intrinsics for Automorphisms of Small Modular Curves         //
//                                                               //
//             mch - 08/2011                                     //
///////////////////////////////////////////////////////////////////

/*
2-part group types (not 1 or C2)
1 - S3 - <a,b|a^2, b^2, (a*b)^3> - #6
2 - D8 - <a,b|a^2, b^2, (a*b)^4> - #8
3 - S4 - <a,b|a^2, b^4, (a*b)^3> - #24
4 - C4 wr C2 - <a,b|a^2, b^4, (a*b)^2 = (b*a)^2> - Syl(G2,2) - #32
5 - G1 - <a,b|a^2, b^4, (a*b)^4, a*b^2*a*b = b*a*b^2*a> - #32
6 - G2 - <a,b|a^2, b^8, (a*b)^3, a*b^4*a*b*a*b^4*a*b^3, (a*b^2)^2*(a*b^6)^2> - #96
7 - G3 - <a,b|a^2, b^8, (a*b)^4, a*b^2*a*b*a*b^6*a*b^3, b*a*b^4*a = a*b^4*a*b> - #128
8 - G4 - <a,b|a^2, b^8, a*b*a*b*a*b^3*a*b^3, b*a*b^2*a = a*b^2*a*b> - #128
9 - C8 wr C2 - <a,b|a^2, b^8, a*b*a*b = b*a*b*a> - #128
*/

rels2 := [ 
  [ [<1,2>], [<2,2>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,1>] ], //S3
  [ [<1,2>], [<2,2>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,1>] ], //D8
  [ [<1,2>], [<2,4>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,1>] ], //S4
  [ [<1,2>], [<2,4>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,-1>,<1,1>,<2,-1>] ], //C4wrC2
  [ [<1,2>], [<2,4>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,1>],
	[<1,1>,<2,2>,<1,1>,<2,1>,<1,1>,<2,-2>,<1,1>,<2,-1>] ], //G1
  [ [<1,2>], [<2,8>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,1>],
	[<1,1>,<2,4>,<1,1>,<2,1>,<1,1>,<2,4>,<1,1>,<2,3>],
	[<1,1>,<2,2>,<1,1>,<2,2>,<1,1>,<2,-2>,<1,1>,<2,-2>] ], //G2
  [ [<1,2>], [<2,8>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,1>],
	[<1,1>,<2,2>,<1,1>,<2,1>,<1,1>,<2,-2>,<1,1>,<2,3>],
	[<1,1>,<2,4>,<1,1>,<2,1>,<1,1>,<2,4>,<1,1>,<2,-1>] ], //G3
  [ [<1,2>], [<2,8>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,3>,<1,1>,<2,3>],
	[<1,1>,<2,2>,<1,1>,<2,1>,<1,1>,<2,-2>,<1,1>,<2,-1>] ], //G4
  [ [<1,2>], [<2,8>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,-1>,<1,1>,<2,-1>] ] //C8wrC2
];

perms2 := [
  [[2,1,3], [1,3,2]], //S3
  [[1,3,2,4], [2,1,4,3]], //D8
  [[4,2,3,1], [2,3,4,1]], //S4
  [[2,1,5,7,3,8,4,6], [1,4,3,5,6,2,7,8]], //C4wrC2
  [[1,3,2,5,4,6,7,8],[2,4,5,6,7,1,8,3]], //G1
  [[1,3,2,4,7,9,5,11,6,10,8,12], [2,4,5,6,8,10,1,9,3,11,12,7]], //G2
  [[2,1,4,3,7,9,5,11,6,13,8,14,10,12,16,15],
	[1,3,5,6,8,10,7,12,2,11,4,13,15,14,9,16]], //G3
  [[2,1,4,3,7,9,5,10,6,8,14,15,16,11,12,13], 
	[1,3,5,6,8,4,7,11,12,13,9,16,10,14,15,2]], //G4
  [[2,1,4,3,6,5,8,7,10,9,12,11,14,13,16,15],
	[1,3,5,4,7,6,9,8,11,10,13,12,15,14,2,16]]  //C8wrC2
];

auts2 := [ [],[], //S3,D8
  [[4,3,2,1]], //S4
  [[1,2,3,6,5,4,8,7]], //C4wrC2
  [[6,4,5,2,3,1,8,7]], //G1
  [[12,2,3,10,9,7,6,8,5,4,11,1], [10,2,3,12,5,6,7,8,9,1,11,4], 
	[1,7,5,12,3,11,2,9,8,10,6,4]], //G2
  [[1,2,8,11,15,10,16,3,13,6,4,12,9,14,5,7], [16,15,8,11,2,4,1,13,3,6,10,5,9,7,12,14], 
	[7,5,3,4,2,11,1,9,8,10,6,15,13,16,12,14]], //G3
  [[1,2,8,10,12,13,15,3,16,4,11,5,6,14,7,9], [15,12,8,10,2,13,1,9,16,6,5,11,4,7,14,3],
	[7,5,3,4,2,6,1,16,9,13,12,11,10,15,14,8]], //G4
  [[1,2,7,8,13,14,3,4,9,10,15,16,5,6,11,12], [1,2,11,12,5,6,15,16,9,10,3,4,13,14,7,8],
	[4,3,2,1,15,16,13,14,11,12,9,10,7,8,5,6]]  //C8wrC2
];


/*
3-part group types (not 1 or C2)
1 - A4 - <a,b|a^2, b^3, (a*b)^3> - #12
2 - C3 wr C2 - <a,b|a^2, b^3, (a*b)^2 = (b*a)^2> - #18
3 - S4 - <a,b|a^3, b^4, (a*b*a)^2> - #24 [only used for N = 63!]
*/

rels3 := [
  [ [<1,2>], [<2,3>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,1>] ], //A4
  [ [<1,2>], [<2,3>], [<1,1>,<2,1>,<1,1>,<2,1>,<1,1>,<2,-1>,<1,1>,<2,-1>] ], //C3wrC2
  [ [<1,3>], [<2,4>], [<1,1>,<2,1>,<1,-1>,<2,1>,<1,1>] ] //S4
];

perms3 := [
  [[2,1,4,3], [1,3,4,2]], //A4
  [[4,5,6,1,2,3], [2,3,1,4,5,6]], //C3wrC2
  [[1,3,4,2],[2,3,4,1]] //S4
];

auts3 := [ [1,2,4,3], [1,3,2,4,6,5] ]; //A4,C3wrC2

import "../Crv/gen_crv_auto_gp.m": gen_seq, find_inverses;
import "../Crv/curve_autisos.m": add_ff_rat_map_data, 
add_extra_attributes, coerce_to_ff, ReduceMapDegree, grpAutCrvEltRec;

function is_primitive_nth_rt_of_1(z,n)
// checks that z (which should lie in a characteristic 0 field) is a primitive
// nth root-of-1
    if z^n ne 1 then return false; end if;
    fact := Factorisation(n);
    ps := [f[1] : f in fact];
    for p in ps do
      if z^(n div p) eq 1 then return false; end if;
    end for;
    return true;
end function;

function seq_to_word(seq,F)
  if #seq eq 0 then return F!1; end if;
  Fs := [F.1, F.2];
  return &*[Fs[s[1]]^(s[2]) : s in seq];
end function;

function crv_iso_to_ff_map(C,phis)
    FC := FunctionField(C);
    KC,mpC := AlgorithmicFunctionField(FC);
    Fgens := gen_seq(KC);
    if Rank(CoordinateRing(Ambient(C))) eq 2 then //P^1
	booP1 := true;
	gen1 := Fgens[1];
	Remove(~Fgens,1);
    else
	booP1 := false;
    end if;

    Ca := AffinePatch(C1, FFPatchIndex(C1))
	where C1 is (IsProjective(C) select C else ProjectiveClosure(C));
    rat_ff := [mpC(FC.i) : i in [1..Length(Ca)]];
    ff_rat := [Index(seq,s): s in [mpCi(f) : f in Fgens]] where
	mpCi is Inverse(mpC) where seq is [FC.i : i in [1..Length(Ca)]];
    assert &and[i gt 0 : i in ff_rat];

    L := [];
    for phi in phis do
      // get corr. ff_map_ims for aelts
      // using stripped down version of Pullback
      phi_aff := RestrictionToPatch(phi,fp,fp) where fp is FFPatchIndex(C);
      ff_map_ims := [coerce_to_ff(eqns[i],rat_ff) : i in ff_rat] where
			eqns is DefiningEquations(phi_aff);
      if booP1 then 
	ff_map_ims := [gen1] cat ff_map_ims cat [gen1];
      end if;
      // and make AlFF morphism from it
      boo,mp,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, ff_map_ims);
      assert boo;
      Append(~L,mp);
    end for;
    if #L eq 0 then //if phis is empty, add the identity
	L := [Identity(FunctionFieldCategory())(KC)];
    end if;
    return L;
end function;

function word_data(ws,n)
// ws is Eltseq(w) for w a word in F(n), a free group of rank n.
//  returns a power sequence for w in the form [<2,m1>,<n+1,m2>,<n+2,m3>..]
//  for g2^m1*g1^-m2*g2^-m3....

    ws1 := [];
    if #ws eq 0 then return ws1; end if;
    j := 1; v := ws[1];
    for i in [2..#ws] do
      if ws[i] eq v then
	j +:= 1;
      else
	if v lt 0 then v := n-v; end if;
	Append(~ws1,<v,j>);
	j := 1; v := ws[i];
      end if;	  	
    end for;
    if v lt 0 then v := n-v; end if;
    Append(~ws1,<v,j>);
    return ws1;

end function;

function gen_ffmps(Gelts,gs,ms,gid)
// gs = [g1f,g2f,..gnf,g1f^-1,g2f^-1,..gnf^-1],
// ms := [m1,m2,..,mn,m_(n+1),m_(n+2),..m_(2n)] are the max powers to which these
//  occur in words. gid is the identity FF map.
//  -assumed that Gelts[1] is id

   n := (#gs) div 2;
   gps := [];
   for j in [1..#gs] do
     gjps := [gs[j]]; gjp := gs[j];
     for i in [2..ms[j]] do
       gjp := gjp*gs[j];
       Append(~gjps,gjp);
     end for;
     Append(~gps,gjps);
   end for;
  
   ffmps := [gid];
   for i in [2..#Gelts] do
      g := Gelts[i];
      wd := word_data(Eltseq(g),n);
      Reverse(~wd); // ff maps go in reverse!
      ffm := gps[wd[1][1]][wd[1][2]];
      for j in [2..#wd] do
	ffm := ffm*(gps[wd[j][1]][wd[j][2]]);
      end for;
      Append(~ffmps,ffm);
   end for;

   return ffmps;
end function;

function get_AL_sm(C,X0Nrec,d)
// return the Atkin-Lehner w_d auto on C, a base change of X0(N)
    N := X0Nrec`N;
    ds := [i : i in Divisors(N) | GCD(i, N div i) eq 1];
    i := Index(ds,d)-1;
    eqns := [R!e : e in (X0Nrec`ALs)[i]] where 
		R is CoordinateRing(Ambient(C));
    return iso<C->C| eqns,eqns : Check := false>;

end function;

function get_S2_power_sm(C,X0Nrec,v2,z)
// return the automophism S_{2^v2} on C, a base change of X0(N) to field K
//  which contains z, a primitive (2^v2)th root of unity

    eqns1 := (X0Nrec`S2ns)[v2];
    R := CoordinateRing(Ambient(C)); // z should be in K
    if v2 eq 1 then //eqns defined over Q and define an ord 2 auto
      eqns := [R!e : e in eqns1]; eqnsi := eqns;
    else
      R1 := Universe(eqns1);            // k1 should be Q(mu_{2^v2})
      k1 := BaseRing(R1); k := BaseRing(R);
      hm := hom<R1->R| hom<k1->k|[z]>,[R.i : i in [1..Rank(R)]]>;
      hmi := hom<R1->R| hom<k1->k|[1/z]>,[R.i : i in [1..Rank(R)]]>;
      eqns := [hm(e) : e in eqns1]; eqnsi := [hmi(e) : e in eqns1];
    end if;
    return iso<C->C| eqns,eqnsi : Check := false>;

end function;

function get_S3_sm(C,X0Nrec,z)
// return the automophism S_3 on C, a base change of X0(N) to field K
//  which contains z, a primitive 3rd root of unity

    eqns1 := X0Nrec`S3;
    R := CoordinateRing(Ambient(C));
    R1 := Universe(eqns1);            // k1 should be Q(mu_3)
    k1 := BaseRing(R1); k := BaseRing(R);
    hm := hom<R1->R| hom<k1->k|[z]>,[R.i : i in [1..Rank(R)]]>;
    hmi := hom<R1->R| hom<k1->k|[1/z]>,[R.i : i in [1..Rank(R)]]>;
    eqns := [hm(e) : e in eqns1]; eqnsi := [hmi(e) : e in eqns1];
    return iso<C->C| eqns,eqnsi : Check := false>;

end function;

function get_extra_aut_sm(C,X0Nrec,z)
// for N = 37 or 63, return the extra automorphism on C, a base change of X0(N) to
// field K which contains z, resp. 1, a primitive 3rd root of unity
// - for N = 108, when the extra inv is not defined over a cyclotomic field, will
//   add a separate function

    N := X0Nrec`N;
    assert (N eq 37) or (N eq 63);
    if N eq 37 then
	eqns1 := X0Nrec`extra_aut;
    else
	eqns1,eqns1i := Explode(X0Nrec`extra_aut);
    end if;
    R := CoordinateRing(Ambient(C));
    if N eq 37 then
	return iso<C->C|eqns,eqns : Check := false> where
	  eqns is [R!f : f in eqns1];
    end if;
    R1 := Universe(eqns1);            // k1 should be Q(mu_3)
    k1 := BaseRing(R1); k := BaseRing(R);
    hm := hom<R1->R| hom<k1->k|[z]>,[R.i : i in [1..Rank(R)]]>;
    eqns := [hm(e) : e in eqns1]; eqnsi := [hm(e) : e in eqns1i];
    return iso<C->C| eqns,eqnsi : Check := false>;

end function;

function get_2_type(N,n)
// Returns the type of the "2-part" of the automorphism group of X0(N) over Q(mu_n)
//  and the maximum exponent r such that S_{2^r} lies in it

    m2 := Valuation(N,2);
    n2 := Min(3,m2 div 2);
    exp2 := Min(n2,Valuation(n,2));
    if exp2 eq 0 then exp2 := Min(1,n2); end if;

    case exp2:
	when 0: typ2 := ((m2 eq 0) select -1 else 0);
	when 1: typ2 := ((m2 eq 2) select 1 else 2);
	when 2: if n2 eq 2 then
		  typ2 := ((m2 eq 4) select 3 else 5);
		else
		  typ2 := 4; //n2 eq 3 case
		end if;
	when 3: typ2 := Min(m2,9); // m2 >= 6, 8|n
    end case;
    return typ2,exp2;

end function;

function ord_2_type(typ)
// the order of the "2-part" group of type typ
    if typ lt 0 then 
	return 1;
    elif typ ge 7 then
	return 128;
    elif typ ge 5 then
	return (typ-3)*(2^(typ-1)); // typ is 5 or 6
    else
	return (IsOdd(typ) select 3 else 2)*(2^typ);
    end if;
end function;

function get_3_type(N,n)
// Returns the type of the "3-part" of the automorphism group of X0(N) over Q(mu_n)
//  and 1 if S3 lies in this group, 0 otherwise.

    m3 := Valuation(N,3);
    if (m3 gt 1) and IsDivisibleBy(n,3) then
	if N eq 63 then return 3,1; end if;
	return ((m3 eq 2) select 1 else 2),1;
    else
	return ((m3 eq 0) select -1 else 0),0;
    end if;

end function;

function ord_3_type(typ)
// the order of the "3-part" group of type typ
    if typ le 0 then return (typ+2); end if;
    return 6*(typ+1);
end function;

function ord_G(N,n)
// order of the aut gp of X0(N) over Q(mu_n)
    return ord_2_type(get_2_type(N,n))*ord_3_type(get_3_type(N,n))*
	(2^(#[f[1] : f in Factorisation(N) | f[1] gt 3]))*((N eq 37) select 2 else 1);
end function;

function poss_ords(N)
// Returns a list of pairs <ord_n,n> of different possible orders for the aut gp of
//  X0(N) over Q(mu_n) [n is minimal for ord_n]

    if N eq 37 then return [<4,1>]; end if;
    m2 := Valuation(N,2);
    n2s := [1] cat [2^r : r in [2..Min(3,m2 div 2)]];
    n2os := [ord_2_type(get_2_type(N,n)) : n in n2s];
    m3 := Valuation(N,3);
    n3s := [3^r : r in [0..Min(1,m3 div 2)]];
    n3os := [ord_3_type(get_3_type(N,n)) : n in n3s];
    o1 := 2^(#[f[1] : f in Factorisation(N) | f[1] gt 3]);
    if N eq 37 then o1 *:= 2; end if;
    pairs := [<n2os[i]*n3os[j]*o1,n2s[i]*n3s[j]> : j in [1..#n3s], i in [1..#n2s]];
    return pairs;

end function;

function get_Wd_ind(d,N,n)
// Returns the indices of the AL involutions w_d for d|N, (d,N/d)=1 in the
//  set of automorphism elements in the auto gp of X0(N) over Q(mu_n)

    if d eq 1 then return 1; end if;

    typ2 := get_2_type(N,n);
    typ3 := get_3_type(N,n);
    if (typ3 eq 3) and (d gt 7) then //N=63 case
	return ((d eq 9) select 17 else 18);
    end if;
    ps := [f[1] : f in Factorisation(N)];
    ords := [case<p|2:ord_2_type(typ2),3:ord_3_type(typ3),default:2> : p in ps];
    ords1 := [&*[Integers()| ords[j] : j in [i+1..#ords]] : i in [1..#ords]];

    pis := [Index(ps,f[1]) : f in Factorisation(d)];
    return 1+(&+[ords1[i] : i in pis]);

end function;

function get_Sr_ind(r,N,n)
// Returns the index of the Sr automorphism in the set of automorphism elements
//  in the auto gp of X0(N) over Q(mu_n). Actually if 6|r, it actually returns
//  the index of (Sr)^(2p+3p)=S2p*S3p where 2p (resp. 3p) is the exact power of 2
//  (resp 3) dividing r.

    if r eq 1 then return 1; end if;
    //assert IsDivisibleBy(24,r) and IsDivisibleBy(N,r^2);
    //assert ((Valuation(r,2) eq 1) select IsDivisibleBy(n,r) else IsDivisibleBy(n,r div 2);

    if N eq 63 then return 3; end if;
    n1 := 2^(#[f[1] : f in Factorisation(N) | f[1] gt 3]);
    if IsDivisibleBy(r,3) then
	ind3 := 2*n1+1;
	r := r div 3;
    else
	ind3 := 1;
    end if;

    if r eq 1 then
	ind2 := 1;
    else
	n1 *:= ord_3_type(get_3_type(N,n));
	typ2,exp2 := get_2_type(N,n);
	er := Valuation(r,2); //r = 2^er
	case exp2-er:
	  when 0: ind2 := 2;
	  when 1: ind2 := 7;
	  when 2: ind2 := \[30,36,37,35][typ2-5]; //here,exp2=3 and typ2>=6
	end case;
	ind2 := ind2*n1+1;
    end if;

    return ind2+ind3-1;

end function;

function get_ea_ind(N)
// for N = 37, 63 or 108, get the index of the extra automorphism in the (full automorphism group)
    case N:
	when 37: return 3;
	when 63: return 5;
    end case;
    return 0; // fill in for N=108 when it arises!
end function;

function auto_gp_over_extension(C,X0Nrec,n,z,boo_inst)
// Generates the group of automorphisms G of C over Q(mu_n), where C is X0N
// over the field K which contains z - a primitive nth root-of-1 which we assume
// corresponds to e^(2*pi*i/n). If boo_inst, the group is cached as the full
// automorphism group of C

    N := X0Nrec`N;
    m2 := Valuation(N,2);
    m3 := Valuation(N,3);
    error if ((Min(m2,m3) ge 3) and IsDivisibleBy(n,12) and IsOdd(m2*m3)),
      "Sorry, can't yet handle the case 864|N, 12|n and the 2 and 3 valuations of N are both odd";

    //generate 2,3 part
    typ2,exp2 := get_2_type(N,n);
    typ3,exp3 := get_3_type(N,n);
    if exp2 gt 0 then
      S2r := get_S2_power_sm(C,X0Nrec,exp2,z^(n div 2^exp2));
    end if;
    if exp3 gt 0 then
      S3 := get_S3_sm(C,X0Nrec,z^(n div 3));
    end if;
    l2 := ((typ2 le 0) select 2*(typ2+1) else (\[3,4,4,8,8,12,16,16,16])[typ2]);
    l3 := ((typ3 eq 3) select 4 else 2*(typ3+1));
//printf "typ2: %o  m2: %o  exp2: %o  l2: %o\n",typ2,m2,exp2,l2;
//printf "typ3: %o  m3: %o  exp3: %o  l3: %o\n",typ3,m3,exp3,l3;

    F := FreeGroup(2);
    C2 := CyclicGroup(2);
    C2elts := {@C2!1,C2.1@};
    Fseq := gen_seq(AlgorithmicFunctionField(FunctionField(C)));
    Fid := Identity(FunctionFieldCategory())
	(AlgorithmicFunctionField(FunctionField(C)));

    if typ2 eq 0 then
      G2 := C2;
      G2elts := C2elts;
      //G2ffmps := [Fid,(crv_iso_to_ff_map(C,[get_AL_sm(C,X0Nrec,2^m2)]))[1]];
      gens2sm := [get_AL_sm(C,X0Nrec,2^m2)];
      G2ffdat := <[w],[1],[w],[0]> where w is
		(crv_iso_to_ff_map(C,gens2sm))[1] ; 
    elif typ2 gt 0 then
      G2 := quo<F|[seq_to_word(r,F) : r in rels2[typ2]]>;
      G2elts := Transversal(G2,sub<G2|>);
      //ms := [1,e,0,e-1] where e is 2^(exp2-1);
      gens2sm := [get_AL_sm(C,X0Nrec,2^m2),S2r];
      gs := crv_iso_to_ff_map(C,gens2sm cat [Inverse(S2r)]);
      //gs := [gs[i]: i in [1,2,1,3]];
      //G2ffmps := gen_ffmps(G2elts,gs,ms,Fid);
      G2ffdat := <[gs[1],gs[2]],[1,e],[gs[1],gs[3]],[0,e-1]> where e is 2^(exp2-1);
    end if;

    if typ3 eq 0 then
      G3 := C2;
      G3elts := C2elts;
      gens3sm := [get_AL_sm(C,X0Nrec,3^m3)];
      G3ffdat := <[w],[1],[w],[0]> where w is
		(crv_iso_to_ff_map(C,gens3sm))[1] ;
    elif typ3 eq 3 then
      G3 := quo<F|[seq_to_word(r,F) : r in rels3[typ3]]>;
      G3elts := Transversal(G3,sub<G3|>);
      gens3sm := [S3,get_extra_aut_sm(C,X0Nrec,z^(n div 3))];
      gs := crv_iso_to_ff_map(C,gens3sm cat [Inverse(g) : g in gens3sm]);
      G3ffdat := <[gs[1],gs[2]],[1,2],[gs[3],gs[4]],[1,1]>; 
    elif typ3 gt 0 then
      G3 := quo<F|[seq_to_word(r,F) : r in rels3[typ3]]>;
      G3elts := Transversal(G3,sub<G3|>);
      gens3sm := [get_AL_sm(C,X0Nrec,3^m3),S3];
      gs := crv_iso_to_ff_map(C,gens3sm cat [Inverse(S3)]);
      //gs := [gs[i]: i in [1,2,1,3]];
      G3ffdat := <[gs[1],gs[2]],[1,1],[gs[1],gs[3]],[0,1]>;
    end if;

    if exp2 gt 1 then
      if IsEven(m2) or (exp3 eq 0) then //2 part is normal subgroup
	gens2 := [p cat [(#p)+i : i in [1..l3]] : p in perms2[typ2]];
	aut2 := (IsEven(m3) select [1..l2] else as[1]) where
	   as is auts2[typ2];
	if exp3 eq 0 then 
	  gens3 := ((m3 eq 0) select [] else [aut2 cat [2+l2,1+l2]]);
	else //exp3 = 1
	  gens3 := [aut2 cat as[1], [1..l2] cat as[2]] where as is perms3[typ3];
	end if;
      else //3 part normal, exp3 = 1, m2 odd, m3 even
	aut3 := [l2+i : i in auts3[typ3]]; 
	gens2 := [p[1] cat aut3, p[2] cat [l2+1..l2+l3]] where
		p is perms2[typ2];
	gens3 := [[1..l2] cat p : p in perms3[typ3]];
      end if;
    elif exp2 eq 1 then //3 part is normal
	if m3 eq 0 then
	  gens2 := perms2[typ2]; gens3 := [];
	elif exp3 eq 0 then
	  gens2 := [p cat [l2+1,l2+2] : p in perms2[typ2]];
	  gens3 := [[1..l2] cat [l2+2,l2+1]];
	else //exp3 = 1
	  aut3 := (IsEven(m2) select [l2+1..l2+l3] else [l2+i : i in auts3[typ3]]);
	  gens2 := [p[1] cat aut3, p[2] cat [l2+1..l2+l3]] where
		p is perms2[typ2];
	  gens3 := [[1..l2] cat [l2+i : i in p] : p in perms3[typ3]];
	end if;
    else //3 part is normal
	if m3 eq 0 then gens3 := [];
	elif exp3 eq 0 then gens3 := [[2,1]];
	else gens3 := perms3[typ3]; end if;
	if l2 gt 0 then
	  gens3 := [[1..l2] cat [l2+i : i in p] : p in gens3];
	end if;
	if m2 eq 0 then
	  gens2 := [];
	elif IsEven(m2) or (exp3 eq 0) then
	  gens2 := [[2,1] cat [l2+1..l2+l3]];
	else
	  gens2 := [[2,1] cat [l2+i : i in auts3[typ3]]];
	end if;
    end if;

    // now do remaining part corr to p|N, p > 3
    N1 := N div ((2^m2)*(3^m3));
    facts := Factorization(N1);
    gens := []; genssm := [];
    Gs := [**];
    Geltss := [**];
    Gffdats := [**];
    l0 := l2+l3;
    if #facts gt 0 then
	seq := [l0+1..l0+2*(#facts)];
	gens2 := [g cat seq : g in gens2];
	gens3 := [g cat seq : g in gens3];
    end if;
    if m2 gt 0 then 
	gens := gens cat gens2; genssm := genssm cat gens2sm;
	Append(~Geltss,G2elts); Append(~Gffdats,G2ffdat); Append(~Gs,G2);
    end if;
    if m3 gt 0 then 
	gens := gens cat gens3; genssm := genssm cat gens3sm;
	Append(~Geltss,G3elts); Append(~Gffdats,G3ffdat); Append(~Gs,G3);
    end if;
    //ps := ps cat [f[1] : f in facts];
    l := l0;
    if N eq 37 then
	gens := [[2,1,3,4],[1,2,4,3]];
	w := get_AL_sm(C,X0Nrec,37);
	ea := get_extra_aut_sm(C,X0Nrec,1);
	genssm := [ea,w];
	Gs := [* C2,C2 *];
	Geltss := [* C2elts,C2elts *];
	Gffdats := [* <[af[1]],[1],[af[1]],[0]>,<[af[2]],[1],[af[2]],[0]> *] 
	   where af is crv_iso_to_ff_map(C,genssm);
	l := 4;
    else
      for f in facts do
	r2 := f[1] mod 2^exp2;
	if IsEven(f[2]) or (exp2 le 1) or (r2 eq 1) then
	  gen := [1..l2];
	else
	  gen := auts2[typ2][(r2-1) div 2]; 
	end if;
	if IsEven(f[2]) or (exp3 eq 0) or ((f[1] mod 3) eq 1) then
	  gen := gen cat [l2+1..l2+l3];
	else
	  gen := gen cat [l2+i : i in auts3[typ3]]; 
	end if;
	gen := gen cat [l0+1..l] cat [l+2,l+1] cat [l+3..l0+2*(#facts)];
	w := get_AL_sm(C,X0Nrec,f[1]^f[2]);
	Append(~gens,gen); Append(~genssm,w);
	Append(~Gs,C2); Append(~Geltss,C2elts);
	Gffdat := <[wf],[1],[wf],[0]> where wf is (crv_iso_to_ff_map(C,[w]))[1];
	Append(~Gffdats,Gffdat);
	l +:= 2;
      end for;
    end if;

    // now build the final aut group data from the prime factor parts
    S := SymmetricGroup(l);
    G := sub<S|gens>;
    FG := FreeGroup(#gens);
    Geltss1 := [**];
    Ghms := [**];
    ind := 1; Gind := 1;
    if m2 gt 0 then
	ng := #gens2;
	s := {@ hm(g) : g in Geltss[1] @} where hm is hom<Gs[1]->G|[G.i : i in [1..ng]]>;
	Append(~Geltss1,s);
	Append(~Ghms,hom<Gs[1]->FG|[FG.i : i in [1..ng]]>);
	ind +:= ng; Gind +:= 1;
    end if;
    if m3 gt 0 then
	ng := #gens3;
	s := {@ hm(g) : g in Geltss[Gind] @} where
			hm is hom<Gs[Gind]->G|[G.i : i in [ind..ind+ng-1]]>;
	Append(~Geltss1,s);
	Append(~Ghms,hom<Gs[Gind]->FG|[FG.i : i in [ind..ind+ng-1]]>);
	ind +:= ng; Gind +:= 1;
    end if;    
    for i in [Gind..#Gs] do
	s := {@ hm(g) : g in Geltss[i] @} where hm is hom<Gs[i]->G|[G.(i+ind-Gind)]>;
	Append(~Geltss1,s);
	Append(~Ghms,hom<Gs[i]->FG|[FG.(i+ind-Gind)]>);
    end for;

    carttup := <[1..#(Gs[1])]>;
    for i in [2..#Gs] do Append(~carttup,[1..#(Gs[i])]); end for;
    cart := CartesianProduct(carttup);
    Gelts := {@ &*[Geltss1[i][c[i]] : i in [1..#Gs]] : c in cart @};
    Gelts1 := [&*[(Ghms[i])(Geltss[i][c[i]]) : i in [1..#Gs]] : c in cart];
    ffelts := gen_ffmps(Gelts1, &cat[Gffdats[i][1] : i in [1..#Gs]] cat
	&cat[Gffdats[i][3] : i in [1..#Gs]], &cat[Gffdats[i][2] : i in [1..#Gs]] cat
	&cat[Gffdats[i][4] : i in [1..#Gs]], Fid);
    seq := (Length(Ambient(C)) eq 2) select [Fseq[2]] else Fseq; // C = P^1?
    Aelts := {@ [f(s) : s in seq] : f in ffelts @};
    invs := find_inverses(Gelts);

    //finally set up the aut group structures
    if boo_inst then
      CG := InternalAutomorphismGroup(C);
    else
      CG := InternalAutomorphismGroup(C,[]);
    end if;
    CG`Fgens := Fseq;
    CG`G := G;
    CG`Gelts := Gelts;
    CG`Aelts := Aelts;
    CG`invs := invs;

    if not assigned CG`ff_rat then
      add_ff_rat_map_data(~CG,Fseq);
    end if;

    //add extra attributes
    Agens := [];
    for i in [1..#gens] do
	ind := Index(Gelts,G.i);
	mp := ffelts[ind]; mpi := ffelts[invs[ind]];
	ff_map := SpecifyInverseMorphisms(FunctionFieldCategory())(mp, mpi);
	sch_map := genssm[i];
	Append(~Agens, rec<grpAutCrvEltRec | crv_map := sch_map,
			ff_map := ff_map, index := ind>);
    end for;
    CG`Agens := Agens;
    CG`id := rec<grpAutCrvEltRec | crv_map := IdentityMap(C), ff_map := Fid, index := 1>;

    return CG;

end function;

function AL_inv_fn(C,X0Nrec,d)
// the AL inv wd [d|N,(d,N/d)=1] for C, a basechange of X0(N)

    N := X0Nrec`N;
    CG := InternalAutomorphismGroup(C);
    booG := (assigned CG`G);

    if d eq 1 then
	return (booG select CG!1 else IdentityMap(C));
    end if;

    wd := get_AL_sm(C,X0Nrec,d);
    if not booG then return wd; end if;

    //return wd as an elt of CG is poss
    wd_aff := RestrictionToPatch(wd,fp,fp) where fp is FFPatchIndex(C);
    ff_map_ims := [coerce_to_ff(eqns[i],CG`rat_ff) : i in CG`ff_rat] where
			eqns is DefiningEquations(wd_aff);
     // try to guess n s.t. CG is aut gp of X0N over Q(mu_n)
    if BaseRing(C) cmpeq Rationals() then
	n := 1;
    else
	pos := poss_ords(N);
	i := Index([o[1] : o in pos],#CG);
        n := ((i eq 0) select 1 else (pos[i])[2]);
    end if;
    wdind := get_Wd_ind(d,N,n);
     //wd should be the wdindth element in CG
    if (wdind le #CG) and (ff_map_ims eq CG`Aelts[wdind]) then
	index := wdind;
    else
	index := Index(CG`Aelts,ff_map_ims);	
    end if;
    if index eq 0 then return wd; end if;
    KC := AlgorithmicFunctionField(FunctionField(C));
    if Rank(CoordinateRing(Ambient(C))) eq 2 then //P^1
	ff_map_ims := [g1] cat ff_map_ims cat [g1] where g1 is(CG`Fgens)[1] ;
    end if;
    boo,mp,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, ff_map_ims);
    assert boo;
    ff_map := SpecifyInverseMorphisms(FunctionFieldCategory())(mp, mp);
    phi := InternalGrpAutCrvEltFromMapAutSch(CG,wd);
    phi`ff_map := ff_map; phi`index := index;
    return phi;

end function;

function Sr_fn(C,X0Nrec,r,z)
// the Sr automorphism of C, a basechange of X0(N) to a field K that contains
//  z as an r-th root of unity [r|24 and r^2|N]

    N := X0Nrec`N;
    CG := InternalAutomorphismGroup(C);
    booG := (assigned CG`G);

    if r eq 1 then
	return (booG select CG!1 else IdentityMap(C));
    end if;

    v2 := Valuation(r,2);
    v3 := Valuation(r,3);
    if v2 eq 0 then			//r=3 case
      Sr := get_S3_sm(C,X0Nrec,z);
    elif v3 eq 0 then			//r=2^v2 case
      Sr := get_S2_power_sm(C,X0Nrec,v2,z);
    else
      S2n := get_S2_power_sm(C,X0Nrec,v2,z^3);
      S3 := get_S3_sm(C,X0Nrec,z^(2^v2));
      case v2:
	when 1: Sr := Expand(S2n*Inverse(S3));
	when 2: Sr := Expand(S3*Inverse(S2n));
	when 3: A := Expand(S2n*S2n); B := Expand(S2n*Inverse(S3));
		Sr := Expand(A*B); //a bit nasty but can only occur for 576|N - a long
				   //  way off in practise!
      end case;
      // must make the type of Sr a MapAutSch!
      Sr := iso<C->C|DefiningPolynomials(Sr),InverseDefiningPolynomials(Sr) : Check := false>;
      if assigned X0Nrec`Sn_degs then
	d := (X0Nrec`Sn_degs)[v2];
	d1 := LeadingTotalDegree([e : e in DefiningPolynomials(Sr) | e ne 0][1]);
	d2 := LeadingTotalDegree([e : e in InverseDefiningPolynomials(Sr) | e ne 0][1]);
	if (d1 gt d) or (d2 gt d) then
	  eqns := ((d1 gt d) select ReduceMapDegree(Sr : DegreeBound := d) else
		DefiningPolynomials(Sr));
	  eqnsi := ((d2 gt d) select ReduceMapDegree(Inverse(Sr) : DegreeBound := d) else
		InverseDefiningPolynomials(Sr));
	  Sr := iso<C->C|eqns,eqnsi : Check := false>;	  
	end if;
      end if;
    end if;
    if not booG then return Sr; end if;

    //return Sr as an elt of CG is poss
    Sr_aff := RestrictionToPatch(Sr,fp,fp) where fp is FFPatchIndex(C);
    ff_map_ims := [coerce_to_ff(eqns[i],CG`rat_ff) : i in CG`ff_rat] where
			eqns is DefiningEquations(Sr_aff);
     // try to guess n s.t. CG is aut gp of X0N over Q(mu_n)
    if BaseRing(C) cmpeq Rationals() then
	n := 1; //r must be 2 here!
    else
	pos := poss_ords(N);
	i := Index([o[1] : o in pos],#CG);
        n := ((i eq 0) select 1 else (pos[i])[2]);
	if not IsDivisibleBy(IsOdd(n) select 2*n else n,r) then
	  n := r;
	end if;
    end if;

    Sind := get_Sr_ind(r,N,n);
    if (v2*v3 gt 0) and (Sind le #CG) then
	if v2 eq 1 then
	  Sind := (CG`invs)[Sind];
	else // only poss when 144|N
	  g := (CG`Gelts)[Sind];
	  g := g^(3+(2^v2));
	  Sind := Index(CG`Gelts,g);
	end if;
    end if;
     //Sr should be the Sindth element in CG
    if (Sind le #CG) and (ff_map_ims eq CG`Aelts[Sind]) then
	index := Sind;
    else
	index := Index(CG`Aelts,ff_map_ims);	
    end if;
    if index eq 0 then return Sr; end if;
    KC := AlgorithmicFunctionField(FunctionField(C));
    bP1 := Rank(CoordinateRing(Ambient(C))) eq 2; //P^1?
    if bP1 then
	gen1 := (CG`Fgens)[1];
	ff_map_ims := [gen1] cat ff_map_ims cat [gen1];
    end if;
    boo,mp,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, ff_map_ims);
    assert boo;
    if r gt 2 then
	mp_inv_ims := (CG`Aelts)[(CG`invs)[index]];
	if bP1 then mp_inv_ims := [gen1] cat mp_inv_ims cat [gen1]; end if;
	boo,mpi,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, mp_inv_ims);
	assert boo;
    else
	mpi := mp;
    end if;
    ff_map := SpecifyInverseMorphisms(FunctionFieldCategory())(mp, mpi);
    phi := InternalGrpAutCrvEltFromMapAutSch(CG,Sr);
    phi`ff_map := ff_map; phi`index := index;
    return phi;

end function;

function extra_aut_fn(C,X0Nrec,z)
// for N = 37,63 or 108 (not done properly yet!), return the "extra automorphism" of C, a basechange of
// X0(N) to a field K that contains z = 1 resp. a prim. 3rd root of unity

    N := X0Nrec`N;
    CG := InternalAutomorphismGroup(C);
    booG := (assigned CG`G);

    ea := get_extra_aut_sm(C,X0Nrec,z);
    if not booG then return ea; end if;

    //return ea as an elt of CG is poss
    ea_aff := RestrictionToPatch(ea,fp,fp) where fp is FFPatchIndex(C);
    ff_map_ims := [coerce_to_ff(eqns[i],CG`rat_ff) : i in CG`ff_rat] where
			eqns is DefiningEquations(ea_aff);
    eaind := get_ea_ind(N);
     //ea should be the eaindth element in CG
    if (eaind le #CG) and (ff_map_ims eq CG`Aelts[eaind]) then
	index := eaind;
    else
	index := Index(CG`Aelts,ff_map_ims);	
    end if;
    if index eq 0 then return ea; end if;
    KC := AlgorithmicFunctionField(FunctionField(C));
    boo,mp,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, ff_map_ims);
    assert boo;
    if N eq 63 then
	boo,mpi,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, (CG`Aelts)[(CG`invs)[index]]);
	assert boo;
    else
	mpi := mp;
    end if;
    ff_map := SpecifyInverseMorphisms(FunctionFieldCategory())(mp, mpi);
    phi := InternalGrpAutCrvEltFromMapAutSch(CG,ea);
    phi`ff_map := ff_map; phi`index := index;
    return phi;

end function;

intrinsic AtkinLehnerInvolution(CN::Crv, N::RngIntElt, d::RngIntElt)
			-> MapAutSch
{ The dth AtkinLehner involution of CN, a base change of the curve from the X0N small modular
  curve database of level N, for d|N, GCD(d,N/d)=1 }

    require N gt 0: "N should be a positive integer";
    boo := (d gt 0);
    if boo then boo,q := IsDivisibleBy(N,d); end if;
    require boo and (GCD(d,q) eq 1):
	"d > 0 must divide N and (d,N/d) must be 1";    
    try
      X0Nrec := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;

    return AL_inv_fn(CN,X0Nrec,d);

end intrinsic;

intrinsic SrAutomorphism(CN::Crv, N::RngIntElt, r::RngIntElt, z::RngElt) -> MapAutSch
{ CN should be a base change of the curve from the X0N small modular
  curve database of level N to a field extension K of Q that contains a primitive r-th root of unity, z.
  r should be a positive divisor of 24 with r^2|N. Function returns the automorphism Sr of C that
  corresponds to the transformation z->z+(1/r) on the complex upper halfplane. }

    require N gt 0: "N should be a positive integer";
    require (r gt 0) and IsDivisibleBy(24,r) and IsDivisibleBy(N,r^2):
	"r should be a positive divisor of 24 such that r^2 divides N";
    boo,z := IsCoercible(BaseRing(CN),z);    
    require boo and is_primitive_nth_rt_of_1(z,r):
	"z should be a primitive r-th root-of-unity in the base field of CN";
    try
      X0Nrec := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;    
    return Sr_fn(CN,X0Nrec,r,z);

end intrinsic;

intrinsic ExtraAutomorphism(CN::Crv, N::RngIntElt, z::RngElt) -> MapAutSch
{ CN should be a base change of the curve from the X0N small modular
  curve database of level N to a field extension K of Q that contains a primitive r-th root of
  unity, z. N should be 37, 63 or 108 with r respectively 1,3,3. Returns an automorphism of C that is
  not given by the action of a matrix normalising GammaO(N)}

    // NB. This doesn't really work yet for N = 108!
    require N in \[37,63,108]:
	"Extra automorphism only exists for modular curves of level 37,63 and 108";
    r := ((N eq 37) select 1 else 3);
    boo,z := IsCoercible(BaseRing(CN),z);    
    require boo and is_primitive_nth_rt_of_1(z,r):
	"z should be a primitive r-th root-of-unity in the base field of C";
    try
      X0Nrec := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    return extra_aut_fn(CN,X0Nrec,z);

end intrinsic;

intrinsic AutomorphismGroupOverQ(CN::Crv, N::RngIntElt: Install := true) -> GrpAutCrv
{ CN should be base change of the curve from the X0N small modular curve database of level N to
  a field K of characteristic 0. Returns the modular automorphism group (i.e, the full automorphism group if
  the genus is > 1 and the group of automorphisms generated by the Wd and Sr automorphisms otherwise) of CN over 
  Q. If the parameter Install is true (the default) then the return value is internally installed as the full
  automorphism group of CN, so all K-rational modular automorphisms should be defined over Q in this case }

    return AutomorphismGroupOverExtension(CN,N,1,1 : Install := Install);

end intrinsic;

intrinsic AutomorphismGroupOverCyclotomicExtension(CN::Crv, N::RngIntElt, n::RngIntElt
		: Install := true ) -> GrpAutCrv
{ CN should be the base change of the curve from the X0N small modular curve database of level N to the
  cyclotomic field extension K of Q generated by the n-th roots of unity. Returns the 
  modular automorphism group (i.e, the full automorphism group if the genus is > 1 and the
  group of automorphisms generated by the Wd and Sr automorphisms otherwise) of CN over K. If the
  parameter Install is true (the default) then the return value is internally installed as the full
  automorphism group of CN }

    K := BaseRing(CN);
    if n eq 1 then
	z := K!1;
    elif n eq 2 then
	z := -K!1;
    else
	z := K.1;
    end if; 
    return AutomorphismGroupOverExtension(CN,N,n,z : Install := Install);

end intrinsic;

intrinsic AutomorphismGroupOverExtension(CN::Crv, N::RngIntElt, n::RngIntElt, z::RngElt
		: Install := true ) -> GrpAutCrv
{ CN should be the base change of the curve from the X0N small modular curve database of level N to
  a field extension K of Q that contains the n-th roots of unity mu_n and z should be a primitive n-th
  root of unity in K. Returns the modular automorphism group (i.e, the full automorphism group if the genus
  is > 1 and the group of automorphisms generated by the Wd and Sr automorphisms otherwise) of CN over Q(mu_n).
  If the parameter Install is true (the default) then the return value is internally installed as the full
  automorphism group of CN, so n should be chosen appropriately for K }

    require (N gt 0) and (n gt 0): "N and n should be positive integers";

    boo,z := IsCoercible(BaseRing(CN),z);    
    require boo and is_primitive_nth_rt_of_1(z,n):
	"z should be a primitive n-th root-of-unity in the base field of CN";
    try
      X0Nrec := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;

    G := InternalAutomorphismGroup(CN);
    if (not assigned G`G) or (#G ne ord_G(N,n)) then
	G := auto_gp_over_extension(CN,X0Nrec,n,z,Install);
    end if;
    if (not assigned G`eqn_deg_bnd) and (assigned X0Nrec`max_aut_degs) then
	mdegs := X0Nrec`max_aut_degs;
	n1 := GCD(n,2^Min(3,Valuation(N,2) div 2)*3^Min(1,Valuation(N,3) div 2));
        if Valuation(n1,2) eq 1 then n1 div:= 2; end if;
	i := Index([m[2] : m in mdegs],n1);
	if i gt 0 then G`eqn_deg_bnd := (mdegs[i])[1]; end if;
    elif not IsOrdinaryProjective(Ambient(CN)) then  //CN is hyperelliptic
	G`no_gcd := true;
    end if;
    return G;

end intrinsic;
