freeze;

import "Galois.m" : get_frobenius;
import "Galois.m" :get_tschirni, invar_coeff_ring;


CheckMSets:=function(G,m)
  L:=Subsets(Set(GSet(G)),m);
  L:=GSet(G,L);
  GG:=ActionImage(G,L);
  O:=Orbits(GG);
  return [#x:x in O], O;
end function; 

intrinsic GaloisProof(K::FldNum, S::GaloisData: Level := 0) -> BoolElt
  {}
  return GaloisProof(DefiningPolynomial(K), S:Level := Level);
end intrinsic;


/* Build up a set resolvent
   returning: 
   resolvent, tschirni, minimal precision to work with resolvent */
function BuildSetResolvent(f,n,S: U_test := false)

 assert IsSquarefree(f);
 s_ind := Subsets({1..Degree(f)},n); 

 if U_test cmpne false then
  assert Degree(f) eq Degree(U_test);
  orbs := Orbits(U_test,GSet(U_test,s_ind));
 else
  orbs := s_ind;
 end if;

 sep_prec := 0;
 repeat
  sep_prec := sep_prec + 1;
  all_tschirni := {};
  tschirn := Polynomial([0,1]);
  rt := [GaloisRoot(i,S:Prec := sep_prec) : i in [1..Degree(f)]]; 
  if sep_prec eq 1 then
   ff, pi := ResidueClassField(S`Ring);
   rt := [pi(x) : x in rt]; 
  end if;
  repeat
   rt_2 := [Evaluate(tschirn,a) : a in rt];
   rr_orbs := [{&+[rt_2[j] : j in jj] : jj in a} : a in orbs];  
   suc := &and [IsDisjoint(rr_orbs[i],rr_orbs[j]) : i,j in [1..#orbs] | i lt j]; 
   Include(~all_tschirni, tschirn);
   tschirn0 := tschirn;
   tschirn := get_tschirni(S, 3, Minimum(Degree(f), 2+#all_tschirni), all_tschirni,"ProdSum");  // linear transformations will not help.
  until suc or (#all_tschirni gt 2*Degree(f));
 until suc;
// Tschirnhausen transformation of f -- naive solution
 r1 := CharacteristicPolynomial(Evaluate(tschirn0,CompanionMatrix(f)));    
 res := MSum(r1,n);

 return res, tschirn0, sep_prec;
end function;

/* Given a group G proven to contain the Galois group of (f,S)
   and a subgroup U believed to contain the Galois group.
   We inspect the n-Set-Resolvent.
   We return false in case that the Galois group is not in U.
   Otherwiese we return the best provable approxmation to U by
   using the n-Set resolvent.                                    
   We return -1 if we can not find a good tschirn for the resolvent.    */
function ProofStepBySetResolvent(G, U, f, S, n) 
 assert U subset G;
 if not S`KnownSubgroup subset U then
  vprint GaloisGroup,1: "U does not contain the known subgroup";
  return false;
 end if;
 ss := Subsets({1..Degree(f)}, n);
 phi := Action(G,GSet(G,ss));
 orb_g := Orbits(phi(G));
 orb_u := Orbits(phi(U));
 if #orb_g eq #orb_u then // No information in this resolvent!
  return G;
 end if;
 
 res, tschirn, sep_prec := BuildSetResolvent(f, n, S: U_test := U);
 
 U0 := phi(G);
 for k := 1 to #orb_u do
  if orb_u[k] ne Orbit(U0,Representative(orb_u[k])) then 
// a check of this factor will improve U0
   r_deg := #orb_u[k];
   b0 := Max([(Evaluate(tschirn,S`max_comp)*n)^e * Binomial(r_deg,e) : e in [0..r_deg]]); 
   prec := 5 + Ceiling(Log(b0)/Log(S`Prime));
   orb_u_loc :=  GSet(S`KnownSubgroup, orb_u[k]);
   loc_orbs := Orbits(S`KnownSubgroup, orb_u_loc);

   if sep_prec eq 1 then
    ff,pi := ResidueClassField(S`Ring);  
    rt := [pi(GaloisRoot(i,S:Prec := 1)) : i in [1..Degree(f)]]; 
    rt := [Evaluate(tschirn,a) : a in rt];
    res_loc := PolynomialRing(ChangePrecision(S`Base,prec))!res;
    ff0,pi0 := ResidueClassField(S`Base); 
    fac0 := &*[PolynomialRing(ff0)!&*[Polynomial([-&+[rt[j] : j in aa],1]) : aa in a] : a in loc_orbs];
    res_ff := Polynomial([pi0(a) : a in Coefficients(res_loc)]);
    t1, fac1 := IsDivisibleBy(res_ff, fac0);    
    if not t1 then
     error "Contradiction in resolvent over finite field";
     return false;
    end if; 
    fac := HenselLift(res_loc, [fac0, fac1]);
    co := Coefficients(fac[1]);
   else
//    if not IsExport() then printf"N"; end if;
    rt := [GaloisRoot(i,S:Prec := prec) : i in [1..Degree(f)]];
    rt := [Evaluate(tschirn,a) : a in rt]; 
    fac0 := &*[PolynomialRing(ChangePrecision(S`Base,prec))!
               PolynomialRing(ChangePrecision(S`Ring,prec))!
               &*[Polynomial([-&+[rt[j] : j in aa],1]) : aa in a] : a in loc_orbs];
    co := Coefficients(fac0);
   end if;
   co2 := [];
   for a in co do
    a1 := Integers()!a; 
    if AbsoluteValue(a1) gt b0  then   
     vprintf GaloisGroup,1: "Coefficients of factor not in range\n";
     return false; 
    end if; // Proof failed. 
    Append(~co2, a1);
   end for; 
   test := Polynomial(co2);
   if not IsDivisibleBy(res, test) then
    vprintf GaloisGroup,1: "Resolvent does not factor as expected\n"; 
    return false;
   end if;
   U0 := Stabilizer(U0, orb_u[k]);
  end if;  
 end for;
 
 return (phi^(-1))(U0);
end function;


/* Given the galois data S. We compute the resolvent with respect to G / U.
   We return false, if the construction fails. This proofs that the Galois-Group is not in G. */
function BuildResolvent(S,G,U: inv := false)
 if Characteristic(S`Ring) eq 0 then
  IR := Integers();
 else
  IR := PolynomialRing(GF(Characteristic(S`Ring)));
 end if;

 if not S`KnownSubgroup subset G then
  error "Known subgroup is not contained in initial group";
  return false,_,_, _,_,_;
 end if;

 if inv cmpeq false then
  inv := RelativeInvariant(IR,G,U);
 end if;

 if not assigned inv`GalInvType then inv`GalInvType := "Other"; end if;

 ff := ResidueClassField(S`Ring);
 prec0 := Ceiling(2*Log(Index(G,U)) / Log(#ff)) + 1;
 tran := Transversal(G,U);
 all_tschirni := {};
 tschirn := Polynomial([0,1]);
 repeat
  rt := [GaloisRoot(i,S:Prec := prec0) : i in [1..Degree(G)]]; 
  Include(~all_tschirni, tschirn);
  rt_2 := [Evaluate(tschirn,a) : a in rt];
  
  val_s := [ Evaluate(inv,PermuteSequence(rt_2,s)) : s in tran];
  prec0 := prec0 + 1;
  tschirn0 := tschirn;
  tschirn := get_tschirni(S, 3, Minimum(Degree(G), 2+#all_tschirni), all_tschirni,inv`GalInvType);
 until Max([Valuation(val_s[i] - val_s[j]) : i,j in [1..#val_s] | i lt j]) lt prec0 - 1; 
 
 tschirn := tschirn0;
 b0 := Bound(inv,Evaluate(tschirn, S`max_comp));
 b0 := Max([b0^i * Binomial(Index(G,U),i) : i in [0..Index(G,U)]]);

 vprint GaloisGroup,2: "Tschirni %o Log_10 of Bound %o\n",tschirn, Log(b0) / Log(10);

 rt := [Evaluate(tschirn,GaloisRoot(i,S:Bound := 2 * b0)) : i in [1..Degree(G)]];

// Precision(rt[1]); S`Ring;

 phi := CosetAction(G,U);
 g_loc := phi(S`KnownSubgroup);
 tran := [i@@phi : i in [1..Index(G,U)]];
 orbs_loc := Orbits(g_loc); 

// first multiply the orbits of the local group
 if NumberOfOperations(inv, "*") gt Degree(S`Ring) then
  rt_rep_l := [Evaluate(inv,PermuteSequence(rt,tran[Representative(o)])) : o in orbs_loc];
  fac_l := [];
  for j := 1 to #orbs_loc do
   rt := [rt_rep_l[j]];
   for i in [2..#orbs_loc[j]] do
    Append(~rt, FrobeniusImage(rt[#rt]));
   end for;
   Append(~fac_l,&*[Polynomial([-a,1]) : a in rt]);
  end for;
 else
  fac_l := [&*[Polynomial([-Evaluate(inv,PermuteSequence(rt,tran[j])),1]) : j in a] : a in orbs_loc];
 end if;
 prec := Precision(rt[1]);
// Cast the local factors down to the base: 
 res_loc := &*[PolynomialRing(ChangePrecision(S`Base,prec))!PolynomialRing(ChangePrecision(S`Ring,prec))!a :  a in fac_l];
 co := Coefficients(res_loc);
 co2 := [];
 for a in co do
  e2 := Integers()!a;
  if AbsoluteValue(e2) gt b0 then // Do not error here. We want to have the option for a proof from below.
   vprintf GaloisGroup,1: "Resolvent coefficients above bound\n";
   return false,_,_, _,_, _; 
  end if;
  Append(~co2,e2);
 end for;
 return Polynomial(co2),inv,tschirn, fac_l, orbs_loc, phi;
end function;



/* Assuming the Galois group of f is proven to be contained in G.
   Using the resolvent corresponding to G / U_res we return
   false if the galois group is not in U.
   Otherwise we return the best proveable approximation to U with 
   respect to this resolvent.  
   I.e. the returned group is a proven parent group of the Galois group. */
function ProofStepGeneral(G, U, S, U_res)
 phi := CosetAction(G,U_res);
 if IsTransitive(phi(U)) then // Resolvent will be useless.
  return G;
 end if;

 res, inv, tschirn, fac_l, orbs_loc, phi := BuildResolvent(S,G,U_res);

 if res cmpeq false then
  vprintf GaloisGroup,1:"Contradiction in resolvent computation. Thus, G is wrong.\n";
  return false;
 end if;

 b0 := Bound(inv,Evaluate(tschirn, S`max_comp));
 b0 := Max([b0^i * Binomial(Index(G,U_res),i) : i in [0..Index(G,U_res)]]); 
 
 orbs_U := Orbits(phi(U)); 
 U0 := phi(G);
 for i := 1 to #orbs_U do
  if #orbs_U[i] ne #Orbit(U0,Representative(orbs_U[i])) then
   fac := &*[fac_l[j] : j in [1..#fac_l] | orbs_loc[j] subset orbs_U[i] ];
   co := Coefficients(fac);
   co2 := [];
   for a in co do
    e2 := Integers()!a;
    if AbsoluteValue(e2) gt b0 then 
     vprintf GaloisGroup,1: "Coefficients of factor above bound\n";
     return false; 
    end if;
    Append(~co2,e2);
   end for; 
  end if;
  if not IsDivisibleBy(res, Polynomial(co2)) then 
   vprintf GaloisGroup,1: "Resolvent does not factor\n";
   return false; 
  end if;
  U0 := Stabilizer(U0,orbs_U[i]);
 end for;
  
 return (phi^-1)(U0);
end function;

function BuildSubfieldPolynomial(S,G,B)
 R := SLPolynomialRing(Integers(),Degree(G):Global); 
 inv := &+[R.i : i in B]; inv`GalInvType := "Intransitive";
 U_bl := Stabilizer(G,B);
 res_sf,inv,tschirn := BuildResolvent(S,G,U_bl: inv := inv);
 
 return res_sf, inv, tschirn; 
end function;

function SubfieldSetResolvent(G,S,B,n)
 res_sf,inv,tschirn := BuildSubfieldPolynomial(S,G,B);
 return MSum(res_sf,n), inv, tschirn;
end function;

function ProofStepBySubfieldSetResolvent(G0, G, f, S, n, B)
 vprintf GaloisGroup, 2: "Using %o set resolvent to proof group of degree %o subfield\n",n,Degree(G) div #B;

 bls := SetToSequence(Orbit(G0,B));
 phi := Action(G0,Orbit(G0,{bls[i] : i in [1..n]}));
 

 if not IsTransitive(phi(G)) and (Degree(Image(phi)) eq Binomial(Degree(G) div #B, n)) then
  vtime GaloisGroup,2: res, inv, tschirn := SubfieldSetResolvent(G,S,B,n);

  orbs := Orbits(phi(G));
  prec0 :=  5 + Degree(tschirn);
  repeat
   rr := [GaloisRoot(i,S:Prec := prec0) : i in [1..Degree(G)]];
   onr := 0;
   repeat
    onr := onr + 1;
   until (onr gt #orbs) or (not IsWeaklyZero(Evaluate(Derivative(res), 
                                &+[ Evaluate(tschirn,rr[b])  : b in a, a in Representative(orbs[onr])] )));  
   prec0 := 2 * prec0;
  until onr le #orbs;
  // onr is the orbit that corresponds to a simple factor of the resolvent
  bb := 2 * (n * Bound(inv, Evaluate(tschirn, S`max_comp)))^#orbs[onr];

  vprintf GaloisGroup,2: "GaloisRoot with Log_10 bound %o\n", Log(bb)/Log(10);
  rt := [GaloisRoot(i,S:Bound := bb) : i in [1..Degree(G)]];
  rt_2 := [Evaluate(tschirn,a) : a in rt];

  vprintf GaloisGroup,2: "Building factor of degree %o\n",#orbs[onr];    
  prec := Precision(rt[1]);
  loc_orbs := Orbits(S`KnownSubgroup,GSet(S`KnownSubgroup,orbs[onr]));
  fac0 := &*[PolynomialRing(ChangePrecision(S`Base,prec))!
             PolynomialRing(ChangePrecision(S`Ring,prec))!
             &*[Polynomial([-&+[rt_2[j] : j in jj, jj in jjj],1]) : jjj in a] : a in loc_orbs];

//   fac0 := &*[Polynomial([-&+[rt_2[j] : j in jj, jj in jjj],1]) : jjj in orbs[onr]];
  co2 := [Integers()!a : a in Coefficients(fac0)];    
  if not IsDivisibleBy(res, Polynomial(co2)) then 
   vprintf GaloisGroup,1: "Subfield set resolvent does not factor\n";
   return false; 
  end if;
  g1 := Stabilizer(Image(phi),orbs[onr])  @@ phi; 
  vprintf GaloisGroup,2: "New group order %o\n",#g1;
  return g1; 
 end if;
 return G0;
end function;

// Compute the tower n-set-resolvent with respect to the block-system B
function BuildTowerSetResolvent(G,S,f,n,B:U_sep := false)

/* R := SLPolynomialRing(Integers(),Degree(G):Global); 
 inv := &+[R.i : i in B]; inv`GalInvType := "Intransitive";
 res_sf,inv,tschirn := BuildResolvent(S,G,U_bl: inv := inv); */
 U_bl := Stabilizer(G,B);

 res_sf,inv,tschirn := BuildSubfieldPolynomial(S,G,B);

 K := NumberField(res_sf);
 fac := Factorization(f,K);
 fac := [a[1] : a in fac];
 assert &and [Degree(a) ge #B  : a in fac];
 fac := [a : a in fac | Degree(a) eq #B]; 
 assert #fac gt 0;
 if #fac gt 1 then
  phi := Action(G,Orbit(G,B));
  o2 := Orbits(phi(U_bl));
  m := #[a : a in o2 | #a eq 1];
  assert #fac ge m;
  if m ne #fac then   // Blocksystem not identified by this
   vprint GaloisGroup,2: "To many subfield embeddings. TowerSetResolvent skiped.";
   return false,_,_; 
  end if;
 end if;
 
 g := fac[1];
 
 ind := GSet(G,Subsets(B,n));
 phi := Action(G,ind);
 if U_sep cmpne false then
  orbs_U := Orbits(phi(U_sep));
 else
  orbs_U := [{a} : a in ind];
 end if;

 sep_prec := 0;
 repeat
  sep_prec := sep_prec + 1;
  all_tschirni := {};
  tschirn := Polynomial([0,1]);
  rt := [GaloisRoot(i,S:Prec := sep_prec) : i in [1..Degree(f)]]; 
  if sep_prec eq 1 then
   ff, pi := ResidueClassField(S`Ring);
   rt := [pi(x) : x in rt]; 
  end if;
  repeat
   rt_2 := [Evaluate(tschirn,a) : a in rt];
   rr_orbs := [{&+[rt_2[j] : j in jj] : jj in a} : a in orbs_U];  
   suc := &and [IsDisjoint(rr_orbs[i],rr_orbs[j]) : i,j in [1..#orbs_U] | i lt j]; 
   Include(~all_tschirni, tschirn);
   tschirn0 := tschirn;
   tschirn := get_tschirni(S, 3, Minimum(Degree(f), 2+#all_tschirni), all_tschirni,"ProdSum");  // linear Tschirnis will not help.
  until suc or (#all_tschirni gt 2*Degree(f));
 until suc;
 tschirn := tschirn0; 

 res := Norm(MSum(CharacteristicPolynomial(Evaluate(tschirn,CompanionMatrix(g))),n));

 return res, tschirn, sep_prec;
end function;

/* Given a block-system of the transitive group G.
   We inspect the n-Set resolvent, corresponding to the tower-presentation with respect to B.
   From this we prove a better approximation of the galois group of f in direction to U and
   return this group.
 
   We return false if the Galois group is proven not to be U. 

   Here B is a block representing a block-system.   */
function ProofStepByTowerSetResolvent(G,U,f,S,n,B)

 assert U subset G;
 if (#B lt 2*n) then // this B/n-combination is useless
  return G;
 end if;
 if (OrbitBounded(G,B,Degree(G) div #B+1) cmpeq false) or (not IsTransitive(G)) then // not a block-system
  return G;
 end if; 

 ind := GSet(G,Subsets(B,n));
 phi := Action(G,ind);
 orbs_g := Orbits(phi(G));
 orbs_u := Orbits(phi(U));
 if #orbs_g eq #orbs_u then // Nothing provable with this resolvent
  return G;
 end if;

 res, tschirn, sep_prec := BuildTowerSetResolvent(G,S,f,n,B: U_sep := U);
 if res cmpeq false then // fail in resolvent construction
  return G;
 end if; 

 U0 := phi(G);
 for i := 1 to #orbs_u do
  if #orbs_u[i] ne #Orbit(U0,Representative(orbs_u[i])) then
   d := #orbs_u[i];
   b0 := Max([ Binomial(d,j) * (Evaluate(tschirn,S`max_comp)*n)^j : j in [1..d]]);
   prec := 5 + Ceiling(Log(b0) / Log(S`Prime));

   if sep_prec eq 1 then
    ff,pi := ResidueClassField(S`Ring);
    rt := [pi(GaloisRoot(i,S:Prec := 1)) : i in [1..Degree(f)]]; 
    rt_2 := [Evaluate(tschirn,a) : a in rt];
    fac0 := &*[Polynomial([-&+[rt_2[j] : j in jj],1]) : jj in orbs_u[i]];
    res_ff := Polynomial([pi(a) : a in Coefficients(res)]);
    t1, fac1 := IsDivisibleBy(res_ff, fac0);    
    if not t1 then
     error "Contradiction in resolvent over finite field";
     return false;
    end if; 
    fac := HenselLift(PolynomialRing(ChangePrecision(S`Base,prec))!res, [fac0, fac1]);
    co2 := [Integers()!a : a in Coefficients(fac[1])];
   else
//    if not IsExport() then printf"n"; end if;
    rt := [GaloisRoot(i,S:Prec := prec) : i in [1..Degree(f)]]; 
    rt_2 := [Evaluate(tschirn,a) : a in rt];
    fac0 := &*[Polynomial([-&+[rt_2[j] : j in jj],1]) : jj in orbs_u[i]];
    co2 := [Integers()!a : a in Coefficients(fac0)];    
   end if;
  end if;
  if not IsDivisibleBy(res, Polynomial(co2)) then 
   vprintf GaloisGroup,1: "Resolvent does not factor\n";
   return false; 
  end if;
  U0 := Stabilizer(U0,orbs_u[i]);
 end for;
 return (phi^(-1))(U0);
end function;

// Searches for a subgroup of G that defines a resolvent factoring in case of a descent to U
function FindResolventGroup(G,U)

// Recusion on orbits and blocks:
 if not IsTransitive(G) then
  orbs := Orbits(G);
  for a in orbs do
   phi := Action(G,a);
   if phi(G) ne phi(U) then
    std,pi := StandardGroup(phi(G));
    std_U := pi(phi(U));
    return (FindResolventGroup(std,std_U) @@ pi) @@ phi;
   end if;
  end for; 
 else
  part := MinimalPartitions(G);
  for a in part do
   phi := Action(G,a);
   if phi(G) ne phi(U) then
    std,pi := StandardGroup(phi(G));
    std_U := pi(phi(U));
    return (FindResolventGroup(std,std_U) @@ pi) @@ phi;
   end if;
  end for;
  part := SetToSequence(AllPartitions(G));
  Sort(~part, func<a,b| #a - #b>);
  for a in part do
   s1 := Stabilizer(G,a); u1 := s1 meet U;
   phi := Action(s1,GSet(s1,a));
   if phi(s1) ne phi(u1) then
    std,pi := StandardGroup(phi(s1));
    std_U := pi(phi(u1));
    return (FindResolventGroup(std,std_U) @@ pi) @@ phi;
   end if;
  end for;
 end if;

// Search in abelian quotient first
 g1 := sub<G | U, DerivedSubgroup(G)>;
 if g1 ne G then
  pd := PrimeDivisors(Index(G,g1));
  p := pd[1];
  g1 := sub<G | g1, [a^p : a in GeneratorsSequence(G)]>;
  assert g1 ne G;
  gen := GeneratorsSequence(G);
  for i := 1 to #gen do
   if IsPrime(Index(G,g1)) then return g1; end if;
   g1 := sub<G | g1, gen[i]>;
  end for;
 end if;   
 while g1 ne G do
  if IsPrime(Index(G,g1)) then return g1; end if;
 end while; 

// No index 2 subgroup will solve the problem!
 lim := 3;
 repeat
  ugv := LowIndexSubgroups(G,<lim, 2*lim - 1>);
  hl := [CosetAction(G,u) : u in ugv];
  ugv := [ugv[j] : j in [1..#ugv] | not IsTransitive(hl[j](U))];
  lim := 2 * lim;
 until #ugv gt 0;
 t1 := [u : u in ugv | not IsTransitive(u)];
// Chose a group with an invariant as simple as possible
 if #t1 gt 0 then  
  orbs := [#Orbits(u) : u in t1];
  m := Max(orbs);
  ugv := [t1[i] : i in [1..#t1] | orbs[i] eq m]; 
 else
  pal := [#AllPartitions(u) : u in ugv];
  m := Max(pal);
  ugv := [ugv[i] : i in [1..#ugv] | pal[i] eq m];
 end if;
 return ugv[1];   
end function;

// The polynomial we work with (internally). I.e. GaloisRoot will return its roots.
function NormalizedPolynomial(S)
 f := S`f;
 if not assigned S`Scale then return f; end if;
 R := Parent(f);
 co := Coefficients(f);
 co := [co[i]* ((S`Scale)^(#co-i)) : i in [1..#co]];
 f := Polynomial(co);
 f := f div LeadingCoefficient(f);
 return f;
end function;

// U is a proper subgroup of Sym(n) and not Alt(n) searches for the smalles reducible k-set-resolvent. k=-1 => No such resolvent
function SearchSetSize(U)
 k := 2;
 n := Degree(U);
 repeat
  if Binomial(n,k) ne #Orbit(U,{1..k}) then
   return k;
  end if; 
  k := k + 1;
 until 2*k ge n;
 return -1; 
end function;

/* Proof Galois group to data S is contained in G. 
   A starting group can be supplied. If not we take S_n. */
function NewGaloisProof(G,S:G_start := false)
 if G_start cmpeq false then
  G0 := Sym(Degree(G));
 else
  G0 := G_start;
 end if;
 f := NormalizedPolynomial(S); 
 if (not G0 subset Alt(Degree(f))) and (G subset Alt(Degree(f))) then 
  if IsSquare(Discriminant(f)) then G0 := Alt(Degree(f)) meet G0; 
                               else return false; 
  end if;
 end if;
 if G eq G0 then
  return true;
 end if;
 if not assigned S`KnownSubgroup then
  S`KnownSubgroup := sub<Sym(Degree(f)) | get_frobenius(S, Degree(f))>;
 end if;

 if not S`KnownSubgroup subset G then
  vprintf GaloisGroup,1:"Group does not contain the known subgroup\n";
  return false;
 end if;
 vprintf GaloisGroup,1:"Starting proof with group of order %o\n",Order(G0);
 n := SearchSetSize(G);
 if n gt 1 then
  G00 := ProofStepBySetResolvent(G0, G, f, S, n); 
  if G00 cmpeq false then 
    vprintf GaloisGroup,1: "Group disproved by inspection of %o-set resolvent\n", n;
    return false; 
  end if;
  if G00 ne G0 then
   vprintf GaloisGroup,1:"Inspection of %o-set resolvent reduced to group of order %o\n",n,Order(G00);
  end if;
  G0 := G00;
 end if;

// Try to use set resolvents for the tower situation:
 if IsTransitive(G0) then
  part := AllPartitions(G0);
  for akt in part do

   if #akt * 6 le Degree(G0) then 
    phi := Action(G0, Orbit(G0,part));
    bg := Image(phi);
    std,pi := StandardGroup(bg);
    kk := Degree(std);
    if (Alt(kk) subset std) and (not Alt(kk) subset pi(phi(G))) then
     n := SearchSetSize(pi(phi(G)));
     if n gt 1 then
      G00 := ProofStepBySubfieldSetResolvent(G0, G, f, S, n, akt);      
      if G00 cmpeq false then 
       vprintf GaloisGroup,1: "Group disproved by inspection of %o-set resolvent of subfield\n", n;
       return false; 
      end if;
      G0 := G00;
     end if;
    end if;
   end if;

   if #akt ge 6 then
    s_B_G0 := Stabilizer(G0,akt);
    phi := Action(s_B_G0, GSet(s_B_G0,akt));
    s_B_G := Stabilizer(G,akt);
    std,pi := StandardGroup(Image(phi));  
    kk := Degree(std);
    if (Alt(kk) subset std) and (not Alt(kk) subset pi(phi(s_B_G))) then
     n := SearchSetSize(pi(phi(s_B_G)));
     if n gt 1 then
      G00 := ProofStepByTowerSetResolvent(G0,G,f,S,n,akt);
      if G00 cmpeq false then
       vprintf GaloisGroup,1: "Group disproved by inspection of relative %o-set resolvent\n", n;
       return false;
      end if;
      if G0 ne G00 then
       vprintf GaloisGroup,1: "Inspection of relative %o-set resolvent reduced to group of order %o\n",n, Order(G00);
      end if;
      G0 := G00;
     end if;    
    end if;
   end if;
  end for; 
 end if;

 while Order(G0) gt Order(G) do
  U_res := FindResolventGroup(G0,G);
  assert not IsTransitive(CosetAction(G0,U_res)(G));
  vprintf GaloisGroup,1: "Inspecting resolvent of degree %o\n", Index(G0,U_res);
  G00 := ProofStepGeneral(G0, G, S, U_res);
  if G00 cmpeq false then 
   vprintf GaloisGroup,1: "Group disproved by inspection of general degree %o resolvent\n", Index(G0,U_res);
   return false; 
  end if;
  vprintf GaloisGroup,1:"Inspection of general degree %o resolvent reduced to group of order %o\n",Index(G0,U_res), Order(G00);
  assert G00 ne G0;
  G0 := G00;
 end while;
 return true;
end function;

/* intrinsic MyResolvent(S::GaloisData, G :: GrpPerm, U :: GrpPerm) -> RngUPolElt
{Compute a resolvent}
 return  BuildResolvent(S,G,U);
end intrinsic; */
 

/* Call the new proof algorithm. We ignore most of the descent chain information.
   This code can handle reducible and irreducible polynomials but only p-adic Galois-Data. */
intrinsic GaloisProof(f::RngUPolElt, S::GaloisData:Level := 0) -> BoolElt
  {Verifies the descent steps of the Stauduhar method that were not proven during the computation.}

 if (assigned S`DescentChain) and (&and [a[2] : a in S`DescentChain]) then
  vprint GaloisGroup, 1: "All steps were proven";
  return true;
 end if;

 if S`Type ne "p-Adic" then
  error"Galois proof for this type not implemented\n";
 end if;

 res := NewGaloisProof(S`DescentChain[#S`DescentChain][1],S);
 if res  then 
  for i := 1 to #S`DescentChain do  
   S`DescentChain[i][2] := true;
  end for;
 end if; 
 return res;

/*
  if Level eq 0 then
    x := Position([y[2] : y in S`DescentChain], false);
    if x eq 0 then
      vprint GaloisGroup, 1: "All steps were proven";
      return true;
    end if;
    assert x ge 2;
    Level := x;
    G := S`DescentChain[x-1][1];
    H := S`DescentChain[#S`DescentChain][1];
  else
    if S`DescentChain[Level][2] then
      vprint GaloisGroup: "Step ", Level, " already checked";
      return true;
    end if;
    G := S`DescentChain[Level][1];
    x := Level-1;
    H := S`DescentChain[x][1];
  end if;

  n := Degree(f);
  m := 1;
  O := 1;
  repeat
    m +:= 1;
    mG, OG := CheckMSets(G, m);
    mH, O := CheckMSets(H, m);
  until mG ne mH;

  vprintf GaloisGroup, 1: "Groups can be distinguished on %o sets\n", m;
  vprintf GaloisGroup, 2: "for G we get: %o\n", mG;
  vprintf GaloisGroup, 2: "and for H   : %o\n", mH;

  use := false;
  for i in O do
    if i notin OG then
      if use cmpeq false or #i lt #use then
        use := i;
      end if;
    end if;
  end for;

  vprintf GaloisGroup, 3: "using orbit %o...\n", use;

  vprint GaloisGroup, 1: "Computing factor mod p...";
  vprint GaloisGroup, 2: "Roots...";
  vtime GaloisGroup, 2: r := [GaloisRoot(i, S: Prec := 1) : i in [1..n]];
  R := ResidueClassField(Universe(r));
  ChangeUniverse(~r, R);

  t := 0;
  vprint GaloisGroup, 1: "Computing MSetPol...", m;
  repeat
    vtime GaloisGroup, 1: F := MSetPolynomial(Evaluate(f, Polynomial([t, 1])), m);
    if IsSquarefree(Polynomial(R, F)) then
      break;
    end if;
    t +:= 1;
    if t gt 10 then
      error "Error: Too many transforms for MSetPol - maybe need different kind of them?";
    end if;
    vprint GaloisGroup, 2: "MSetPol not squarefree, trying substitution";
  until false;

  vprint GaloisGroup, 2: "Factors...";
  vtime GaloisGroup, 2: 
               lf := [ Polynomial([-&* [ r[i]-t : i in u], 1]) : u in use];
  vprint GaloisGroup, 2: "Product...";
  vtime GaloisGroup, 2: q1 := &* lf;

  vprint GaloisGroup, 1: "Computing cofactor...";
  vtime GaloisGroup, 2: f, q2 := IsDivisibleBy(Polynomial(R, F), q1);
  assert f;

  vprint GaloisGroup, 1: "Computing bounds...";
  B := 2^#O*Sqrt(Degree(F)+1)*Maximum([Abs(x) : x in Eltseq(F)]);
  B := Ceiling(B);

  prec := Ilog(S`Prime, 2*B);
  vprint GaloisGroup, 1: "using precision bound ", prec, "for lifting";
  R := BaseRing(S`Ring);
  R := ChangePrecision(R, prec);
  FL := Polynomial(R, F);
  fl, qq1 := IsCoercible(Parent(FL), q1);
  if not fl then
    vprint GaloisGroup, 1: "Factorisation is not over BaseRing";
    return false;
  end if;
  fl, qq2 := IsCoercible(Parent(FL), q2);
  if not fl then
    vprint GaloisGroup, 1: "Factorisation is not over BaseRing";
    return false;
  end if;
  L := [ qq1, qq2];

  vprint GaloisGroup, 1: "Lifting...";
  vtime GaloisGroup, 1: L := HenselLift(FL, L);
  q1 := L[1];

  vprint GaloisGroup, 2: "Checking coefficients...";
  q1 := Eltseq(q1);
  Q1 := [];
  for i in q1 do
    fl, p := IsInt(S`Ring!BaseRing(S`Ring)!i, B, S);
    if not fl then
      vprint GaloisGroup, 1: "Coefficient too large...";
      return false;
    end if;
    Append(~Q1, p);
  end for;

  vprint GaloisGroup, 1: "Final division...";
  Q1 := Polynomial(Q1);
  vtime GaloisGroup, 1: fl := IsDivisibleBy(F, Q1);
 
  S`DescentChain[Level][2] := true;

  return fl; */
end intrinsic;    

    
