freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//                   NONFUNDAMENTAL KERNEL GROUPS                 //
//                          David Kohel                           //
//                     Last modified April 2000                   //
//                                                                //
////////////////////////////////////////////////////////////////////

// intrinsics: ClassGroup, FundamentalKernel 

import "abelian_groups.m" : GeneratedSubgroup;

forward RingClassGroupKernel, RingClassMap;
forward RingClassUnitGroup; 
forward RingClassLocalUnitGroup, RingClass2LocalUnitGroup;
forward RingClassUnit, CyclotomicUnitMod; 
forward RamifiedModlog, SplitModlog, InertModlog;
forward RamifiedMod2log, SplitMod2log, InertMod2log;
forward CyclotomicMod2log, CyclotomicMod3log;
forward Modquo, Modlog;
 
IntNorm := func< x | Integers()!Norm(x) >;
IntTrace := func< x | Integers()!Trace(x) >;

intrinsic ClassGroupStructure(Q::QuadBin : FactorBasisBound := 0.1, ProofBound := 6.0, ExtraRelations := 1, Al := "Automatic") -> SeqEnum
   {The sequence of invariants of the abelian class group of Q.}
    require ISA(Type(FactorBasisBound), FldReElt) :
			"FactorBasisBound must be a FldReElt";
    require ISA(Type(ProofBound), FldReElt) : "ProofBound must be a FldReElt";
    require ISA(Type(ExtraRelations), RngIntElt) :
					"ExtraRelations must be a RngIntElt";
    require Al in {"Automatic", "ReducedForms", "Relations", "Shanks", "Sieve", "NoSieve"}:
        "Al must be one of Automatic, ReducedForms, Relations, Shanks, Sieve or NoSieve";

   return Invariants(ClassGroup(Q : FactorBasisBound := FactorBasisBound, ProofBound := ProofBound, ExtraRelations := ExtraRelations, Al := Al));
end intrinsic;

forward class_group;

intrinsic ClassGroup(Q::QuadBin : FactorBasisBound := 0.1, ProofBound := 6.0, ExtraRelations := 1, Al := "Automatic") -> GrpAb, Map
    {The abelian class group of Q, followed by the isomorphism to Q.}
    require ISA(Type(FactorBasisBound), FldReElt) :
			"FactorBasisBound must be a FldReElt";
    require ISA(Type(ProofBound), FldReElt) : "ProofBound must be a FldReElt";
    require ISA(Type(ExtraRelations), RngIntElt) :
					"ExtraRelations must be a RngIntElt";
    require Al in {"Automatic", "ReducedForms", "Relations", "Shanks", "Sieve", "NoSieve"}:
        "Al must be one of Automatic, ReducedForms, Relations, Shanks, Sieve or NoSieve";

    pi := FundamentalQuotient(Q);
    G, g := FundamentalClassGroup(Codomain(pi) : FactorBasisBound := FactorBasisBound, ProofBound := ProofBound, ExtraRelations := ExtraRelations, Al := Al);
    return class_group(Q, pi, G, g);
end intrinsic;

function class_group(Q, pi, G, g)
    H, h := FundamentalKernel(Q);  
    m := #H; 
    n := #G;
    t := GCD(m,n);
    if t eq 1 then
	E,_,_,p1,p2 := DirectSum(H,G);   
	gens := [ h(p1(E.i))*(g(p2(m*E.i))@@pi)^m : i in [1..Ngens(E)] ]; 
	return E, hom< E -> Q | x :-> 
	    &*[ Q | gens[i]^c[i] : i in [1..Ngens(E)] ]
	        where c is Eltseq(x) >;
    end if;
    m0 := t;
    m1 := m div t; 
    n0 := t;
    n1 := n div t; 
    t := GCD(m0,m1);
    while t ne 1 do
	m0 *:= t;
	m1 div:= t;
	t := GCD(m0,m1);
    end while;
    t := GCD(n0,n1);
    while t ne 1 do
	n0 *:= t;
	n1 div:= t;
	t := GCD(n0,n1);
    end while;
    // First compute the coprime parts.
    G1 := sub< G | [ n0*G.i : i in [1..Ngens(G)] ] >;
    ggens1 := [ (g(G!G1.j)@@pi)^((n*m) div n1) : j in [1..Ngens(G1)] ]; 
    g1 := hom< G1 -> Q | x :-> 
       &*[ Q | ggens1[j]^c[j] : j in [1..Ngens(G1)] ]  where c is Eltseq(x) >;
    H1 := sub< H | [ m0*H.i : i in [1..Ngens(H)] ] >;
    hgens1 := [ h(H!H1.j) : j in [1..Ngens(H1)] ]; 
    h1 := hom< H1 -> Q | x :-> 
       &*[ Q | hgens1[j]^c[j] : j in [1..Ngens(H1)] ]  where c is Eltseq(x) >;
    E1,_,_,p1,p2 := DirectSum(H1,G1);   
    egens1 := [ h1(p1(E1.i))*g1(p2(E1.i)) : i in [1..Ngens(E1)] ]; 
    e1 := hom< E1 -> Q | x :-> 
       &*[ Q | egens1[i]^c[i] : i in [1..Ngens(E1)] ]  where c is Eltseq(x) >;
    // Now compute the possibly nontrivial group extension.
    G2 := sub< G | [ n1*G.i : i in [1..Ngens(G)] ] >;
    ggens2 := [ (g(G!G2.j)@@pi)^m1 : j in [1..Ngens(G2)] ]; 
    H2 := sub< H | [ m1*H.i : i in [1..Ngens(H)] ] >;
    hgens2 := [ h(H!H2.j) : j in [1..Ngens(H2)] ]; 
    E2, e2 := GeneratedSubgroup(ggens2 cat hgens2,m0*n0);  
    // And put them together.
    E,_,_,p1,p2 := DirectSum(E1,E2);   
    egens := [ e1(p1(E.i))*e2(p2(E.i)) : i in [1..Ngens(E)] ]; 
    e := hom< E -> Q | x :-> 
      &*[ Q | egens[i]^c[i] : i in [1..Ngens(E)] ]  where c is Eltseq(x) >;
    assert #E eq #G*#H;
    return E, e;  
end function;

intrinsic PicardGroup(R::RngQuad : FactorBasisBound := 0.1, ProofBound := 6.0, ExtraRelations := 1, Al := "Automatic") -> GrpAb, Map
{Class group of non maximal quadratic orders and a map from the group to the ideals of R}

    require ISA(Type(FactorBasisBound), FldReElt) :
			"FactorBasisBound must be a FldReElt";
    require ISA(Type(ProofBound), FldReElt) : "ProofBound must be a FldReElt";
    require ISA(Type(ExtraRelations), RngIntElt) :
					"ExtraRelations must be a RngIntElt";
    require Al in {"Automatic", "ReducedForms", "Relations", "Shanks", "Sieve", "NoSieve"}:
        "Al must be one of Automatic, ReducedForms, Relations, Shanks, Sieve or NoSieve";

    G, g := ClassGroup(MaximalOrder(R) : FactorBasisBound := FactorBasisBound, ProofBound := ProofBound, ExtraRelations := ExtraRelations, Al := Al); 
    Q := QuadraticForms(Discriminant(R));
    pi := FundamentalQuotient(Q);
    g := map<G -> Codomain(pi) | x :-> QuadraticForm(g(x))>;
    G, m := class_group(Q, pi, G, g);
    ideal_map := map<G -> PowerIdeal(R) | g :-> Ideal(m(g))>;

    return G, ideal_map;
end intrinsic;

intrinsic FundamentalKernel(Q::QuadBin) -> GrpAb, Map
    {The kernel of the fundamental quotient of Q.}
    D := Discriminant(Q); 
    m := Conductor(Q);
    P := PolynomialRing(Integers());
    DK := D div m^2;
    t := DK mod 2;
    n := (t - DK) div 4;
    R := MaximalOrder(NumberField(P.1^2-t*P.1 + n));
    G, f := RingClassGroupKernel(R,m);
  //G, f := RingClassUnitGroup(R,m); // see comment below
    h := RingClassMap(R,m,Q);
    gens := [ Q | h(f(G.i)) : i in [1..Ngens(G)] ];
    u := hom< G->Q | x :-> &*[ Q | gens[i]^c[i] 
              : i in [1..Ngens(G)] ]  where c is Eltseq(x) >;
    return G, u;
end intrinsic;


// June 2012, SRD
// What happened here: David's code gave some runtime errors 
// (eg discriminants 24*9^2, -84*45^2) and wrong answers 
// (eg discriminants 5*16^2, 12*8^2, maybe always positive).
// In 2010, Claus tried to fix something by replacing one of the
// functions below with a call to RayResidueRing, but this was wrong
// (because did not quotient the RayResidueRing by scalars).
// I'm now replacing David's RingClassUnitGroup for the relative 
// part of the ring class group with RingClassGroupKernel,
// although the call to RayResidueRing here is actually slower 
// than David's meticulous hand-crafted package code.

function RingClassGroupKernel(R, m)
   // Given a maximal quadratic order R and an integer m,
   // this returns   
   //   (R/m)* / (Z/m)* / units 
   // as an abstract group with a map to R

   assert AbsoluteDegree(R) eq 2 and IsMaximal(R);

   Rm, _Rm := RayResidueRing(m*R);

   // scalars
   Z := Integers();
   Zm, _Zm := MultiplicativeGroup(Integers(m));
   scalars := [Rm| (R!Z!(z @ _Zm)) @@ _Rm : z in Generators(Zm)];

   // units
   D := Discriminant(R); 
   if D lt -4 then
       units := [Rm| ];
   elif D lt 0 then
       U, _U := TorsionUnitGroup(R);
       units := [Rm| U.1 @ _U @@ _Rm];
   else
       U, _U := UnitGroup(R);
       units := [Rm| U.2 @ _U @@ _Rm];
   end if;
   
   G, _G := quo< Rm | scalars, units >;
   h := Inverse(_G) * _Rm;  // Map G -> R

   return G, h;
end function;

function RingClassMap(R,m,Q)
   // The map to the kernel of the class group of conductor 
   // m from R, inducing a homomorphism from (R/mR)^*

   w := Basis(R)[2];
   t := IntTrace(w);
   n := IntNorm(w);
   return map< R -> Q | x :-> Reduction(Q![ 
        X[1,1]^2 + t*X[1,1]*X[1,2] + n*X[1,2]^2, 
        t*X[1,1]*X[2,2] + 2*n*X[1,2]*X[2,2], n*X[2,2]^2 
        where X is EchelonForm( RMatrixSpace(Integers(),3,2) ! 
              &cat[ Eltseq(x), [ m, 0 ], [ 0, m ] ] ) ]) >;
end function;





///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
//  The rest of the file is obselete
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function RingClassUnitGroup(R,m)
   // The unit group mapping to the kernel of the ideal class 
   // group of the quadratic maximal order R from the ideal class
   // group of the order of conductor m.}

   if m eq 1 then
      G := AbelianGroup([]);
      return G, hom< G->R | x :-> 1 >;
   end if;
   grps := [ ];
   maps := [PowerStructure(Map)| ];
   elts := [ ];
   u := RingClassUnit(R);
   fact := Factorization(m);
   for p in fact do
       if p[1] eq 2 then
	   Gp, fp, xp := RingClass2LocalUnitGroup(R,p[2],u);
       else
	   Gp, fp, xp := RingClassLocalUnitGroup(R,p[1]^p[2],u);
       end if;
       Append(~grps,Gp); 
       Append(~maps,fp);
       Append(~elts,Eltseq(xp)); 
   end for;
   exps := &cat[ [ Order(Gp.i) : i in [1..Ngens(Gp)] ] : Gp in grps ]; 
   G := AbelianGroup(exps);
   Q := ideal< R | m >;
   gens := [ R | ];
   one := [ R | 1 : i in [1..#fact] ];
   mods := [ ideal< R | p[1]^p[2] > : p in fact ]; 
   for j in [1..#fact] do
      Gp := grps[j];
      fp := maps[j];
      for i in [1..Ngens(Gp)] do
         crtgen := one; 
         crtgen[j] := fp(Gp.i);
         Append(~gens,CRT(crtgen,mods));
      end for;
   end for;
   u0 := G!&cat(elts);
   H, pi := quo< G | u0 >;
   hgens := [ &*[ Modexp(gens[k],c[k],m) : k in [1..Ngens(G)] ] mod Q 
	    where c is Eltseq(H.j@@pi) : j in [1..Ngens(H)] ];
   f := map< H->R | x:-> 
      &*[ Modexp(hgens[j],c[j],m) : j in [1..Ngens(H)] ] mod Q 
            where c is Eltseq(x) >;
   return H, f;
end function;

function RingClassLocalUnitGroup(R,q,e)
   _, p, r := IsPrimePower(q);
   D := Discriminant(R);
   Q := ideal< R | q >;
   if KroneckerSymbol(D,p) eq 0 then
      P := Factorization(ideal<R|p>)[1][1];
      if p eq 3 and r gt 1 and D mod 27 eq 24 then
         G := AbelianGroup([p,p^(r-1)]);
         //CF: the above example creates a group with more than
         //2 generators.
         U :=  [  CyclotomicUnitMod(3,P,r),
                     1 + 3*UniformizingElement(P) ];
         f := map< G->R | x:-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) 
                   : i in [1,2] ] mod Q >; 
         x := CyclotomicMod3log(f,e,P,r);
         return G, f, x;
      else
         G := AbelianGroup([p^r]);
      end if;
      u := 1 + UniformizingElement(P);
      f := map< G->R | x:-> Modexp(u,Eltseq(x)[1],p^r) >; 
      x := RamifiedModlog(f,e,P,r);
      return G, f, x;
   elif KroneckerSymbol(D,p) eq 1 then
      F := Factorization(ideal<R|p>);
      P1 := F[1,1]; P2 := F[2,1]; 
      u := CyclotomicUnitMod(p-1,P1,r);
      U := [ CRT([R|u,1],[P1^r,P2^r]) ];
      if r eq 1 then
         u1 := CRT([R|u,1],[P1^r,P2^r]);
         G := AbelianGroup([p-1]);
         f := map< G->R | x:-> Modexp(u1,Eltseq(x)[1],p^r) >; 
      else
         U := [ CRT([R|u,1],[P1^r,P2^r]), 
                CRT([R!1+p,1],[P1^r,P2^r]) ];  
         G := AbelianGroup([p-1,p^(r-1)]);
         f := map< G->R | x:-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) 
                   : i in [1,2] ] mod Q >; 
      end if;
      x := SplitModlog(f,e,P1,P2,r);
      return G, f, x;
   else 
      P := ideal< R | p >;
      U := [ CyclotomicUnitMod(p^2-1,P,r) ];
      if r gt 1 then
         G := AbelianGroup([p+1,p^(r-1)]);
         U cat:= [ 1 + p*R![0,1] ];
      else 
         G := AbelianGroup([p+1]);
      end if;
      f := map< G->R | x:-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) 
                : i in [1..Ngens(G)] ] mod Q >; 
      x := InertModlog(f,e,p,r);
      return G, f, x;
   end if;
end function;

function RingClass2LocalUnitGroup(R,r,e)
   p := 2;
   D := Discriminant(R);
   Q := ideal< R | 2^r >;
   if KroneckerSymbol(D,p) eq 0 then
      P := Factorization(ideal<R|p>)[1][1];
      if r gt 1 and D mod 16 eq 12 then
         G := AbelianGroup([p,p^(r-1)]);
         U :=  [ CyclotomicUnitMod(4,P,r), 1 + 2*UniformizingElement(P) ];
         f := map< G->R | x:-> &*[ Modexp(U[i],Eltseq(x)[i],p^r) 
                   : i in [1,2] ] mod Q >; 
         x := CyclotomicMod2log(f,e,r);
         return G, f, x;
      else // D mod 16 eq 8 
         G := AbelianGroup([p^r]);
      end if;
      pi := UniformizingElement(P);
      G := AbelianGroup([p^r]);
      f := hom< G->R | x :-> Modexp((1 + pi),Eltseq(x)[1],p^r) >;
      x := RamifiedMod2log(f,e,r);
      return G, f, x;
   elif KroneckerSymbol(D,p) eq 1 then
      if r eq 1 then
         G := AbelianGroup([]);
         f := map< G->R | x:-> R!1 >; 
         x := G!0;
      elif r eq 2 then
         fact := Factorization(ideal<R|p>);
         P1 := fact[1,1]; P2 := fact[2,1]; 
         u := CRT([R|-1,1],[P1^2,P2^2]);
         G := AbelianGroup([2]);
         f := map< G->R | x :-> Modexp(u,Eltseq(x)[1],p^2) mod Q >; 
         x := SplitMod2log(f,e,P1,P2,r);
      else
         fact := Factorization(ideal<R|p>);
         P1 := fact[1,1]; P2 := fact[2,1]; 
         u1 := CRT([R|-1,1],[P1^r,P2^r]);
         u2 := CRT([R|1+4,1],[P1^r,P2^r]);
         G := AbelianGroup([2,2^(r-2)]);
	 f := map< G->R | x :-> (Modexp(u1,c[1],p^r) mod Q) *
       	           (Modexp(u2,c[2],p^r) mod Q) where c := Eltseq(x) >; 
         x := SplitMod2log(f,e,P1,P2,r);
      end if;
      return G, f, x;
   else 
      P := ideal< R | p >;
      w := CyclotomicUnitMod(3,P,r);
      if r eq 1 then
	  G := AbelianGroup([3]);
	  U := [ w ];
      elif r eq 2 then
	  G := AbelianGroup([3,2]);
	  U := [ w, 1 + 2*w ];
      else 
	  G := AbelianGroup([3,2,2^(r-2)]);
	  U := [ w, 1 + 2*w, 1 + 4*w ];
      end if;
      f := map< G->R | x:-> &*[ Modexp(U[i],c[i],p^r) :
                i in [1..Ngens(G)] ] mod Q where c := Eltseq(x) >; 
      x := InertMod2log(f,e,r);
      return G, f, x;
   end if;
end function;

function RingClassUnit(R)
   // A generator of the cyclic group R^*/<-1>.
   D := Discriminant(R);
   if D lt 0 then
      if D eq -3 then
         return R![0,1];      
      elif D eq -4 then
         return R![0,1];      
      end if;
      return R!1;
   end if;
   U, m := UnitGroup(R);
   return m(U.2);
end function;

function CyclotomicUnitMod(t,P,r)
   // A P-adic t-th root of unity, computed modulo P^r.

   R := Order(P);
   if t eq 1 then
      return R!1;
   elif t eq 2 then
      return R!-1;
   elif t eq 3 and Norm(P) eq 3 then
      R := Order(P);
      assert Discriminant(R) mod 27 eq 24;
      z0 := ((IntTrace(R![0,1])) div 2) - R![0,1]; 
      if r le 3 then
         return z0;
      end if;   
   elif t eq 4 and Norm(P) eq 2 then
      R := Order(P);
      assert Discriminant(R) mod 16 eq 12;
      z0 := R![0,1];
      z0 -:= (IntTrace(z0)) div 2; 
      if r le 5 then
         return z0;
      end if;   
   else
      FF, proj := ResidueClassField(P);
      z0 := (PrimitiveElement(FF)^((#FF - 1) div t))@@proj;
   end if;
   Q := P^r;
   q := IntNorm(P)^r;
   while true do;
      a0 := Modexp(z0,t-1,q) mod Q;
      c0 := (a0*z0-1) mod Q;
      if c0 eq 0 then break; end if; 
      z0 +:= -Modquo(c0,t*a0,Q);
   end while;
   return z0;
end function;

function SplitModlog(f,e,P1,P2,r)
   // The discrete log pullback of a unit with respect to
   // the isomorphism f: G -> (R/p^r)^*, where (p) = P1*P2.

   G := Domain(f);
   R := Codomain(f);
   F, pi1 := ResidueClassField(P1);
   F, pi2 := ResidueClassField(P2);
   u0 := f(G.1);
   n0 := Log(pi1(u0)/pi2(u0),pi2(e)/pi1(e));
   if r eq 1 then
      return G![n0];
   end if;
   c1 := Eltseq((u0^n0*e) mod P1^r);
   c2 := Eltseq((u0^n0*e) mod P2^r);
   assert c1[2] eq 0 and c2[2] eq 0; 
   p := #F;
   ZZ := Integers();
   a1 := ZZ!c1[1]*Modinv(ZZ!c2[1],p^r) mod p^r;
   n1 := Modlog(1+p,a1,p^r);
   return G![-n0,n1];
end function;

function InertModlog(f,e,p,r)
   // The discrete log pullback of the unit e with respect 
   // to the isomorphism f: G -> (R/P^r)^*/(Z/pZ)^*, with
   // (p) prime.

   G := Domain(f);
   u0 := f(G.1);
   F, pi := ResidueClassField(ideal< Codomain(f) | p >);
   n0 := Log(pi(u0),pi(e));
   if r eq 1 then
      return G![n0];
   end if;
   n1 := 0;
   u1 := f(G.2);

   V := RSpace(GF(p),2);
   MatF := MatrixAlgebra(GF(p),2);
   e1 := e*Modinv(Modexp(u0,n0,p^r),p^r);
   ZZ := Integers();
   e1 *:= ZZ!Eltseq(e1)[1]; 
   for i in [1..r-1] do
      v0 := V![ (ZZ!x) div p^i : x in Eltseq(e1-1) ];
      M := MatF!( [ (ZZ!x) div p^i : x in Eltseq(u1-1) ] cat [ 1, 0 ] );
      v1 := v0*M^-1;  
      m1 := ZZ!v1[1]; 
      m2 := ZZ!v1[2];
      n1 +:= m1*p^(i-1);
      if i eq r-1 then break i; end if;
      e1 *:= Modinv(Modexp(u1,m1,p^r),p^r);
      e1 *:= Modinv(Modexp(1+p^i,m2,p^r),p^r);
      u1 := Modexp(u1,p,p^r); 
   end for;
   return G![n0,n1];
end function;

function RamifiedModlog(f,e,P,r)
   // The discrete log pullback of the unit e with respect to 
   // the isomorphism f: G -> (R/P^r)^*, with (p) = P^2.

   G := Domain(f);
   // CF: the if seems to be neccessary, otherwise the example fails:
   //Q:=BinaryQuadraticForms(-4*790+1);
   //ClassGroup(Q);
   // sice u1 becomes 1 which means the Modquo tries to devide by 0
   if e eq 1 then
     return G.0;
   end if;
   n1 := 0;
   u1 := f(G.1);
   e1 := (e mod P)*e;
   p := IntNorm(P);
   ZZ := Integers();
   for i in [1..r] do
      e1 *:= Modinv(ZZ!Eltseq(e1 mod P^(2*i-1))[1],p^i);
      m1 := ZZ!Eltseq(Modquo(e1-1,u1-1,P))[1] mod p;
      n1 +:= m1*p^(i-1);
      if i eq r then break i; end if;
      e1 *:= Modinv(Modexp(u1,m1,p^r),p^r);
      u1 := Modexp(u1,p,p^r);
   end for;
   return G![n1];
end function;

function SplitMod2log(f,e,P1,P2,r)
   // The discrete log pullback of a unit with respect to
   // the isomorphism f: G -> (R/p^r)^*, where (p) = P1*P2.

   ZZ := Integers();
   G := Domain(f);
   if r eq 1 then
      return G!0;
   end if;
   R := Codomain(f);
   c1 := Eltseq(e mod P1^r);
   c2 := Eltseq(e mod P2^r);
   assert c1[2] eq 0 and c2[2] eq 0; 
   a1 := (ZZ!c1[1]*Modinv(ZZ!c2[1],2^r)) mod 2^r;
   n1 := 0;
   if a1 mod 4 eq 3 then
       a1 := (-a1 mod 2^r);
       n1 := 1;
   end if;
   if r eq 2 then return G![n1]; end if;
   return G![n1,Modlog(1+4,a1,2^r)];
end function;

function InertMod2log(f,e,r)
   // The discrete log pullback of the unit e with respect 
   // to the isomorphism f: G -> (R/2^rR)^*/(Z/2^rZ)^*.

   G := Domain(f);
   R := Codomain(f);
   F, pi := ResidueClassField(ideal< R | 2 >);
   u0 := f(G.1);
   n0 := Log(pi(u0),pi(e));
   if r eq 1 then return G![n0]; end if;
   ZZ := Integers();
   u1 := f(G.2);
   e1 := e*Modinv(Modexp(u0,n0,2^r),2^r);
   e1 *:= ZZ!Eltseq(e1)[1]; 
   t0 := (ZZ!Eltseq(e1)[2] div 2) mod 2;
   n1 := t0 eq 1 select 1 else 0;
   if r eq 2 then
       return G![n0,n1];
   end if;
   n2 := 0;
   u2 := f(G.3);
   for i in [1..r-2] do
       t0 := (ZZ!Eltseq(e1)[2] div 2^(i+1)) mod 2;
       if t0 ne 0 then
	   n2 +:= 2^(i-1);
	   if i eq r-2 then break i; end if;
	   e1 *:= Modinv(u2,2^r);
	   e1 *:= Modinv(ZZ!Eltseq(e1)[1],2^r);
       end if;
       u2 := Modexp(u2,2,2^r);
   end for;
   return G![n0,n1,n2];
end function;

function RamifiedMod2log(f,e,r)
   // The discrete log pullback of the unit e with respect to the
   // isomorphism f: G -> (R/P^r)^*/(Z/p^rZ)^*, with (p) = P^2.

   ZZ := Integers();
   G := Domain(f);
   n1 := ZZ!Eltseq(e)[2] mod 2;
   if r eq 1 then return G![n1]; end if; 
   u1 := f(G.1);
   e1 := Modexp(e*Modinv(Modexp(u1,n1,2^r),2^r),1,2^r);
   for i in [2..r] do
      u1 := Modexp(u1,2,2^r);
      m1 := ZZ!Eltseq(e1)[2] mod 2^i;
      n1 +:= m1;
      e1 *:= Modinv(Modexp(u1,m1 div 2^(i-1),2^r),2^r);
   end for;
   return G![n1];
end function;

function CyclotomicMod2log(f,e,r)
   // The discrete log pullback of the unit e with respect 
   // to the isomorphism f: G -> (R/2^r)^*, with (2) = P^2, 
   // in a ring with 4th roots of unity.

   p := 2;
   G := Domain(f);
   if e eq 1 then
      return G!0;
   end if;

   ZZ := Integers();
   u0 := f(G.1);
   n0 := ZZ!Eltseq(e)[2] mod 2;
   e1 := e*Modexp(u0,n0,2^r);
   n1 := 0;
   u1 := f(G.2);
   for i in [2..r] do
      m1 := ZZ!Eltseq(e1)[2] mod 2^i;
      n1 +:= m1;
      e1 *:= Modexp(u1,m1 div 2^(i-1),2^r);
      if i eq r then break i; end if;
      u1 := Modexp(u1,2,2^r);
   end for;
   return G![n0,n1];
end function;

function CyclotomicMod3log(f,e,P,r)
   // The discrete log pullback of the unit e with respect 
   // to the isomorphism f: G -> (R/3^r)^*, with (3) = P^2, 
   // in a ring with 3rd roots of unity.

   p := 3;
   G := Domain(f);
   ZZ := Integers();
   u0 := f(G.1);
   e1 := (e mod P)*e;
   n0 := ZZ!Eltseq(Modquo(e1-1,u0-1,P))[1] mod p;
   e1 *:= Modinv(Modexp(u0,n0,p^r),p^r);
   n1 := 0;
   u1 := f(G.2);
   for i in [2..r] do
      e1 *:= Modinv(ZZ!Eltseq(e1 mod P^(2*i-1))[1],p^i);
      m1 := ZZ!Eltseq(Modquo(e1-1,u1-1,P))[1] mod p;
      n1 +:= m1*p^(i-1);
      if i eq r then break i; end if;
      e1 *:= Modinv(Modexp(u1,m1,p^r),p^r);
      u1 := Modexp(u1,p,p^r);
   end for;
   return G![n0,n1];
end function;

function Modquo(x,y,Q)
   error if y eq 0, "Error: Argument 2 must not be zero";
   if not IsPrime(Q) then
      fact := Factorization(Q);
      if #fact gt 1 then
         ppows := [ fact[i][1]^fact[i][2] : i in [1..#fact] ];
         return CRT( [ Modquo(x,y,Qi) : Qi in ppows ], ppows );
      end if; 
      P := fact[1][1];
   else 
      P := Q;
   end if;
   ZZ := Integers();
   _, p := IsPrimePower(IntNorm(P));
   if x eq 0 then
      return Parent(x)!0;
   end if;
   e1 := Valuation(y,P);
   if e1 eq 0 then
      return x*Modinv(y,Q) mod Q;  
   end if;
   error if e1 gt Valuation(x,P),
      "Error: Valuation of argument 2 must not exceed that of argument 1";
   z := x*(IntTrace(y)-y);
   n := IntNorm(y);
   return Parent(x)!
      [ Modinv(n div p^e1,p)*(ZZ!a div p^e1) : a in Eltseq(z) ] mod Q;
end function;

function Modlog(b,a,m)
   // The modular logarithm n of a = b^n mod m, or -1 
   // if no n exists.  Modulus m must be a prime power.

   yes, p, e := IsPrimePower(m);   
   error if not yes, "Error: Argument 3 must be a prime power";
   error if not b mod p ne 0, 
      "Error: Argument 1 must be coprime to argument 3";
   error if not a mod p ne 0, 
      "Error: Argument 2 must be coprime to argument 3";
   if p eq 2 then
      if e eq 1 then
         return 0;
      elif e eq 2 then
         if a mod 4 eq 1 then
   	    return 0; 
         elif (a mod 4) eq (b mod 4) then
   	    return 1; 
         else
   	    return -1; 
         end if;
      elif (a mod 8 ne 1) and 
         ((a*Modinv(b,8) mod 8) mod m) ne 1 then
         return -1; 
      end if;
   end if;
   a0 := GF(p)!a;
   b0 := GF(p)!b;
   n0 := Log(b0,a0);
   if n0 eq -1 then 
      return -1;
   end if;
   a1 := Modexp(a,p-1,p^e);
   b1 := Modexp(b,p-1,p^e);
   if b1 eq 1 then
      if a1 eq 1 then
         return n0;
      end if;
      return -1;
   end if;
   r := 1;
   d := 0;
   n1 := 0; 
   while r+d lt e do
      br := Modexp(b1,p^(r-1),p^(r+d+1));
      cr := a1*Modexp(b1,-n1,p^(r+d+1)) mod p^(r+d+1);
      sr := (br-1) div p^(r+d);         
      tr := (cr-1) div p^(r+d);         
      while sr eq 0 do
         if tr eq 0 then
       	    d +:= 1; 
            br := Modexp(b1,p^(r-1),p^(r+d+1));
            cr := a1*Modexp(b1,-n1,p^(r+d+1)) mod p^(r+d+1);
            sr := (br-1) div p^(r+d);         
            tr := (cr-1) div p^(r+d);         
         else 
            return -1; 
         end if;
      end while;
      nr := tr*Modinv(sr,p) mod p;
      n1 +:= p^(r-1)*nr;
      r +:= 1;
   end while;
   return CRT([n0,n1],[p-1,p^(e-2+(p mod 2))]);
end function;

