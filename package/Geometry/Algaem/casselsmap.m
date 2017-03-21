freeze;
 
/******************************************************************************
 *
 * casselsmap.m
 *
 * date:   23/12/2003
 * author: Nils Bruin
 *
 * routines to compute the Cassels map and 2-torsors for elliptic curves.
 *
 ******************************************************************************/

declare attributes Map:Algebra,Isogeny_MuTor;
import "selmer.m":IsogenyIsMultiplicationByTwo;

/******************************************************************************
 Compute map mu:E -> A^* and map tor:A^* -> {Covers of E}
 Input:
   E       - The elliptic curve
   Algebra - If set, algebra to map to
   Fields  - If set, used for AbsoluteAlgebra call.
 Return:
   mu   - map cop<K,E> -> A
   tor  - map A^* -> {Covers}
   
 If delta in A^* is of square norm, then tor(delta) returns a cover T->E
 otherwise it returns a cover T->P^1. In both cases, T is an intersection of
 two quadrics in P^3.
 ******************************************************************************/

function CasselsMapECm2(E:Algebra:=false,Fields:=false)
  K:=BaseRing(E);
  f,h:=HyperellipticPolynomials(E);
  F:=f+h^2/4;
  if Algebra cmpne false then
    error if not(F cmpeq Modulus(Algebra)),
      "Algebra must have modulus equal to F";
    A:=Algebra;theta:=A.1;
  else
    A<theta>:=quo<Parent(F)|F>;
  end if;
  if Fields cmpne false then
    Aa,toAa:=AbsoluteAlgebra(A:Fields:=Fields);
  else
    Aa,toAa:=AbsoluteAlgebra(A);
  end if;
  dFtheta:=toAa(Evaluate(Derivative(F),A.1));
  function mumap(P)
    if ISA(Type(P),PtEll) then
      error if Curve(P) cmpne E,"Point must be on the curve";
      if P[3] eq 0 then
        return A!1;
      end if;
      P:=P[1]/P[3];
    end if;
    if Evaluate(F,P) eq 0 then
      v:=toAa(P-A.1);
      bl:=exists(i){i: i in [1..#v]| v[i] eq 0};
      assert bl;
      v[i]:=dFtheta[i];
      return v@@toAa;
    else
      return P-A.1;
    end if;
  end function;
  
  AR:=PolynomialRing(A,4);
  RA,swap:=SwapExtension(AR);
  P3<u0,u1,u2,u3>:=Proj(BaseRing(RA));
  P1<x,z>:=ProjectiveSpace(K,1);
  N:=Norm(swap(&+[AR.i*(A.1)^(i-1):i in [1..3]]));
  a1:=Coefficient(h,1);
  a3:=Coefficient(h,0);
  function tormap(delta)
    Q:=Coefficients(swap(delta*(&+[AR.i*(A.1)^(i-1):i in [1..3]])^2));
    bl,d:=IsSquare(Norm(delta));
    T:=Curve(Scheme(P3,[Q[3],Q[2]+u3^2]));
    if bl then // original seems wrong
H,m1:=AssociatedHyperellipticCurve(T); /* STUPID FIX - MW 20-02-08 */
He,m2:=EllipticCurve(H); b,m3:=IsIsomorphic(He,E); assert b;
m:=Normalisation(Expand(m1*m2*m3)); return m; // Gavin suggests Normalization
      return map<T->E|[-Q[1]*u3^3,d*N*Q[2]+(a1*Q[1]-a3*Q[2])*u3^3,u3^3*Q[2]]>;
    else
      return map<T->P1|[-Q[1],Q[2]]>;
    end if;
  end function;
  
  return map<cop<K,E>->A| u:->mumap(Retrieve(u))>,
         map<A->PowerStructure(MapSch)| delta:->tormap(delta)>;
end function;

/******************************************************************************
 Compute map mu:E -> K^* and map tor:K^* -> {Covers of E}
 associated to a 2-isogeny phi: Ed -> E

 Input:
   phi       - The 2-isogeny
 Return:
   mu   - map cop<K,E> -> A
   tor  - map K^* -> {Covers}
   
 The covering curves are hyperelliptic curves of the form v^2=A*u^4+B*u^2+C
 ******************************************************************************/

function CasselsMapECtwoIso(phi)
  assert Degree(phi) eq 2;
  E:=Codomain(phi);
  K:=BaseRing(E);
  phid:=DualIsogeny(phi);
  x0:=Roots(IsogenyMapPsi(phid))[1][1];
  f,h:=HyperellipticPolynomials(E);
  x:=Parent(f).1;
  a1:=Coefficient(h,1);
  a3:=Coefficient(h,0);
  F:=ExactQuotient(Evaluate(f+h^2/4,x+x0),x);
  B:=Coefficient(F,0);
  function mumap(P)
    if ISA(Type(P),PtEll) then
      error if Curve(P) cmpne E,"Point must be on the curve";
      if P[3] eq 0 then
        return K!1;
      end if;
      P:=P[1]/P[3];
    end if;
    if P eq x0 then
      return B;
    else
      return P-x0;
    end if;
  end function;
  function tormap(delta)
    T<u,v,w>:=HyperellipticCurve(delta*Evaluate(F,delta*x^2));
    return map <T->E | [delta*u^2*w+x0*w^3,u*v-(a1*(delta*u^2*w+x0*w^3)+a3*w^3)/2,w^3]>;
  end function;
  return map<cop<K,E>->K| u:->mumap(Retrieve(u))>,
         map<K->PowerStructure(MapSch)| delta:->tormap(delta)>;
end function;

/******************************************************************************
 User interface, with memory
 ******************************************************************************/

intrinsic DescentMaps(phi::Map:Algebra:=false,Fields:={})->Map,Map
  {Given an isogeny phi : E -> E1 of elliptic curves over a number field K or Q,
  returns the connecting homomorphism E1(K) -> H^1(K, E[phi]), 
  and the map sending an element of H^1(K, E[phi]) 
  to the corresponding homogeneous space for E.
  Implemented for 2-isogenies and the multiplication-by-two isogeny.}
  return CasselsMap(phi : Algebra:=Algebra, Fields:=Fields);
end intrinsic;

intrinsic CasselsMap(phi::Map:Algebra:=false,Fields:={})->Map,Map
  {Given an isogeny phi : E -> E1 of elliptic curves over a number field K or Q,
  returns the connecting homomorphism E1(K) -> H^1(K, E[phi]), 
  and the map sending an element of H^1(K, E[phi]) 
  to the corresponding homogeneous space for E.
  Implemented for 2-isogenies and the multiplication-by-two isogeny.}
  if not assigned(phi`Isogeny_MuTor) then
    if IsogenyIsMultiplicationByTwo(phi) then
      E:=Domain(phi);
      if Algebra cmpne false then
        mu,tor:=CasselsMapECm2(E:Algebra:=Algebra,Fields:=Fields);
      elif assigned phi`Algebra then
        mu,tor:=CasselsMapECm2(E:Algebra:=phi`Algebra,Fields:=Fields);
      else
        mu,tor:=CasselsMapECm2(E:Algebra:=Algebra,Fields:=Fields);
        phi`Algebra:=Codomain(mu);
      end if;
    elif Degree(phi) eq 2 then
      mu,tor:=CasselsMapECtwoIso(phi);
    else
      require false:"Not implemented";
    end if;
    phi`Isogeny_MuTor:=<mu,tor>;
  else
    mu,tor:=Explode(phi`Isogeny_MuTor);
  end if;
  return mu,tor;
end intrinsic;

intrinsic IsogenyMu(phi::Map : Fields:={})->Map,Map
  {Depricated. Use CasselsMap instead.}
  return CasselsMap(phi:Fields:=Fields);
end intrinsic;
