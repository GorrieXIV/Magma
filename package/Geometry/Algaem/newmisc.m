freeze;

/******************************************************************************
 *
 * newmisc.m
 *
 * date:   26/6/2001
 * author: Nils Bruin
 *
 * Some general features that were missing in MAGMA proper.
 *
 ******************************************************************************/

/**
 ** OrderedGenerators
 **
 ** Returns an ordered list of generators rather than a set of them.
 ** Indispensible if you want to loop through them in order (for instance, if
 ** you want to define a homomorphism)
 **/
 
intrinsic OrderedGenerators(L::.)->.
  {patch to get an *ordered* list of generators}
  if Type(L) in {RngUPol,RngMPol,FldFunRat,RngMPolRes} then
    return [L.i:i in [1..Rank(L)]];
  elif Type(L) in {RngInt,FldRat} then
    return [L|];
  elif Type(L) in {RngSerPow,RngSerLaur,RngSerPuis} then
    return [L.1];
  else  
    return [L|L.i:i in [1..Ngens(L)]];
  end if; 
end intrinsic;

/**
 ** SwapExtension
 **
 ** Swaps the topmost two levels of an extension
 **/

function lsrelt(R,v,L,p)
  if p eq 0 then
    return elt<R|v-1,[Universe(L)|0] cat L,p+1>;
  else
    return elt<R|v,L,p>;
  end if;
end function;

intrinsic SwapExtension(R::Rng)->Rng,Map
  {Takes an extension tower and swaps the two topmost extensions}
  if ISA(Type(R),RngUPol) and ISA(Type(BaseRing(R)),RngMPol) then
    K:=BaseRing(R); // this is a multivariate polynomial ring
    k:=BaseRing(K);
    Pk:=PolynomialRing(k);
    RPk:=PolynomialRing(Pk,Rank(K));

    KtoRPk:=hom<K->RPk| Coercion(k,RPk),OrderedGenerators(RPk)>;
    RtoRPk:=hom<R->RPk| KtoRPk, RPk!(Pk.1)>;

    PktoR:=hom<Pk->R| Coercion(k,R), R.1>;
    RPktoR:=hom<RPk->R| PktoR,ChangeUniverse(OrderedGenerators(K),R)>;

    return RPk,map<R->RPk|a:->RtoRPk(a),b:->RPktoR(b)>;
  elif ISA(Type(R),RngUPol) then
    K:=BaseRing(R);
    //assert ISA(Type(K),FldNum);
    k:=BaseField(K);
    Pk:=PolynomialRing(k);
    PkX:=PolynomialRing(Pk);
    if ISA(Type(K),FldNum) then
      h:=Evaluate(DefiningPolynomial(K),PkX.1);
    elif ISA(Type(K),RngUPolRes) then
      h:=Evaluate(Modulus(K),PkX.1);
    else
      error "not supported";
    end if;
    PkK:=quo<PkX|h>;

    KtoPkK:=hom<K->PkK|Coercion(k,PkK),PkK.1>;
    RtoPkK:=hom<R->PkK|KtoPkK, PkK!Pk.1>;

    PktoR:=hom<Pk->R|Coercion(k,R), R.1>;
    PkKtoR:=hom<PkK->R|PktoR, R!(K.1)>;

    return PkK,map<R->PkK|a:->RtoPkK(a),b:->PkKtoR(b)>;
  elif ISA(Type(R),RngMPol) then
    K:=BaseRing(R);
    if ISA(Type(K),FldNum) then
      k:=BaseField(K);
      modulus:=DefiningPolynomial(K);
    elif ISA(Type(K),RngUPolRes) then
      k:=BaseRing(K);
      modulus:=Modulus(K);
    elif ISA(Type(K),RngSerLaur) then
      k:=BaseRing(K);
      Pk:=PolynomialRing(k,Rank(R));
      PkK:=LaurentSeriesRing(Pk);
      KtoPkK:=map<K->PkK|a:->
          (v eq Infinity() select PkK!0 else
            lsrelt(PkK,v,L,RelativePrecision(a)) where L,v:=Eltseq(a))>;
      RtoPkK:=hom<R->PkK|KtoPkK, [PkK!Pk.i: i in [1..Rank(R)]]>;
      
      return PkK, map<R->PkK|a:->RtoPkK(a)>;
    else
      error "Can't do that type yet";
    end if;
    Pk:=PolynomialRing(k,Rank(R));
    PkX:=PolynomialRing(Pk);
    modulus /:= LeadingCoefficient(modulus);
    PkK:=quo<PkX|Evaluate(modulus,PkX.1)>;

    KtoPkK:=hom<K->PkK|Coercion(k,PkK),PkK.1>;
    RtoPkK:=hom<R->PkK|KtoPkK, [PkK!Pk.i: i in [1..Rank(R)]]>;

    PktoR:=hom<Pk->R|Coercion(k,R), [R.i: i in [1..Rank(R)]]>;
    PkKtoR:=hom<PkK->R|PktoR, R!(K.1)>;

    return PkK,map<R->PkK|a:->RtoPkK(a),b:->PkKtoR(b)>;
  elif ISA(Type(R),RngUPolRes) then
    K:=BaseRing(R);
    assert ISA(Type(K),FldNum);
    k:=BaseField(K);
    fR:=Modulus(R);
    Pk:=PolynomialRing(k);
    fk:=Polynomial(k,fR);//the extension must be descendable ...
    Ak:=quo<Pk|fk>;
    AkX:=PolynomialRing(Ak);
    AK:=quo<AkX|Evaluate(DefiningPolynomial(K),AkX.1)>;
    
    KtoAK:=hom<K->AK|Coercion(k,AK),AK.1>;
    RtoAK:=hom<R->AK|KtoAK,AK!(Ak.1)>;
    
    AktoR:=hom<Ak->R|Coercion(k,R), R.1>;
    AKtoR:=hom<AK->R|AktoR, R!(K.1)>;
    
    return AK,map<R->AK|a:->RtoAK(a),b:->AKtoR(b)>;
  else
    error "not implemented";
  end if;  
end intrinsic;

/**
 ** SymmetricMatrix
 **
 ** Given a quadratic form, returns its symmetric matrix
 **/

intrinsic SymmetricMatrix(Q::RngMPolElt)->AlgMatElt
  {Given a quadratic form, return its associated symmetric matrix}
  require IsHomogeneous(Q) and TotalDegree(Q) eq 2:
    "Must be quadratic form";
  R:=Parent(Q);
  return Matrix([[i eq j select MonomialCoefficient(Q,R.i^2) else
                  MonomialCoefficient(Q,R.i*R.j)/2 : i in [1..Rank(R)]]:
              j in [1..Rank(R)]]);
end intrinsic;

/**
 ** PowerFreePart
 **
 ** Return the power free part of a rational number
 **/

intrinsic PowerFreePart(n::FldRatElt,e::RngIntElt)->RngIntElt,RngIntElt
{Returns the e-th power free part of n and an e-th root of the remaining part of
n}
  local R,L,u;
  if n eq 0 then
    return 1,0;
  end if;
  L1,u1:=Factorisation(Numerator(n));
  L2,u2:=Factorisation(Denominator(n));
  u:=u1/u2;
  L:=L1 cat [<l[1],-l[2]>:l in L2];
  if Abs(n) eq 1 then
    R:=[1,1];
  else
    R :=
    [&*{@ u[1]^(u[2] mod e) : u in L @},&*{@ u[1]^(u[2] div e) : u in L @}];
  end if;
  if e mod 2 eq 0 then
    return u*R[1],R[2];
  else
    return R[1],u*R[2];
  end if;
end intrinsic;
