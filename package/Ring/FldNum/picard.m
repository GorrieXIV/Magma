freeze;

/******************************************************************

            RingClassGroup for nonmaximal orders 
       
            Written by Klueners/Pauli 

******************************************************************/



// "Current" was not my choice -- SRD
function cg(O)
    if Type(O) eq RngQuad then
        return ClassGroup(O);
    else
        return ClassGroup(O : Proof := "Current");
    end if;    
end function;



//True if the RngOrdIdl's A and B are coprime
function IsCoprime(A,B)  // -> BoolElt
  if Order(A) ne Order(B) then
    error "IsCoprime: Ideals must be defined over the same order.";
  end if;
  return A+B eq One(Parent(A));
end function;


residue_class_field_primitive_element := function(id)

  rf, phi := ResidueClassField(id);
  pe := PrimitiveElement(rf);
  a := pe @@ phi;
  return a;

end function;


residue_class_ring_unit_subgroup_generators:=function(o, F)
// determine generators of the subgroup of (o/F)^* as elements of om

  om:=MaximalOrder(o);
  Fm:=om !! F;
  l:=Factorization(Fm);
  l2:=[<x[1] meet o,x[2]>: x in l]; 
  primes:={x[1]:x in l2};
  primes:=[<x, Maximum([y[2]: y in l2 |y[1] eq x])>:x in primes];
  elts:={om | };
  for a in primes do
    idp:=a[1];
    rest:=1*o;
    for b in primes do
      if b[1] ne idp then
         rest:=rest*b[1]^b[2];
      end if;
    end for;
    //Compute primitive elt for residue field
    c:=residue_class_field_primitive_element(idp);
    c:=ChineseRemainderTheorem(a[1]^a[2],rest,c,o ! 1);
    c:=om ! c;
    Include(~elts,c);
    b:=1;
    while b lt a[2] do
      min:=Minimum(idp^2);
      M:=Basis(idp);
      M:=[1+x:x in M];
      for elt in M do
        c:=ChineseRemainderTheorem((a[1]^a[2]),rest,elt,o ! 1);
        c:=om ! c;
        Include(~elts,c);
      end for;
      b:=b*2;idp:=idp^2;
    end while;
  end for;
  return elts;
end function;

intrinsic PicardGroup(O::RngOrd) -> GrpAb, Map
{Same as RingClassGroup}
  return RingClassGroup(O);
end intrinsic;

intrinsic RingClassGroup(O::RngOrd) -> GrpAb, Map
{The ideal class group of the order O, which is not required to be a maximal order, 
together with a map from the class group to the set of ideals of O giving 
representative ideals for each class. 
The map has an inverse map, sending an ideal to its ideal class.}

  o := O;
  if IsMaximal(o) then 
    return cg(o);
  end if;

  F := Conductor(o);  
  om := MaximalOrder(o);
  Fm := om!!F;
  C, mC := cg(om);
  H := FreeAbelianGroup(#Generators(C));  
  // find generators of the class group C that are coprime to F
  // build a map from C to these generators
  if Order(C) gt 1 then
    Cgen := [];
    for i in [1..#Generators(C)] do
      cocoeff := CoprimeRepresentative(mC(C.i),Fm);
      Append(~Cgen,cocoeff*mC(C.i));
    end for;
    mCo:= function(rep)
      repseq := Eltseq(rep);
      return &*[Cgen[i]^repseq[i]:i in [1..#Cgen]];
    end function;
  else
    Cgen := [];
    C := FreeAbelianGroup(0);
    mCo:= function(rep) return 1*om; end function;
  end if;
  
  Um, mUm := UnitGroup(om);
  G, mG := RayResidueRing(Fm);
  D, mGD, mHD, mDG, mDH := DirectSum(G,H);
  
  // factor out the multiplicative group of o/F
  ogens := residue_class_ring_unit_subgroup_generators(o,F);
  relDresidue := [mGD(gen@@mG):gen in ogens];
  // glue G and C
  relDglue := [];
  for i in [1..#Cgen] do
    is_princ, gen := IsPrincipal(Cgen[i]^InvariantFactors(C)[i]);
    Append(~relDglue,-mGD(gen@@mG)+mHD(H.i*InvariantFactors(C)[i]));
  end for;
  // relations coming form the unit group
  ugens := [mUm(gen):gen in Generators(Um)];
  relDunits := [mGD(gen@@mG):gen in ugens];

  P, mDP := quo<D|relDresidue cat relDglue cat relDunits>;
  P_gens_in_D := [P.i@@mDP:i in [1..#Generators(P)]]; 
  generators_in_om := [mG(mDG(P_gens_in_D[i]))*om*mCo(mDH(P_gens_in_D[i]))
                       :i in [1..#Generators(P)]];

  // The next line has been hacked by Claus!!
  generators_in_o := [ PowerIdeal(FieldOfFractions(o)) |
                       (om!!(id*Denominator(id)) meet o) * (1/Denominator(id))
                     : id in generators_in_om ];
 
  representative_picard_group := function(rep)
    repseq := Eltseq(rep);
    return &*[generators_in_o[i]^repseq[i]:i in [1..#generators_in_o]];
  end function;

    disc_log_picard_group_inner := function(id)
	idm := om!!id;
	if not IsCoprime(id,F) then
	  error "PicardGroup: Ideal must be coprime to the conductor";
	end if;
	Crep := id@@mC;
	is_princ, elt := IsPrincipal(mCo(-(H!Eltseq(Crep)))*idm);
	if not is_princ then 
	  error "PicardGroup: Failure in discrete logarithm.";
	end if;
	return Crep, elt;
    end function;

  disc_log_picard_group := function(id)
    Crep, elt := disc_log_picard_group_inner(id);
    Grep := elt@@mG;
    return mDP(mGD(Grep)+mHD(H!Eltseq(Crep)));
  end function;

  is_principal_with_generator := function(id)
    Crep, elt := disc_log_picard_group_inner(id);
    if not IsId(Crep) then
	return false, _;
    end if;
    Grep := elt@@mG;
    if not IsId(mDP(mGD(Grep))) then
	return false, _;
    end if;
    return true, mG(Grep);
  end function;

  return P, map< P    -> PowerIdeal(FieldOfFractions(o)) |
                 rep :-> representative_picard_group(rep),
                 id  :-> disc_log_picard_group(id) >;
end intrinsic;

intrinsic UnitGroupAsSubgroup(o::RngOrd, O::RngOrd:UG := false) -> GrpAb, Map
{The unit group of o as a subgroup of the unit group of a maximal order}

  // m_Um cannot be a "raw" map here!!!

  require IsMaximal(O): "The second argument must be a maximal order";

  if UG cmpne false then
    Um := UG[1];
    m_Um := UG[2];
  else
    Um, m_Um := UnitGroup(O);
  end if;
  if IsMaximal(o) then 
    return sub<Um|Um>;
  end if;
  
  F := Conductor(o);
  om := O;
  Fm := om!!F;
  
  G, m_G := RayResidueRing(Fm);
  // factor out the multiplicative group of o/F
  ogens := residue_class_ring_unit_subgroup_generators(o, F);
  omFoF, m_omFoF := quo< G | [ a@@m_G : a in ogens ]>;
  im_Um := [m_omFoF(m_Um(Um.i)@@m_G) : i in [1..#Generators(Um)]];
  m := hom< Um->omFoF | im_Um >; 
  kern := Kernel(m);
  return sub<Um|kern>;
end intrinsic;

intrinsic UnitGroupAsSubgroup(o::RngOrd:UG := false) -> GrpAb, Map
{"} // "
  return UnitGroupAsSubgroup(o, MaximalOrder(o) : UG := UG);
end intrinsic;

function UnitGroupQuotientTransversal(O)
    M := MaximalOrder(O);
    Um, m_Um := UnitGroup(M);

    s := UnitGroupAsSubgroup(O, M : UG := <Um, m_Um>);
    T := [x @ m_Um : x in Transversal(Um, s)];

    return T;
end function;

intrinsic InternalIsPrincipal(I::RngOrdIdl, inv::RngOrdFracIdl) -> BoolElt, RngOrdElt
{For ideals of non maximal orders}
    O := Order(I);
    F := Conductor(O);
    g := F + I;
    size := 2;
    scale := 1;
    sI := I;
    while not IsOne(g) do
    //"g = ", g;
	scale := Random(inv, Floor(size));
	assert scale in inv;
	sI := scale*I;
	g := F + sI;
	size := size*1.1;
    end while;
    assert FieldOfFractions(O)!!(sI)/scale eq I;
    assert IsIntegral(sI);
    I := sI;

    mI := MaximalOrder(O)!!I;
    is_princ, mg := IsPrincipal(mI);

    if not is_princ then
    //"max non princ";
	return false, _;
    end if;

    assert mg*MaximalOrder(O) eq ideal<MaximalOrder(O) | Basis(mI)>;
    R, mR := RayResidueRing(MaximalOrder(O)!!F);
    if Order(R) eq 1 then
	return true, scale eq 1 select O!mg else mg/scale;
    end if;

    /* mg |-> R |-> U |-> max order */
/*
mg;
"scale = ", scale;
*/
    is_princ, g := HasPreimage(mg, mR);
    assert is_princ;
    if not is_princ then
    "first preimage fail";
	return false, _;
    end if;

    U, f := UnitGroup(MaximalOrder(O));
    q := residue_class_ring_unit_subgroup_generators(O, Conductor(O));
    q, mq := quo<R|[x@@mR : x in q]>;
    h := hom<U -> q | [U.i @ f @@ mR @mq : i in [1..Ngens(U)]]>;

    k := Kernel(h);
    k := [Eltseq(U!x) : x in Generators(k)];
    b := LLL(Matrix(k));

    is_princ, g := HasPreimage(mq(g), h);
    if not is_princ then
	//"second preimage fail";
	return false, _;
    /*	    
	G, m := PicardGroup(O);
	if not IsId(I @@ m) then
	    return false, _;
	end if;
	OU := UnitGroupAsSubgroup(O : UG := <U, f>);
	T := Transversal(U, OU);
	for t in T do 
	    if not IsId(t) and IsCoercible(O, mg*f(t)) then
		g := t^-1;
		break;
	    end if;
	end for;
	if not assigned g then
	while true do
	    ru := Random(OU);
	    if not IsId(ru) and IsCoercible(O, mg*f(ru)) then
		g := ru^-1;
		break;
		if O!(mg*f(ru))*F eq I then
		end if;
	    end if;
	end while;
	end if;
    */
    end if;

    bi := Matrix(Rationals(), b)^-1;
    g := Eltseq(g);
    bi := Vector(Rationals(), g)*bi;
    bi := [ Round(x) : x in Eltseq(bi)];
    g := Eltseq(Vector(g) - Vector(Integers(), bi)*b)[1..Ngens(U)];

//mg, f(g), scale;
    mg := O!(mg/f(g));
    mg := scale ne 1 select mg/scale else mg;
    return true, mg;
    /* U -> max order -> R */
    h := hom< U -> R | [U.i @ f @@ mR : i in [1..Ngens(U)]]>;

end intrinsic;
