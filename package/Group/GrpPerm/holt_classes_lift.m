freeze;

/*
** Code to lift conjugacy classes together with centralizers and
** power maps through the soluble radical of a permutation group.
** 
** Orginal code by Derek Holt, September 2004.
** Modified (before installation here) by Bill Unger, May 2005.
**
**/

// A couple of functions for storing permutations as base images.
// I don't trust the Magma functions, since the base might change.
// Functions below take the base as an argument

// PtoBI := func<B,p|B^p>;

BItoP := function(G,B,Bim)
  isc, p := IsConjugate(G,B,Bim);
  assert isc;
  return p;
end function;

ConjugatingElement := function(el1,el2,phi,vecs,repnoi,gens,mats,sv,toX)
  //calculate g conjugating el1 to el2 using affine action data structure
  M := Image(phi);
  V := VectorSpace(M);
  rho := Representation(M);
  F := Field(M);
  dim := Dimension(M); dim1 := dim+1;
  g := Id(Parent(gens[1]));
  MA := MatrixAlgebra(F,dim);
  V1 := VectorSpace(F,dim1);
  v1 := V1!([0 : i in [1..dim]] cat [1]);
        w := vecs[repnoi] + (el1^-1*el2) @ phi @ toX;
        p := Position(vecs,w);
        while sv[p] ne -1 do
          g := gens[sv[p]] * g;
          w := InsertBlock(v1,w@@toX,1,1) * mats[sv[p]]^-1;
          w := (V!ExtractBlock(w,1,1,1,dim)) @ toX;
          p := Position(vecs, w );
        end while;

        w := ((el1^g)^-1 * el2) @ phi;
        mat := MA!rho(el1) - MA!1;
        isc,x := IsConsistent(mat,w);
        x := (M!x) @@ phi;
        g := g * x^-1;
        // assert V!(((el1^g)^-1 * el2) @ phi) eq V!0;
  return g;
end function;

LiftClassStabs := function(G,BG,g,gens,A,B,phi,Cord)
/* g in group G, G acts on vector space V = A/B over finite field.
 * gens = list of generators of centralizer of g in action on V.
 * phi is homomorphisms from A to V.
 * Cord = Order(centralizer of g in G/A)
 * Calculate orbits and stabilizers of C=<gens> on gV using affine action
 * of C on V 
 * BG is base of group G used for base images.
 */
  M := Image(phi);
  V := VectorSpace(M);
  rho := Representation(M);
  F := Field(M);
  W := sub< V | [ V | phi((g,c)) : c in Generators(A) ] >;
  //X := Complement(V,W);
  //conjugacy classes in gV will correspond to orbit reps of C on X
  //not working at moment try another approach
  X, toX := quo<V|W>;

  // set up matrices for affine action.
  dim := Dimension(M); dim1 := dim+1;

  mats := [ GL(dim1,F) | ];
  for c in gens do
    mat := MatrixAlgebra(F,dim1)!0;
    InsertBlock(~mat,rho(c),1,1);
    v := phi((g,c));
    InsertBlock(~mat,v,dim1,1);
    mat[dim1][dim1] := F!1;
    Append(~mats,mat);
  end for;

  //Now work out orbits of mats on X via affine action.
  V1 := VectorSpace(F,dim1);
  v1 := V1!([0 : i in [1..dim]] cat [1]);
  vecs := {@ v : v in X @};
  orbno := [ 0 : v in X ]; //orbno[i] = number of orbit of vecs[i]
  orbct := 0;
  repno := [];
  orblen := [];
  sv := []; //Schreier vector for the orbits
  for i in [1..#vecs] do if orbno[i] eq 0 then
    orbct +:= 1;
    repno[orbct] := i;
    v := vecs[i];
    orbno[i] := orbct;
    sv[i] := -1;
    orb := {@ v @};
    ol := 1;
    while ol le #orb do
      w := InsertBlock(v1,orb[ol]@@toX,1,1); 
      for k in [1..#mats] do
        m := mats[k];
        x := V!ExtractBlock(w*m,1,1,1,dim);
        //x := ReduceVector(W,x);
        x := x@toX;
        p := Position(vecs,x);
        if orbno[p] eq 0 then
          orbno[p] := orbct; Include(~orb,x);
          sv[p] := k;
        end if;
      end for;
      ol +:=1;
    end while;
    orblen[orbct] := ol-1;
  end if; end for;

  // construct list of class reps of form g*a, a in A, and centralizers
  // MA := MatrixAlgebra(F,dim);
  cl := [];
  C := sub<G|gens,A>;
  C`Order := #A * Cord;
  RPC := RandomProcess(C);
  for i in [1..#repno] do
    v := vecs[repno[i]] @@ toX;
    el := g*((M!v) @@ phi);
    //now we want to find generators of the centralizer of el in C (mod B)
    //we know the order is #C /(orblen[i] * #W), so we append random
    //elements until the order is correct
    // Use BSGS rather than grp to reduce time spent in RandomSchreier [BU]
    ordc := #C div (orblen[i] * #W);
    cgens := [C|el]; Cel := Representation(B); 
    AddNormalizingGenerator(~Cel, el);
    first_added := true;
    k := #Base(Cel);
    while #Cel ne ordc do
        //get new random element of centralizer
        cel := Random(RPC);
        x := ConjugatingElement(el,el^cel,phi,vecs,repno[i],gens,mats,sv,toX);
        cel := cel * x^-1;
        // assert V!((el,cel) @ phi) eq V!0;

	inCel, cel, lev := Strip(Cel, cel);
        if not inCel then
	  Append(~cgens, cel);
          // Cel := sub<C|cgens,B>; RandomSchreier(Cel:Run:=5);
	  if first_added then
	      AddNormalizingGenerator(~Cel, cel);	
	      first_added := false;
	  else
	      if lev gt k then
		AppendBasePoint(~Cel, Rep(Support(cel)));
	      end if;
	      AddStrongGenerator(~Cel, cel, ~n);
	      SetDefining(~Cel, n, true);
	      RandomSchreier(Cel:Run:=5);
	  end if;
	  k := #Base(Cel);
        end if;
    end while;
    Append(~cl,<orblen[i] * #W, el, [BG^g:g in cgens] >);
  end for;
  return cl, toX, vecs, orbno, repno, sv, mats;
end function;

LiftClassesCentsPM := function(Cl,G,A,B,Q,toQ,Bfact)
//lift classes Cl of G/A to G/B, where A/B is elementary abelian
//toQ : G -> G/A = Q
//Include centralizers and power maps - store by base images
  Print := GetVerbose("Classes");
  ind := FactoredIndex(A,B);
  assert #ind eq 1;
  p := ind[1,1];
  if Print ge 1 then
    printf "Lifting %o classes through layer of size %o^%o\n", 
		#Cl, p, ind[1,2];
    zeit := Cputime();
  end if;
  BG := Base(G);
  M,phi:=GModule(G,A,B);
  classes:=[];
  toXlist:=[**]; vecslist:=[**]; orbnolist:=[]; repnolist:=[]; svlist:=[];
  reps := [G|]; classno:=[]; genslist:=[]; matslist:=[]; cmQ := [];
  ct:=0;
  for c in Cl do
    ct +:= 1; 
    if Print ge 2 then
	"Lifting quotient class number", ct;
    end if;
    g := c[3];
    g_ord := c[1];
    //get minimal set of generators of Centraliser(Q,g).
    C := ClassCentraliser(Q, ct);
    gens := [ C | Random(C), Random(C) ];
    D := sub< C | gens >; RandomSchreier(D:Run:=5);
    while #D ne #C do
      repeat
	  x := Random(C);
      until x notin D;
      Append(~gens,x); D := sub< C | gens >; RandomSchreier(D:Run:=5);
    end while;
    gens := [ x@@toQ : x in gens ];
    g:=g@@toQ;
    Append(~reps,g);
    cn:=[];
    cl, toX, vecs, orbno, repno, sv, mats :=
                    LiftClassStabs(G,BG,g,gens,A,B,phi,#C);
    Append(~toXlist,toX);
    Append(~vecslist,vecs);
    Append(~orbnolist,orbno);
    Append(~repnolist,repno);
    Append(~svlist,sv);
    Append(~genslist,gens);
    Append(~matslist,mats);
    for x in cl do
       if x[2]^g_ord in B then x_ord := g_ord; else x_ord := p*g_ord; end if;
       // assert x[2]^x_ord in B;
       Append(~classes,<x_ord,Index(Q,C)*x[1],x[2],x[3]>);
       Append(~cn,#classes);
       Append(~cmQ, ct);
    end for;
    Append(~classno,cn);
    if Print ge 2 then
	"Now have",#classes, "lifted classes";
    end if;
  end for;

  if Print ge 1 then
    printf "Lifted %o classes to %o in %o secs, now lifting power maps\n", 
		#Cl, #classes, RealField(5)!Cputime(zeit);
  end if;

  //Now calculate power maps
  dummy := exists(idclno){i:i in [1..#classes]|classes[i][1] eq 1};
  assert dummy;
  classespm:=[ car<IntegerRing(), IntegerRing(), G,
               PowerSequence(PowerSequence(IntegerRing())),
               PowerSequence(car<IntegerRing(), IntegerRing(),
                            PowerSequence(IntegerRing())>) > | ];

  ct:=0;
  pmQ := PowerMap(Q);
  B_primes := {t[1]:t in FactoredOrder(B)};
  for c in classes do
    ct +:= 1; 
    if Print ge 2 then
	"Class", ct;
    end if;
    cc := c;
    cc5 := [];
    Qclass := cmQ[ct];
    CCQc := ClassCentralizer(Q, Qclass);

    /* Construct the list of powers we are going to work out for this rep.
     * We need, for every possible lift of the rep, each prime dividing its
     * order and generators for the group of units modulo its order.
     * The first line sets up enough primes, and the next two add enough
     * generators. [BU]
     */
    Plist := B_primes join {t[1]: t in Factorization(c[1])};
    U,f := UnitGroup(Integers(Bfact*c[1]));
    Plist := Plist join {Integers()|x@f:x in Generators(U)};

    cc5 := [];
    cc5hold := [];
    done_pow := {@ @};
    for f1 in Plist do
      f1red := f1 mod cc[1];
      if f1red eq 0 then
	Append(~cc5hold,<f1,idclno, BG>);
	continue;
      end if;
      if f1red eq 1 then
	Append(~cc5hold,<f1,ct, BG>);
	continue;
      end if;
      ind := Index(done_pow, f1red);
      if ind gt 0 then
	t := cc5[ind];
	Append(~cc5hold, <f1, t[2], t[3]>);
      end if;

      g := cc[3]^f1;
      sqcl := pmQ(Qclass, f1);
     //We have to locate the class number of g.
     //first replace by representative in socle quotient
      isc, h := IsConjugate(Q, g@toQ, Cl[sqcl][3]:
		    LeftSubgroup := CCQc,
		    RightSubgroup:= ClassCentralizer(Q, sqcl));
      assert isc;
      h := h @@ toQ;
      g:=g^h;

      v := (reps[sqcl]^-1 * g) @ phi @ toXlist[sqcl];
      on := orbnolist[sqcl][Position(vecslist[sqcl],v)];
      cn := classno[sqcl][on];
      //we also include a conjugating element
      x := ConjugatingElement(classes[cn][3],g,
                phi,vecslist[sqcl],repnolist[sqcl][on],genslist[sqcl],
                    matslist[sqcl],svlist[sqcl],toXlist[sqcl]);
      Append(~cc5,<f1,cn, BG^(h*x^-1)>);
      Include(~done_pow, f1red);
    end for; //for f1 in Plist do

    Append(~cc,cc5 cat cc5hold);
    Append(~classespm,cc);
  end for; //for c in classes do

  if Print ge 1 then
    printf "Layer complete, time %o secs\n", 
		RealField(5)!Cputime(zeit);
  end if;
  return classespm, BG;
end function;

LiftClassesCentsPMInduct := function(Cl,G,BG,A,B)
//in this version, Cl is assumed to contain centralizers and power maps,
//and is result of previous call of LiftClassesCentsPM(Induct)
//BG is the base for G used inearlier calculations
  Print := GetVerbose("Classes");
  ind := FactoredIndex(A,B);
  assert #ind eq 1;
  p := ind[1,1];
  if Print ge 1 then
    printf "Lifting %o classes through layer of size %o^%o\n", 
		#Cl, p, ind[1,2];
    zeit := Cputime();
  end if;
  M,phi:=GModule(G,A,B);
  classes:=[];
  toXlist:=[**]; vecslist:=[**]; orbnolist:=[]; repnolist:=[]; svlist:=[];
  reps := [G|]; classno:=[]; genslist:=[]; matslist:=[];
  Qclassno:=[];
  Qord := Index(G,A);
  for k := 1 to #Cl do
    if Print ge 2 then
	"Lifting quotient class number", k;
    end if;
    c := Cl[k];
    g:=c[3];
    g_ord := c[1];
    //get minimal set of generators of Centraliser(Q,g).
    gens := [ BItoP(G,BG,x) : x in c[4] ];
    Append(~reps,g);
    cn:=[];
    cl, toX, vecs, orbno, repno, sv, mats :=
       LiftClassStabs(G,BG,g,gens,A,B,phi, Qord div c[2]);
    Append(~toXlist,toX);
    Append(~vecslist,vecs);
    Append(~orbnolist,orbno);
    Append(~repnolist,repno);
    Append(~svlist,sv);
    Append(~genslist,gens);
    Append(~matslist,mats);
    for x in cl do
       if x[2]^g_ord in B then x_ord := g_ord; else x_ord := p*g_ord; end if;
       // assert x[2]^x_ord in B;
       Append(~classes,<x_ord,c[2]*x[1],x[2],x[3]>);
       Qclassno[#classes] := k; Append(~cn,#classes);
    end for;
    Append(~classno,cn);
    if Print ge 2 then
	"Now have",#classes, "lifted classes";
    end if;
  end for;

  if Print ge 1 then
    printf "Lifted %o classes to %o in %o secs, now lifting power maps\n", 
		#Cl, #classes, RealField(5)!Cputime(zeit);
  end if;

  //Now calculate power maps
  dummy := exists(idclno){i:i in [1..#classes]| classes[i][1] eq 1};
  assert dummy;
  // idclno := Representative({i:i in [1..#classes]|classes[i][3] eq Id(G)});
  classespm:=[ car<IntegerRing(), IntegerRing(), G,
               PowerSequence(PowerSequence(IntegerRing())),
               PowerSequence(car<IntegerRing(), IntegerRing(),
                            PowerSequence(IntegerRing())>) > | ];

  for k := 1 to #classes do
    if Print ge 2 then
	"Class", k;
    end if;
    c := classes[k];
    //c[3] should be equal to some Cl[kk][3] mod A
    kk := Qclassno[k];
    // assert Cl[kk][3]^-1*c[3] in A;
    cc5 := [];
    cc5hold := [];
    Clkk5 := Cl[kk][5];
    done_pow := {@ @};
    for j := 1 to #Clkk5 do
      Clkk5j:=Clkk5[j];
      f1 := Clkk5j[1] mod c[1];
      if f1 eq 0 then
        Append(~cc5hold,<Clkk5j[1],idclno, BG>);
        continue;
      end if;
      if f1 eq 1 then
	Append(~cc5hold,<Clkk5j[1], k, BG>);
	continue;
      end if;
      ind := Index(done_pow, f1);
      if ind gt 0 then
	tup := cc5[ind];
	Append(~cc5hold,<Clkk5j[1], tup[2], tup[3]>);
	continue;
      end if;
      g := c[3]^f1;
      //We have to locate the class number of g.
      //the class modulo A should be stored in Cl[kk][5][j]
      sqcl := Clkk5j[2];
      h := BItoP(G,BG,Clkk5j[3]); g:=g^h;

      v := (reps[sqcl]^-1 * g) @ phi @ toXlist[sqcl];
      on := orbnolist[sqcl][Position(vecslist[sqcl],v)];
      cn := classno[sqcl][on];
      //we also include a conjugating element
      x := ConjugatingElement(classes[cn][3],g,
                phi,vecslist[sqcl],repnolist[sqcl][on],genslist[sqcl],
                    matslist[sqcl],svlist[sqcl],toXlist[sqcl]);
      Append(~cc5,<Clkk5j[1],cn, BG^(h*x^-1)>);
      Include(~done_pow, f1);
      // assert (c[3]^Clkk5j[1])^(h*x^-1) * classes[cn,3]^-1 in B;
    end for; //for j := 1 to #Clkk5 do
    Append(~c,cc5 cat cc5hold);
    Append(~classespm,c);
  end for; //for c in classes do

  if Print ge 1 then
    printf "Layer complete, time %o secs\n", 
		RealField(5)!Cputime(zeit);
  end if;
  return classespm, BG;
end function;

intrinsic ClassesLiftCentPMSetup(G::GrpPerm, TF::MonStgElt)
{Compute conjugacy classes of G together with centralizers and
power map information}

    S := ElementaryAbelianSeries(G:LayerSizes:=[2,10,3,7,5,5,7,4,11,3,37,2,257,1]);

    Q, toQ := RadicalQuotient(G);
    if #S eq 1 then /* TF group */
	cl :=  Classes(G:Centralizers:=true,PowerMap:=true, TFAl := TF);
	assert HasAttribute(G, "Classes");
	return;
    end if;
    cl := Classes(Q:Centralizers:=true, PowerMap:=true, TFAl := TF);
    A := S[1];
    B := S[2];
    if #S eq 2 then 
	fact := 1;
    else
	fact := &*[FactoredIndex(S[i], S[i+1])[1,1]:i in [2..#S-1]];
    end if;
    /* fact is an upper bound on increase in elt order lifting through B */
    cl1, BG := LiftClassesCentsPM(cl, G, A, B, Q, toQ, fact);
    delete cl, Q, toQ, fact;
    ii := 3;
    while ii le #S do
	A := B;
	B := S[ii];
	cl2, BG := LiftClassesCentsPMInduct(cl1, G, BG, A, B);
	ii +:= 1;
	cl1 := cl2;
    end while;
    cl := [<t[1],t[2],t[3],sub<G|[BItoP(G,BG,bi):bi in t[4]]>,
		    [[x[1],x[2]]:x in t[5]]>: t in cl1];
    G`Classes := cl;
end intrinsic;
