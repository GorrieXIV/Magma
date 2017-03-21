freeze;

/******************************************************************************
*                                                                             *   
*                     MODULAR FORMS OF WEIGHT ONE                             *   
*                                                                             *   
*                    Steve Donnelly, September 2007                           *
*                                                                             *   
*            Adapted from an original version by Kevin Buzzard,               *
*            who deserves most the credit and none of the blame!              *   
*                                                                             *   
******************************************************************************/


///////////////////////////////////////////////////////////////////////////////
//   GENERAL STUFF
///////////////////////////////////////////////////////////////////////////////

// General congruence subgroup stuff

numberofcuspsgamma1:=function(N)
// the number of cusps for Gamma_1(N).
  if N eq 1 then return 1; end if;
  if N eq 2 then return 2; end if;
  if N eq 4 then return 3; end if;
  return &+[EulerPhi(d)*EulerPhi(N div d):d in Divisors(N)] div 2;
end function;

indexofgamma0:=function(N)
   return &*[Integers()| t[1]^t[2] + t[1]^(t[2]-1) : t in Factorization(N)];
end function;

sturmbound:=function(N,k)
// returns t such that if q-expansion of a weight k cusp form
// of level N in some given eigenspace for Diamond ops is 0
// up to and including coefft of q^t,
// then form is zero.
  assert N ge 5; // didn't think about other cases.
  c:=numberofcuspsgamma1(N);
  return Max(0,Floor(k*indexofgamma0(N)/12-2*c/EulerPhi(N))+1);
end function;

numberofcuspsGamma0:=function(N)
  return &+[EulerPhi(Gcd(d, N div d)) : d in Divisors(N)];
end function;

exponentofzpez:=function(p,e)
  // returns the exponent of Z/p^eZ.
  assert IsPrime(p) and e ge 1;
  if p gt 2 then return p^(e-1)*(p-1);
  elif e le 2 then return e; // Z/2Z has exponent 1 and Z/4Z has exponent 2.
  else return p^(e-2);
  end if;
end function;

exponentofznz:=function(n)
  // returns the exponent of Z/nZ
  F:=Factorization(n);
  return LCM([Integers()|exponentofzpez(f[1],f[2]):f in F]);
end function;

codetocharacter:=function(s);
  N,o,seq:=Explode(s);
  return DirichletGroup(N,CyclotomicField(o))!seq;
end function;

charactertocode:=function(chi);
  N:=Modulus(chi);
  return <N,exponentofznz(N),Eltseq(chi)>;
end function;

// This works for characters too? The formula's from WAS were only for Gamma0 or Gamma1

dimensionweightoneeisensteinseries:=function(chi);
  // speaks for itself. Taken from Cohen-Oesterle.
  if IsEven(chi) then return 0; end if;
  N := Modulus(chi);
  facN := Factorization(N);
  f := Conductor(chi);
  facf := [<p,Valuation(f,p)> : p in [q[1] : q in facN]];

  function lambda(r,s,p)
    if 2*s le r then
      if IsEven(r) then
        return p^(r div 2) + p^((r div 2)-1);
      else
        return 2*p^((r-1) div 2);
      end if;
    else
      return 2*p^(r-s);
    end if;
  end function;
  return (1/2)  *  &*[lambda(facN[i][2],facf[i][2],facN[i][1])
                  : i in [1..#facN]];
end function;

weightkeisensteinseries:=function(eps,k,prec)
  return [ PowerSeries(e,prec) : e in EisensteinSeries(ModularForms(eps,k)) 
         | chi*psi^-1 eq eps where _,_,_,chi,psi := Explode(EisensteinData(e)) ];
end function;

degreeofomegagamma1:=function(N);
// computes degree of omega on X_1(N), N>=5.
  if N le 4 then error "degreeofomegagamma1 called with N=",N,
    "so no sheaf because of automorphism problems.";
  end if;
  g:=DimensionCuspFormsGamma1(N,2); // genus.
  c:=numberofcuspsgamma1(N);
  assert c mod 2 eq 0;
  return ((2*g-2)+c) div 2;
end function;

degreeofcuspsheafgamma1:=function(N);
// Computes degree of sheaf on X_1(N) whose sections are wt 1 cusp forms.
  if N le 4 then error "degreeofcuspsheafgamma1 called with N=",N,
    "so no sheaf because of automorphism problems.";
  end if;
  c:=numberofcuspsgamma1(N);
  return degreeofomegagamma1(N)-c;
end function;

degreeofcuspsheafweight2gamma0:=function(N)
// Computes (an upper bound for) degree of (pi_*omega)(chi) for chi odd
//  on X_0(N) in char 0.
  return 2*DimensionCuspFormsGamma0(N,2)-2;
end function;

degreeupperboundforweightonecuspforms:=function(N);
  d:=degreeofcuspsheafgamma1(N);
  return d lt 0 select 0 else d+1;
end function;


///////////////////////////////////////////////////////////////////////////////
//   COMPUTING DIHEDRAL FORMS
///////////////////////////////////////////////////////////////////////////////

forward compute_aplist_from_dihedral_data;

// Returns a sequence of tuples <eps,seq> where seq is the sequence of
// q-expansions of character eps we've found so far.
  
// This was written to do all characters at level N together. 
// Steve hacked it to also do a specified list 'eps' of characters
// (eps:="all" means take all GaloisConjugacyRepresentatives).

// If the option return_dihedral_data:=m is set, then a second object is returned,
// of the form [*<chi,list>*], where each list looks like <eps,1,chi,f0i,...>,
// this data gets stored in f`wt1_dihedral_data for the corresponding ModFrmElt f.

newdihedralforms:=function(N :eps:="all",prec:=0,return_aps:=true,return_dihedral_data:=false);

  // First set up the collection of all chars.
  vprintf ModularForms: "Computing new dihedral forms at level %o.\n", N;
  mu:=exponentofznz(N);
  Cy:=CyclotomicField(mu);
  H0:=DirichletGroup(N,Cy);
  // by default, only compute q-expansions for the chosen representative in each Galois orbit of eps's
  if eps cmpeq "all" then 
    eps := GaloisConjugacyRepresentatives(H0);
    eps_given := eps;
  else
    eps_given := eps; 
    eps := [];
    for i := 1 to #eps_given do 
      eps_ok, newchar := IsCoercible(H0,eps_given[i]); assert eps_ok; 
      Append(~eps,newchar); end for; 
  end if;
  mumax:=mu;
  // mumax may go up later. mumax is the cyclo field over which every
  // eigenform is definitely defined. Every eigenform is always defined
  // over CyclotomicField(mumax). This is a really inefficient way
  // of doing things but it makes things easier to program because that
  // way equality of characters is just = .
  gens:=UnitGenerators(H0);
  pgens:=[Integers()|];
  for n in gens do
    p:=n;
    while IsPrime(p) eq false do p:=p+N; end while;
    Append(~pgens,p);
  end for;
  allchars:=[<eps1,[Parent([<2,Cy!0>])|]>:eps1 in eps];
  data:=[*<eps1,[* *]>:eps1 in eps_given*]; // for dihedral_data

  // Next compute the possible quadratic fields.
  alldivisors:=Divisors(N) cat [-d:d in Divisors(N)];
  DS:=[d:d in alldivisors | IsFundamentalDiscriminant(d)];
  vprintf ModularForms: "Fundamental discriminants dividing N : %o\n", DS;
  for d in DS do
    vprintf ModularForms: "Trying d = %o, M = %o:\n", d, Abs(N div d);
    IndentPush();
    r1:=d gt 0 select 2 else 0;
    M:=AbsoluteValue(N div d);
    K:=QuadraticField(d);
    O:=MaximalOrder(K);
    _:=ClassGroup(K);
    AK:=Automorphisms(K);
    I0:=M*O;
    X:=[I:I in Divisors(I0) | AbsoluteValue(Norm(I)) eq M];
    if #X eq 0 then 
      vprintf ModularForms: "No appropriate ray class characters.\n";
      IndentPop();
      continue d; 
    end if;
    vprintf ModularForms: "Computing some ray class groups.\n";
    G0,f0:=RayClassGroup(I0,[1..r1]);
    f0i:=Inverse(f0);
    c:=InducedMap(f0,f0,AK[2],M);  
    // the same as
    // c:=iso<G0->G0|[<g,f0i(Conjugate(f0(g)))>:g in Generators(G0)]>;
    // I think.
    // TO DO: InducedMap seems to take about half the time in newdihedralforms
    Y:={ {I,Conjugate(I)} : I in X};
    Z:={SetToSequence(i)[1]:i in Y};
    // Z is a list of I is the ideals of norm M up to conjugation.
    vprintf ModularForms: "Number of ideals of norm M is %o.\n", #Z;
    icount:=0;
    for I in Z do
      icount:=icount+1;
      vprintf ModularForms: "Trying ideal #%o:\n", icount;
      G,f:=RayClassGroup(I,[1..r1]);
      fi:=Inverse(f);
      s:=InducedMap(f0,f,AK[1],M);
      si:=Inverse(s);
      H:=Kernel(s);
      // We're only interested in characters whose kernel contains H for
      // some H. Furthermore we are not interested in characters whose
      // kernel contains some bigger subgroup than H; we want the
      // conductor to be exactly I. So let's find all the bigger
      // subgroups!
      toobig:=[Parent(H)|];
      for J in [I/P:P in Divisors(I)|IsPrime(P)] do
        G1,f1:=RayClassGroup(J,[1..r1]);
        s1:=InducedMap(f0,f1,AK[1],M);
        H1:=Kernel(s1);
        Append(~toobig,H1);
      end for;
      vprintf ModularForms: "Computing linear characters with conductor I that are trivial"*
                            " on subgroup of index %o.\n", Index(G0,H);
      /*
      C:=LinearCharacters(G0); // C is all chars of G0.
      C1:=[chi:chi in C | H subset Kernel(chi)];
      */
      // TO DO: these LinearCharacters still swamp the memory sometimes, eg
      // DihedralForms(ModularForms( DirichletGroup(193*12^2)! KroneckerCharacter(-193), 1 )); 
//"Memory before/after LinearCharacters:\n"; ShowMemoryUsage();
      G0modH,modH:=quo<G0|H>;
//"LinearCharacters";
//time
      C1:=LinearCharacters(G0modH);
//"LiftCharacters";
//time
      C1:=LiftCharacters(C1,modH,G0); // C1 is chars whose conductor divides I;
      C2:=[Universe(C1)| chi : chi in C1 | &or[H1 subset Kernel(chi):H1 in toobig] eq false];
      delete C1; // not sure if this makes any difference
//""; ShowMemoryUsage();
      // C2 is those whose conductor equals I.
      // Note that if I isn't its conjugate then definitely
      // we can't have chi = chi o c.
      // But if I is its conjugate we could still have too many characters.
      if I eq Conjugate(I) then
        // Throw away characters which give reducible representations.
        // There is a chance that chi will be chi o c. So remove these.
        C3:=[Universe(C2)| ];
        for chi in C2 do
          if [chi(g):g in Generators(G0)] ne [chi(c(g)):g in Generators(G0)] then
            // chi isn't its conjugate.
            Append(~C3,chi);
          end if;
        end for;
        // Now we have exactly twice as many characters as we want.
        assert IsEven(#C3);
        C2:=[Universe(C2)| ];
        C3temp:={{[chi(g):g in Generators(G0)],[chi(c(g)):g in Generators(G0)]}:chi in C3};
        assert 2*#C3temp eq #C3;
        for i in SetToSequence(C3temp) do
          x:=SetToSequence(i)[1];
          Append(~C2,[chi:chi in C3|[chi(g):g in Generators(G0)] eq x][1]);
        end for;
      end if;          
      vprintf ModularForms: "%o characters of conductor I give irreducible induced representations.\n", #C2;
      // Now C2 contains one char per irred 2-d repn of conductor N
      // which is induced from a character of the quadratic field K
      // with conductor I.
      //
      // Every element of C2 contributes 1 towards the newforms of
      // level N and some character, unless we counted it already!
      // There *are* representations which are induced repns in two distinct
      // ways from two K's, unfortunately. So we have to check that
      // we havent' counted it already. We also have to work out the
      // Dirichlet character.
      // 
      // We have to work out the value of the character on pgens; this
      // will pin it down. And we have to work out the first few a_n;
      // that way we know whether we have seen this representation
      // before.

      if not IsEmpty(C2) then
        vprintf ModularForms: "Computing Dirichlet characters of forms coming from dihedral reps:\n";
      end if;
      counter := 0;
      for chi in C2 do
        mumaxnew:=LCM(mumax,Order(chi));
        Cynew:=CyclotomicField(mumaxnew);
        if mumaxnew gt mumax then
          // Now have to coerce all of allchars into this exciting new field.
          vprintf ModularForms: " (coercing everything up to cyclotomic field of degree %o)\n", mumaxnew;
          allchars:=[<x[1],[Parent([<2,Cynew!0>])|[<z[1],Cynew!(z[2])>:z in y]:y in x[2] ]>:x in allchars];
          mumax:=mumaxnew;
        end if;
        // First let's work out the character.
        vals:=[Cy|];
        for p in pgens do
          F:=Factorization(p*O);
          if #F eq 1 then 
            Append(~vals,-Cy!chi(f0i(F[1][1])));
          else
            Append(~vals,Cy!( chi(f0i(F[1][1]))*chi(f0i(F[2][1])) ));
          end if;
        end for;
        // We now have to find the character corresponding to this!
        // this is easy now, thanks William.
        eps:=DirichletCharacterFromValuesOnUnitGenerators(H0,vals);
        we_want_this_one := exists(i){i : i in [1..#allchars] | allchars[i][1] cmpeq eps};  
        if not we_want_this_one then continue; end if; 
        counter +:= 1;
        x := allchars[i];
        
        // Let's work out all a_p for p<=1+degreeofcuspsheafweight2gamma0(N).
        vprintf ModularForms: "Computing a_p's.\n";
        max_p:=Max([1+degreeofcuspsheafweight2gamma0(N),N,prec]);
        dihedral_data:=[*eps,1,chi,f0i,I,fi,si*];
        aplist:=compute_aplist_from_dihedral_data(dihedral_data,max_p,Cynew);
        if aplist in x[2] then
          vprintf ModularForms: "Looks like we'd found this one already.\n";
        else
          vprintf ModularForms: "Appending to list.\n";
          Append(~allchars[i][2],aplist);
          if return_dihedral_data then Append(~data[i][2],dihedral_data); end if;
        end if;
        delete aplist;
      end for; // chi
      vprintf ModularForms: "Found %o dihedral forms.\n", counter;
      delete C2;
    end for; // I in Z
    IndentPop();
  end for; // d in Ds
  
  if return_aps then 
    ans := allchars;
  else
    // throw away aplists now if not wanted
    ans := [<allchars[i][1],#allchars[i][2]> : i in [1..#allchars]];
  end if;
  if return_dihedral_data then 
    return ans, data;
  else 
    return ans; end if;
end function;

// The coeffs a_p of the dihedral series in M_1(eps) with given dihedral_data,
// returned as a sequence of tuples <p,ap> for primes p up to max_p, with values in F.
// (Here I,fi,si are extra data that perhaps we could do without...)

function compute_aplist_from_dihedral_data(dihedral_data,max_p,F);
 
  eps,_,chi,f0i,I,fi,si := Explode(dihedral_data);
  N := Modulus(eps);
  O := Order(Domain(f0i)!1);
  assert Group(Parent(chi)) eq Codomain(f0i);
  
  aplist:=[Parent(<2,F!1>)|];
  for p in [p:p in [1..max_p] | IsPrime(p)] do
    Ps:=Factorization(p*O);
    if N mod p ne 0 then
      // easy case.
      if #Ps eq 1 then
        // very easy case!
        ap:=F!0;
      else
        ap:=F!( chi(f0i(Ps[1][1]))+chi(f0i(Ps[2][1])) );
      end if;
    else
      // awkward cases.
      if Ps[1][2] eq 1 then
        // p is unramified in K so must not be coprime to I.
        if #Ps eq 1 then
          // p is inert so it divides I and its conjugate.
          ap:=F!0;
        else
          ap:=F!0;
          for PP in Ps do
            P:=PP[1];
            if not (P in Divisors(I)) then
              ap:=ap+F!chi(si(fi(P)));
            end if;
          end for;
        end if;
      else
        // p has ramified in the quadratic field.
        P:=Ps[1][1];
        if P in Divisors(I) then
          ap:=F!0;
        else
          // I hope this is right!
          ap:=F!chi(f0i(P));
        end if;
      end if;
    end if;
    if #[c: c in Eltseq(ap) | c ne 0] le 6 then
      vprintf ModularForms: "%o ", <p,ap>; 
    else 
      vprintf ModularForms: "%o ", <p,"...">;
    end if;
    Append(~aplist,<p,ap>);
  end for;
  vprintf ModularForms: "\n";
  return aplist;
end function;

function qExpansion_wt1_dihedral_form(f,prec)
  eps, mm := Explode(f`wt1_dihedral_data);
  precm := Ceiling(prec/mm);
  K := BaseRing(Parent(f));
  aps := compute_aplist_from_dihedral_data(f`wt1_dihedral_data, precm-1, K);
  ans := [K| 1];  // coeff of 'q' is 1
  num_primes := 0;  // keeps track of how many aps we've used
  for n := 2 to precm-1 do 
    if IsPrime(n) then
      num_primes +:= 1;
      assert aps[num_primes][1] eq n;
      an := aps[num_primes][2];
      aps[num_primes] := <n,0>; // save a bit of memory, these things can be bulky
    else
      fac := Factorization(n);
      if #fac eq 1 then
        // a_{p^r} := a_p * a_{p^{r-1}} - eps(p) a_{p^{r-2}}.
        p  := fac[1][1];
        r  := fac[1][2];
        an := ans[p] * ans[p^(r-1)] - eps(p) * ans[p^(r-2)];
      else  // a_m*a_r := a_{mr} and we know all a_i for i<n.
        m  := fac[1][1]^fac[1][2];
        an := ans[m]*ans[n div m];
      end if;
    end if;
    Append( ~ans, an);
  end for;
  PK := PowerSeriesRing(K);
  if mm eq 1 then 
    f := PK! ([0] cat ans) + O(PK.1^precm);
  else
    // f := Evaluate(f1, PK.1^mm) + O(PK.1^prec); // Evaluate is always &@#!! broken
    f := &+ [PK| ans[i] * PK.1^(mm*i) : i in [1..precm-1]] + O(PK.1^prec); 
  end if;
  return f;
end function;

// This is not needed for any intrinsics, but gets called if one runs 'formsdata0' the old way.

numberofdihedralforms:=function(N:eps:="all");
// count forms including oldforms.
// returns a list of tuples <eps,num>, num=number of forms at character eps.

  mu:=exponentofznz(N);
  K:=CyclotomicField(mu);
  G:=DirichletGroup(N,K);
  X:=[* *];
  for t in [t:t in Divisors(N) | t ne N] do
    if eps cmpne "all" and t mod Conductor(eps) ne 0 then continue; end if;
    Append(~X,<t,newdihedralforms(t:eps:=eps)>);
  end for;
  Y:=newdihedralforms(N:eps:=eps,return_aps:=false);
  answer:=[<charactertocode(y[1]),y[2]>:y in Y];
  for s in X do
    oldforms:=s[2];
    for t in oldforms do
      eps:=G!t[1];  // this is the level N character.
      n:=#t[2];
      // need to bump up X[eps] by n.
      i:=Position([a[1]:a in Y],eps);
      answer[i][2]:=answer[i][2]+n*NumberOfDivisors(N div s[1]);
    end for;
  end for;
  return answer;
end function;

///////////////////////////////////////////////////////////////////////////////
//   THE CORE FUNCTIONS
///////////////////////////////////////////////////////////////////////////////

computecuspforms:=function(chi,k,ModSymList:maxdim:=Infinity());
// This function attempts to decide whether computing
// C:=CuspidalSubspace(ModularSymbols(MinimalBaseRingCharacter(chi),k,-1))
// will take an age or not. If it won't, it computes it.
//
// More precisely, it returns bool,ModSymList,C, where
// either bool is true and C is the space above (cusp forms weight k char chi),
// or bool is false and C is nothing. Why might bool be true?
// Firstly C might have already been computed (it'll be in ModSymList)
// and secondly it might have small dimension, in which case it's
// computed on the fly. If neither holds, it won't compute it.

// TO DO: maxdim is not a good measure of what's feasible -- should be a carefully chosen function of k, dim/C and deg/Q 

  //j:=Position([<i[1],i[2]>:i in ModSymList],<chi,k>);
  got_it := exists(j){j: j in [1..#ModSymList] | ModSymList[j][2] eq k and ModSymList[j][1] eq chi}; 
  if got_it then
    vprintf ModularForms: "Found space in list.\n";
    return true,ModSymList,ModSymList[j][3];
  else
    // shall we work it out?
    dim:=DimensionCuspForms(chi,k)*EulerPhi(Order(chi));
    vprintf ModularForms: "Being asked to compute, in some sense, a Q-vector space of dimension %o.\n", dim;
    if dim gt maxdim then
      vprintf ModularForms: "Refusing to do this!\n";
      return false,ModSymList,_;
    else
      vprintf ModularForms: "Computing forms of weight %o and character %o.\n", k, charactertocode(chi);
      IndentPush();
      C:=CuspidalSubspace(ModularSymbols(MinimalBaseRingCharacter(chi),k,-1));
      IndentPop();
      Append(~ModSymList,<chi,k,C>);
      return true,ModSymList,C;
    end if;
  end if;
end function;

function aretheseweight1(V1,chi,F2,psi2,N,ModSymList);
  // returns bool2, ModSymList, MS, vecs. 
  // 'bool2' is true if V1 is weight 1 forms.
  // MS and 'vecs' are required for 'wt1_auxil_modsyms'

  // I know that V1*F2 is weight 2 level chi*psi.   <--- That should read chi*psi2, I think
  
  // First thing to do is to compute q-expansions to 4*St because this is where the squares will lie.
  qdist:=OverDimension(V1)+1;

  K:=BaseField(V1);
  Kq:=PowerSeriesRing(K); q:=Kq.1;
  F2:=PowerSeries(F2,qdist);  
  meroFs:=[O(q^qdist)+&+[q^i*t[i]:i in [1..qdist-1]]:t in Basis(V1)];
  wt2Fs:=[F2*f:f in meroFs];

  // Now have to find these forms in weight 2 and compute their qexps a bit more.
  vprintf ModularForms: "Computing weight 2 char chi*psi forms.\n";
  bool,ModSymList,C:=computecuspforms(chi*psi2,2,ModSymList); assert bool;
  MS:=C; // to be returned ...
  prec:=2*sturmbound(N,2)+1;
  vprintf ModularForms: "Computing q-expansion basis to precision %o\n", prec;
  IndentPush();
  time0:=Cputime();
  B:=qExpansionBasis(C,prec); 
  ChangeUniverse(~B,Kq);
  IndentPop();
  vprintf ModularForms: "%o sec\n", Cputime(time0);
  vprintf ModularForms: "Finding relevent weight two forms to required precision.\n";
  wt2Gs:=[];
  vecs := [VectorSpace(K,#B)| ]; // remember which combination of the basis gives us the wt2Fs
                                // (this will be stable assuming our "sturm bound" is big enough)
  for f in wt2Fs do
    f0:=f;
    g:=Parent(f)!0;
    vec := [K| ];
    for b in B do
      c_b := Coefficient(f0,Valuation(b));
      term_b := c_b*b;
      f0 -:= term_b;
      g +:= term_b;
      Append( ~vec, c_b);
    end for;
    assert IsWeaklyZero(f0);
    Append(~wt2Gs,g);
    Append(~vecs,Vector(vec));
  end for;
  
  vprintf ModularForms: "Computing Eisenstein series.\n";
  Es:=weightkeisensteinseries(psi2,1,2*sturmbound(N,2)+1);
  // now find G2.
  assert exists(G2){f: f in Es | IsWeaklyEqual(f,F2)};
  vprintf ModularForms: "Computing weight 1 mero forms to big precision.\n";
  wt1Gs:=[Kq!(f/G2):f in wt2Gs]; 
  // Now let's try and find them in weight 2 char chi^2.
  vprintf ModularForms: "Now computing weight 2 character chi^2.\n";
  bool,ModSymList,C:=computecuspforms(chi^2,2,ModSymList); assert bool;
  vprintf ModularForms: "Computing basis: ";  
  time0_basis:=Cputime();
  B:=qExpansionBasis(C,2*sturmbound(N,2)+1); 
  ChangeUniverse(~B,Kq);
  vprintf ModularForms: "%o sec\n", Cputime(time0_basis);
  for g in wt1Gs do
    g2:=g^2;
    // need to check g2 is in C.
    for b in B do
      g2 -:= Coefficient(g2,Valuation(b))*b;
    end for;
    if not IsWeaklyZero(g2) then 
      return false,ModSymList,_,_;  // not all holomorphic weight 1 forms
    end if;
  end for;
  return true,ModSymList,MS,vecs;
end function;

function formsdata0(arg : maxdim:=0, docheaptests:=false, 
                          chiset:=[], myprec:=0, use_mod_p_option:=true); 
  // returns a sequence of tuples of the form
  // <chi,d0,d,V>
  // where chi runs over chiset if it's non-empty, or
  // over all conjugacy classes of characters of level N if it is,
  // d0 is the dim of the dihedral forms, d is the dimension of the
  // forms, and V is the actual weight 1 forms (unless docheaptests
  // is on, in which case it might be "didn't compute").
  // docheaptests is a bool indicating whether we should try tricks
  // which for N<39 or so greatly increase the speed of the computation
  // of the dimension, at the expense of giving us no q-expansions.
  // Note that if a test proves a dim is 0 then it's not cheap!

  // 'arg' can be an integer N or a ModFrm space S (which must be the cusp subspace of a full space of wt 1)
  // In that case, S should already know its dihedral_forms. 
  // If these turn out not to generate all of S, then we will assign S`wt1_auxil_modsyms.
  if Type(arg) eq RngIntElt then 
     N := arg;
     SS := 0; // not used
  elif Type(arg) eq ModFrm then
     SS := arg;
     assert Weight(SS) eq 1 and IsIdentical(SS, AmbientSpace(SS)`cusp);
     assert assigned SS`ambient_space`wt1_dihedral_forms;
     error if assigned SS`is_wt1_dihedral, "Why are we calling formsdata0 ??";
     error if assigned SS`dimension and SS`dimension ne -1, "How do we know the dimension ??";
     N := Level(SS);
     error if not IsEmpty(chiset), "When feeding a ModFrm to formsdata0, not allowed to also specify a 'chiset'";
     chiset := [tup[1]: tup in SS`ambient_space`wt1_dihedral_forms];
     SS`is_wt1_dihedral := [ <chi,true> : chi in chiset ];
     SS`wt1_auxil_modsyms := [* <chi> : chi in chiset *];  
        // will make dihedral flag false and append modsyms data for chi that are not purely dihedral
     SS`dimension := 0; // Caution: we're not observing WAS's standard safety procedure (to set dimension:=-1)
  else
     error "Invalid arg in formsdata0"; end if;

  if maxdim eq 0 then maxdim := 300 + indexofgamma0(N) div 6; end if; 

  mu:=exponentofznz(N);
  K:=CyclotomicField(mu); zeta:=K.1;
  G:=DirichletGroup(N,K);
  Kq:=PowerSeriesRing(K); q:=Kq.1;

  // Let's get some initial variables set up.

  kmax:=3; // do we ever need to loop up to weight 4? Doesn't appear to help.

  GCR:=GaloisConjugacyRepresentatives(G);
 
  // First let's sort out the characters.
  evenchars:=[G|]; oddchars:=[G|];
  for psi in GCR do 
    if IsEven(psi) then Append(~evenchars,psi);
    else Append(~oddchars,psi); end if;
  end for;

  S := IsEmpty(chiset) select oddchars else chiset;

  // we'll loop through S ordered by size of space they generate.

  dimspace3:=func<x|DimensionCuspForms(x,3)*EulerPhi(Order(x))>;
  dimspace2:=func<x|DimensionCuspForms(x,2)*EulerPhi(Order(x))>;
  Sort( ~evenchars, func<x,y|dimspace2(x)-dimspace2(y)>);
  Sort( ~oddchars, func<x,y|dimspace3(x)-dimspace3(y)>);

  ModSymList:=[* *]; // stores weight 2 and weight 3 spaces for which we've computed some q-exps.

  // TO DO: use the stored data when SS is given
  if SS cmpeq 0 then
    dihedraldata:=numberofdihedralforms(N);
  else
    dihedraldata:=[*<Eltseq(tup[1]),#tup[2]> : tup in SS`ambient_space`wt1_dihedral_forms*];
  end if;
  vprintf ModularForms: "Numbers of dihedral forms: ";
  for tup in dihedraldata do 
    vprintf ModularForms: "%o ", tup;
  end for;
  vprintf ModularForms: "\n";

  // There are no weight 1 cusp forms of level 12, for degree reasons,
  // and hence there are no weight 1 cusp forms of level N<5.

  if N lt 5 then // we're done.
    vprintf ModularForms: "N<5 trick worked.\n";
    V0:=VectorSpace(K,1);
    V:=sub<V0|>;
    return SequenceToList([<chi,0,0,V>:chi in S]); end if;

  // we're representable.

  dmax:=sturmbound(N,1);
  // This will have to go *up* later on because once we start the loop,
  // a potential dmax is about kmax times this!
  // The point: f weight 1 cuspidal given char whose q-expansion is
  // 0 mod q^(dmax+1) must be 0.

  vprintf ModularForms: "Trying degree of omega - cusps trick.\n";

  if dmax eq 0 then
    // finished already
    vprintf ModularForms: "Degree of omega - cusps trick worked!\n";
    V0:=VectorSpace(K,Floor(sturmbound(N,1)));
    V:=sub<V0|>;
    return [<chi,0,0,V>:chi in S]; end if;

  // Just a check: Can go later.  --  can also stay!
  globaldmin:=&+[i[2]:i in dihedraldata];
  globaldmax:=degreeupperboundforweightonecuspforms(N);
  assert globaldmax ge globaldmin;

  // Now go character by character --- main loop.

  returndata:=[* *];  

  for i_chi:=1 to #S do
    chi:=S[i_chi];
    vprintf ModularForms: "\nCharacter #%o of %o : chi = %o\n", i_chi, #S, charactertocode(chi);
    if SS cmpeq 0 then
      i:=Position([j[1]:j in dihedraldata],charactertocode(chi)); // the old way
    else
      assert exists(i){i: i in [1..#dihedraldata] | dihedraldata[i][1] eq Eltseq(chi)}; // my way
    end if;
    dmin:=dihedraldata[i][2];

    // Cheap test: is everything left dihedral?
    if docheaptests then
      if dmin eq dmax then
        Append(~returndata,<chi,dmin,dmin,"didn't compute.">);
        continue i_chi;
      end if;
    end if;

    Stmax:=sturmbound(N,kmax); // best Sturm bound i can do without
                               // running into trouble.
    // The point is that we have to compute this far even though at the
    // end of the day we need to know much less.

    // If we have to find an exceptional form, we must check that we
    // actually did something in weight 2 or else the argument
    // won't be rigorous.

    weight2data:=[* *];

    // After a while we probably want to try and see if we can prove
    // that everything in our space is a weight one form. This will
    // be triggered by the following bool:

    exceptionaltrigger:=false;    
    forceexceptionaltest:=false;
    olddimV1s:=[Stmax+2,Stmax+1,Stmax+1,Stmax+1,Stmax+1];
    // bogus list of "old dimensions", all bigger than max.

    vprintf ModularForms: "Trying cusp forms of character chi^2 trick.\n";
    // This trick says: if there's a weight 1 cusp form then multiplying
    // all such forms by one fixed one gives a space of weight 2 cusp
    // forms all of whose q-expansions start q^2+...
    // and hence the dimension of the weight 2 cusp forms must be at 
    // least 1 + the dimension of the weight 1 ones.
    // Hence: if there are no weight 2 forms of level chi^2 then there
    // have to be no weight 1 forms of level chi. And if there are some
    // weight 2 forms of level chi^2 then if we subtract 1 from the
    // dimension then we get an upper bound for the weight 1 forms.
    dmax:=DimensionCuspForms(chi^2,2)-1; if dmax lt 0 then dmax:=0;end if;
    assert dmax ge dmin;
    if dmax eq dmin then 
      vprintf ModularForms: "cusp forms of character chi^2 trick worked.\n";
      if dmin eq 0 then
        V0:=VectorSpace(K,Floor(sturmbound(N,1)));
        V:=sub<V0|>;
        Append(~returndata,<chi,0,0,V>);
        continue i_chi;
      elif docheaptests then
        Append(~returndata,<chi,dmin,dmin,"didn't compute.">);
        continue i_chi;
      end if;
    end if;
   
    // Next trick: if there's a non-zero cusp form of weight 1 then
    // the dimension of the wt 1 Eisenstein series of level psi will
    // be <= the dimension of the wt 2 cusp forms of level psi*chi.
    // Hence if the dimension of the wt 1 Eisenstein series of level psi
    // is > the dimension of the wt 2 cusp forms of level psi*chi,
    // there are no weight 1 cusp forms.

    vprintf ModularForms: "Trying Eisenstein series trick.\n";
    psis := [psi:psi in Elements(G)|IsOdd(psi)];
    vprintf ModularForms: "   %o possible characters: ", #psis;
    for psi in psis do
      vprintf ModularForms: ".";
      d1:=dimensionweightoneeisensteinseries(psi);
      d2:=DimensionCuspForms(psi*chi,2);
      if d1 gt d2 then
        assert dmin eq 0;
        vprintf ModularForms: "Eisenstein series trick worked!\n";
        V0:=VectorSpace(K,Floor(sturmbound(N,1)));
        V:=sub<V0|>;
        Append(~returndata,<chi,0,0,V>);
        continue i_chi;
      end if;
    end for;
    vprintf ModularForms: "\n";

    // Survived initial stoopid tests.
    // So let's try and compute the q-expansions.

    vprintf ModularForms: "Current bounds for dimension are %o and %o.\n", dmin, Stmax;
    
    for test_mod_p in use_mod_p_option select [true, false] 
                                        else  [false] do 
     // This mod_p malarky is all Steve's idea.
     // If all the forms are dihedral, ie if Dimension(weight 1 forms) = dmin, then we can prove this
     // by working in a finite field, which is extremely fast (whereas working in a large cyclo field
     // is extremely slow).  If it turns out there a non-dihedral forms after all, we have to go back 
     // and do it in characteristic zero to identify the space (however hardly any time is lost).
     if test_mod_p then
       // choose a prime p = 1 mod mu ie which splits in CyclotomicField(mu)
       //  (the field in which all the eisenstein series have coeffs)
       p := 1 + (10^7 div mu)*mu;  while not IsPrime(p) do p -:= mu; end while;  assert p gt 10^6;
       zetamu_mod_p := (GF(p)!PrimitiveRoot(p))^((p-1) div mu);  assert Order(zetamu_mod_p) eq mu;
       vprintf ModularForms: "Reducing q-expansions mod %o sending zeta_%o to %o.\n", p, mu, zetamu_mod_p;
       red_mod_p := hom< CyclotomicField(mu) -> GF(p) | zetamu_mod_p >;
       red_mod_p := func< a | red_mod_p(CyclotomicField(mu)!a) >;
       Kqq := PowerSeriesRing(GF(p));  
       red_series_mod_p := func< qexp | Kqq! [Coefficient(qexp,kk) @ red_mod_p : kk in [0..AbsolutePrecision(qexp)-1]] >;
       conjectural_dim := -1; // not set (will be set if the mod p loop seems to stabilize)
     else
       Kqq:=Kq; 
     end if;

     qq := Kqq.1;
     V0:=VectorSpace(BaseRing(Kqq), Max(myprec,Stmax));  // Coeffts from 1 to kmax*St or so. Ambient space.
     V1:=V0;  // this will be the subspace of q-expansions of weight 1 forms.
     for k:=2 to kmax do
      vprintf ModularForms: "Starting tests at weight %o in characteristic %o.\n", k, test_mod_p select p else 0;

      // Now loop through weight k chars.
 
      for eps in (IsOdd(k) select oddchars else evenchars) do
        // first see if we have already computed weight k forms.

        bool,ModSymList,C:=computecuspforms(eps,k,ModSymList:maxdim:=maxdim);
        if bool eq false then continue eps; end if;

        vprintf ModularForms: "Computing basis for %o : ", C;
        IndentPush();
        time0_basisC:=Cputime();
        myprec_safe:=myprec+numberofcuspsGamma0(N)+5; // so that we still have >= prec after dividing 
        bigsturm:=Max(myprec_safe,sturmbound(N,kmax+k-1));
        B:=qExpansionBasis(C,bigsturm+1);  ChangeUniverse(~B,Kq);  assert #B eq Dimension(C);
        IndentPop();  
        vprintf ModularForms: "%o sec\n", Cputime(time0_basisC);

        // now compute the set of Galois conjugates of eps.   

        ord:=Order(eps);
        epsconjs:=[];
        for ii:=1 to ord do
          if GCD(ii,ord) eq 1 then // keep this one
            jj:=ii;
            while GCD(jj,mu) gt 1 do jj:=jj+ord; end while;
            Append(~epsconjs,<jj,eps^jj>); end if;
        end for;

        for epsconj in epsconjs do
          // TO DO: for some chi, repeating the work for conjugates will be a complete waste
          sig,epsc:=Explode(epsconj);
          psi:=epsc*chi^(-1);

          // Fs is the F's at weight k-1 and character psi that we'll divide by
          vprintf ModularForms: "Computing eisenstein q-exps of weight %o : ", k-1;
          time0_es:=Cputime();
          mf_psi := ModularForms(psi,k-1);
          Fs_mf := [*es: es in EisensteinSeries(mf_psi : AllCharacters) | echi*epsi^-1 eq psi 
                                                              where _,_,_,echi,epsi:=Explode(EisensteinData(es))*];
          // TO DO: make the following return this:
          //        EisensteinSeries(ModularForms(psi,k-1) : Pure:=psi);
          Fs := [* PowerSeries(es,bigsturm+1): es in Fs_mf *];
          if test_mod_p then Fs := [* red_series_mod_p(F) : F in Fs *]; end if;
          vprintf ModularForms: "%o sec\n", Cputime(time0_es);
          
          // Why not add cusp forms if k>=3.
          // TO DO: should probably be done only as needed...
          if k ge 3 and not test_mod_p then
            // This is a bit of a pain.  Don't want to compute the
            // conjugate of a space of forms I've already computed.
            ordpsi := Order(psi);
            for ii in [ii: ii in [0..ordpsi-1] | GCD(ii,ordpsi) eq 1] do 
              psic := psi^ii;
              if psic in (IsEven(k-1) select evenchars else oddchars) then 
                 sig2inv := ii; break; end if; 
            end for; 
            sig2 := Integers()! (1/ Integers(ordpsi)! sig2inv);  assert psic^sig2 eq psi;
            while GCD(sig2,mu) gt 1 do sig2:=sig2+ordpsi; end while;
            
            // psi is psic^sig2 and we might have computed at level psic.
            // TO DO: What's he up to here? Will he really know if he's already computed some conjugate?
            bool,ModSymList,C:=computecuspforms(psic,k-1,ModSymList:maxdim:=maxdim); 
            if bool then
              vprintf ModularForms: "Getting basis of weight %o cusp forms.\n", k-1;
              B2c:=qExpansionBasis(C,bigsturm+1);
              assert #B2c eq Dimension(C);
              zeta_to_sig2 := zeta^sig2;
              Fs cat:= [* O(q^(bigsturm+1))+&+[Conjugate(K!Coefficient(f,j),zeta_to_sig2)*q^j:j in [1..bigsturm]]:f in B2c *];
            end if;
          end if; // k>=3           
 
          degseq:=[Degree(BaseRing(Parent(F))) : F in Fs];  Sort(~degseq,~permut);  Fs:=[*Fs[ii^permut] : ii in [1..#Fs]*]; 
          vprintf ModularForms: "Using %o auxiliary forms F (of weight %o) with coefficients in\n", #Fs, k-1;
          rings := [*BaseRing(Parent(F)) : F in Fs*];
          for ii := 1 to #rings do
            if not exists{jj : jj in [1..ii-1] | IsIdentical(rings[ii],rings[jj])} then
              vprintf ModularForms: "  %o\n", rings[ii];
            end if;
          end for;

          // Now conjugate B.  
          vprintf ModularForms: "Conjugating q-expansions: ";
          time0_conj:=Cputime();
          if test_mod_p then
             // reduce elements of B by sending zeta to zetamu_mod_p^sig
             red_mod_p_conj := hom< CyclotomicField(mu) -> GF(p) | zetamu_mod_p^sig >;
             red_series_mod_p_conj := 
                func< qexp | Kqq! [Coefficient(qexp,kk) @ red_mod_p_conj : kk in [0..AbsolutePrecision(qexp)-1]] >;
             Bc:=[red_series_mod_p_conj(b) : b in B]; 
          else
             Bc:=[O(q^(bigsturm+1)) + Kq![Conjugate(Coefficient(f,j),zeta^sig) : j in [0..bigsturm]] : f in B];
          end if;
          vprintf ModularForms: "%o sec\n", Cputime(time0_conj);
          
          for indF:=1 to #Fs do 
            F:=Fs[indF];
            vv:=Valuation(F);

           if V1 eq V0 then 
            // When the q-exps have coeffs in a large cyclotomic field, the following gives awful
            // coefficient blow-up.  Experience shows that Method 1 is better for the first step,
            // while Method 2 is far better for subsequent steps (although I expect there are probably 
            // counterexamples, but it seems hard to predict which method will have worse blow-up)
            // The observation holds true no matter whether we use EchelonForm or Kernel in the two methods.
            // (Obviously in the mod_p case there is no blow-up and all methods are fast.)

            // METHOD ONE: DIVIDE BY F  (Kevin's original)
            F0:=(Kqq!F)/qq^vv;  // normalise (both the F's and the f's) to get invertible power series F0
            F0+:=O(qq^(Dimension(V0)+1));  // avoid working too hard
            vprintf ModularForms: "Inverting F (as a power series over %o): ", BaseRing(Kqq);
            time0_F0i:=Cputime();
            F0i:=1/F0;
            assert AbsolutePrecision(F0i) eq Dimension(V0)+1;
            vprintf ModularForms: "%o sec\n", Cputime(time0_F0i);

            vprintf ModularForms: "Getting %o coefficients of %o meromorphic forms f/F: ", Dimension(V0), #Bc;
            time0_mero_coeffs := Cputime();
            R:=[ ];
            counter:=0;
            for f in Bc do 
               if vv ge Valuation(f) then continue; end if;
               error if AbsolutePrecision(f)-vv lt Dimension(V0), 
                    "Not enough precision in quotient of q-expansions";
               counter+:=1;
               thing:=(Kqq!(f/qq^vv)+O(qq^(Dimension(V0)+1)))*F0i;  // = f/F
               Append(~R, [Coefficient(thing,j):j in [1..Dimension(V0)]]);
            end for;
            error if counter eq 0, "Error in weight 1 forms: PLEASE send this example to magma-bugs@maths.usyd.edu.au";
                                    // (Kevin was interested to know if this is true.)
            vprintf ModularForms: "%o sec\n", Cputime(time0_mero_coeffs);
            vprintf ModularForms: "Echelonizing them: ";
            time0_vs:=Cputime();
            V:=RowSpace(Matrix(R));
            delete R;
            vprintf ModularForms: "%o sec\n", Cputime(time0_vs);
            vprintf ModularForms: "Finding intersection: ";
            time0_intn:=Cputime();
            V1 meet:= V; // weight 1 forms just perhaps got smaller.
            vprintf ModularForms: "%o sec\n", Cputime(time0_intn);
 
           else
            // METHOD TWO: MULTIPLY WEIGHT 1 FORMS BY F  (Steve added this alternative)
            prec_wtk := Dimension(V0)+vv; // want to find products that match a form of weight k to prec_wtk coeffs 
            F := Kqq!F + O(qq^(prec_wtk+1));
            vprintf ModularForms: "Getting %o coefficients of f1*F for %o candidate weight 1 forms f1: ", prec_wtk, Dimension(V1);
            time0_prods:=Cputime();
            prods := [F * (&+[vec[j]*qq^j : j in [1..Dimension(V0)]] + O(qq^(prec_wtk+1))) : vec in Basis(V1)];
            vprintf ModularForms: "%o sec\n", Cputime(time0_prods);
            prods_mat := Matrix([ [Coefficient(prod,j) : j in [1..prec_wtk]] : prod in prods]);
            wtk_mat := Matrix([ [Coefficient(f,j) : j in [1..prec_wtk]] : f in Bc]);
            // Compute intersection of this space with weight k forms (coeffs up to prec_wtk)
            vprintf ModularForms: "Computing intersection with weight %o forms: ", k;
            time0_intn:=Cputime();
            nullspace := KernelMatrix(VerticalJoin(prods_mat, wtk_mat));
            combs_in_intn := ColumnSubmatrix(nullspace, 1, #prods); 
            delete nullspace;
            V1 := RowSpace(combs_in_intn * BasisMatrix(V1));
            delete combs_in_intn;
            vprintf ModularForms: "%o sec\n", Cputime(time0_intn);
           end if;

            vprintf ModularForms: "Dimension of meromorphic weight one forms is now %o.\n", Dimension(V1);
            assert Dimension(V1) ge dmin;

            // We are in the middle of about 10 loops but if we're done then get out.

            if Dimension(V1) eq dmin then
              vprintf ModularForms: (dmin eq 0) select "The intersection trick worked.\n" 
                                   else "These all come from dihedral reps -- the intersection trick worked.\n";
              Append(~returndata,<chi,dmin,dmin,V1>);
              continue i_chi; end if;

            // If the trigger is on and V1 just went down then let's see if we're done.

            if not test_mod_p and exceptionaltrigger and (forceexceptionaltest or (Dimension(V1) lt olddimV1s[#olddimV1s])) then
              assert not IsEmpty(weight2data); // otherwise algorithm isn't correct.
              forceexceptionaltest:=false;
              vprintf ModularForms: "!!!!!  Are all these forms weight one cusp forms?\n";
              F2,psi2:=Explode(weight2data);
              bool2,ModSymList,MS,combs:=aretheseweight1(V1,chi,F2,psi2,N,ModSymList); 
              if bool2 then // we're done
                vprintf ModularForms: "!!!!!  Yes. These are weight 1 forms.\n";
                Append(~returndata,<chi,dmin,Dimension(V1),V1>);  assert dmin lt Dimension(V1);
                vprintf ModularForms: "\n NON-DIHEDRAL CUSP FORMS AT LEVEL %o, CHARACTER %o.\n\n", N, chi;
                if SS cmpne 0 then
                   assert IsIdentical(chi, SS`is_wt1_dihedral[i_chi][1]) and 
                          IsIdentical(chi, SS`wt1_auxil_modsyms[i_chi][1]); 
                   SS`is_wt1_dihedral[i_chi][2] := false;
                   SS`wt1_auxil_modsyms[i_chi] := <chi,F2,combs,MS>; 
                end if;
                continue i_chi; 
              end if;
              vprintf ModularForms: "!!!!!  No. They're not all holomorphic weight 1 forms.\n";
            end if;

            Remove(~olddimV1s,1); Append(~olddimV1s,Dimension(V1)); // Shunt the previous dimensions along

            // Does V1 look like it's become constant?
            if not exceptionaltrigger and olddimV1s eq [Dimension(V1):i in [1..#olddimV1s]] then
              if test_mod_p then 
                 // it looks like the cuspidal dimension is Dimension(V1), and there are non-dihedral forms, so
                 // we'll have to repeat the above in characteristic zero to compute the actual space of q-exps.
                 vprintf ModularForms: "Looks like there are non-dihedral forms, so we'll have to work harder.\n";
                 conjectural_dim := Dimension(V1);  
                 continue test_mod_p; 
              end if; 
              vprintf ModularForms: "!!!!!: Dimension looks constant. Switching trigger on.\n";
              exceptionaltrigger:=true;
              forceexceptionaltest:=true; 
            end if;
      
            // Now let's remember the data if we need to. This is helpful if we are looking for exceptional forms.
            // TO DO: I'm now also using this for the wt1_auxil_modsyms, but this is just arbitrarily
            //        the first psi and F that turn up ... would be better to pick out the 'best' psi and F
            if k eq 2 and IsEmpty(weight2data) then 
              weight2data:=[* Fs_mf[indF], psi *]; 
            end if;
 
          end for; // F
        end for; // epsconj
      end for; // eps
    end for; // k
    end for; // test_mod_p
    error "Magma doesn't know how to compute this space of weight 1 forms.\n\n" *
          "PLEASE send this example to magma-bugs@maths.usyd.edu.au.  " *
          "We will be interested to see it, as we are likely to implement " *
          "improvements to the algorithm in the near future.  Thanks!";
  end for; // i_chi

  if SS cmpne 0 then
    assert SS`is_wt1_dihedral eq [<tup[1], tup[2] eq tup[3]> : tup in returndata];
    SS`dimension := &+[EulerPhi(Order(tup[1]))*tup[3] : tup in returndata]; 
  end if;
  
  return returndata;
end function;

///////////////////////////////////////////////////////////////////////////////
//   INTERFACE --- INTRINSICS
///////////////////////////////////////////////////////////////////////////////

procedure compute_weight1_cusp_space( ~M : prec:=0)
// This sets up dihedral forms and some way of computing the q-expansion basis.
  assert Weight(M) eq 1;
  A := AmbientSpace(M);
  S := CuspidalSubspace(A);
  _ := DihedralForms(A);
  _ := formsdata0(S);  // assigns S`is_wt1_dihedral and S`wt1_auxil_modsyms
end procedure;

intrinsic DihedralForms(M::ModFrm) -> SeqEnum[ModFrmElt]
{For a space M of modular forms of weight 1, returns the cuspidal eigenforms 
that arise from dihedral Galois representations (or twists of these)} 

  // Note: the attribute wt1_dihedral_forms gets attached to the ambient space only.
  if not IsAmbientSpace(M) then return DihedralForms(AmbientSpace(M)); 
  elif assigned M`wt1_dihedral_forms then return M`wt1_dihedral_forms; end if;

  N := Level(M);
  charsM := [chi : chi in DirichletCharacters(M) | IsOdd(chi)];
  Chi := Parent(charsM);

  // Get new and old forms 
  // TO DO: also store NewDihedralForms by themselves?
  
  data := [* <chi,[**]> : chi in charsM *];

  for t in Divisors(N) do
    inds_t := [i : i in [1..#charsM] | t mod Conductor(charsM[i]) eq 0];
    if #inds_t eq 0 then continue; end if;
    charsM_t := [charsM[i] : i in inds_t];
    _, data_t := newdihedralforms(t : eps:=charsM_t, return_dihedral_data, return_aps:=false); 
 
    // Append these to the collected 'data', and remember to record oldforms multiple times
    for chi_tup in data_t do
      chi := chi_tup[1];
      assert exists(i){i: i in [1..#charsM] | IsIdentical(chi, charsM[i]) };
      if t eq N then 
         data[i][2] cat:= chi_tup[2]; // easy case, always want m = 1 
      else
         for elt_data in chi_tup[2] do 
            new_elt_data := elt_data;
            for m in Divisors(N div t) do 
               new_elt_data[2] := m; Append( ~data[i][2], new_elt_data); end for;
         end for;
      end if;
    end for;
  end for;

  // Although some a_p's were computed by 'newdihedralforms', we don't store them, 
  // as they are sometimes very bulky but are reasonably quick to recompute.

  // Create a ModFrmElt for each form, assigning the data
  M`wt1_dihedral_forms := [* <chi,[**]> : chi in charsM *];
  for i := 1 to #data do 
    assert IsIdentical(data[i][1], M`wt1_dihedral_forms[i][1]); // check the characters still come in the right order
    for j := 1 to #data[i][2] do 
      f := New(ModFrmElt);
      f`weight := 1;
      f`wt1_dihedral_data := data[i][2][j]; 
          // data[i][2][j] is [*chi,m,phi,f0i,...*] where m is the exponent (old --> new), 
          //                                        f0i : ideals -> some ray class group,
          //                                        phi is a character on that group, and '...' is
          //                                        data needed by the function that computes qexps
      K := CyclotomicField(Conductor(CoefficientField(phi))) where phi is data[i][2][j][3]; 
      f`parent := BaseChange(M,K);
      Append( ~M`wt1_dihedral_forms[i][2], f);
    end for;
  end for;

  return M`wt1_dihedral_forms;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////
//  AD HOC INTERFACE  --  SPACES FOR INDIVIDUAL CHARACTERS
////////////////////////////////////////////////////////////////////////////////////

// Given a list of power series B, 
// return their restriction of scalars to F
// (to precision n)

function restriction_of_scalars(B, F, n);
  
  R := PowerSeriesRing(F);

  B1 := [R| ];
  B2 := [* *];
  for f in B do
    bool, fR := IsCoercible(R, f);
    if bool then
      Append(~B1, fR);
    else
      Append(~B2, f);
    end if;
  end for;

  if #B2 eq 0 then
    return B1;
  end if;

  // Do "restriction of scalars to F" for each f in B2

  assert Type(F) in {RngInt, FldRat, FldCyc};

  B3 := [R| ];

  for f in B2 do
    Kf := BaseRing(Parent(f));
    assert Type(Kf) eq FldCyc;
    Kf1 := CyclotomicField(GCD(Conductor(F), Conductor(Kf)));
    if Conductor(Kf1) eq 1 then
      Kf2 := Kf;
    else
      Kf2 := RelativeField(Kf1, Kf);
    end if;
    c := [Kf2| Coefficient(f,i) : i in [0..n-1]];
    for a in Basis(Kf2) do
      Append(~B3, R! [Trace(a*c[i]) : i in [1..n]]);
    end for;
  end for;

  // echelonize B3 to remove repeats
  B4 := [R| ];
  M := Matrix(F, n, [Coefficient(f,i) : i in [0..n-1], f in B3]);
  M := EchelonForm(M);
  for i := 1 to Nrows(M) do
    v := M[i];
    if IsZero(v) then 
      break;
    end if;
    Append(~B4,  R! Eltseq(v));
  end for;

  B5 := B1 cat B4;

  assert #B ge #B5;
  error if #B ne #B5, "Wrong number of q-expansions. Try higher precision";

  return B5; 

end function;

// By convention, currently, spaces of ModularForms are always over Z.
// For now, we provide a way to call the weight 1 functions for a given character,
// over a cyclotomic field.  However it can only return a q-expansion basis.

intrinsic ModularFormsBasis(eps::GrpDrchElt, k::RngIntElt, n::RngIntElt : Cuspidal:=false) 
       -> SeqEnum[RngSerPowElt]

{A basis of q-expansions for the space of modular forms with character eps and weight k, 
returned as a sequence of power series with precision n over the base ring of eps}

  require k eq 1 : "Currently only implemented for weight 1";

  F := BaseRing(eps);
  require Type(F) in {RngInt, FldRat, FldCyc} :
          "The first argument is required to be over the rationals or a cyclotomic field";

  R := PowerSeriesRing(F);
  B := [R| ];

  if IsOdd(k + (IsEven(eps) select 0 else 1)) then
    return B;
  end if;

  M := CuspidalSubspace(ModularForms(eps, 1));
  D := DihedralForms(M);
  _ := formsdata0(M);
  S := M`wt1_auxil_modsyms;
  assert #S eq 1 and S[1,1] eq eps;

  if #S[1] gt 1 then
    g := qExpansion(S[1,2], n);
    e := Valuation(g);
    V := [ChangeRing(v, F) : v in S[1,3]];
    BS := qExpansionBasis(S[1,4], n+e);
    ChangeUniverse(~BS, R);
    B cat:= [R| (R! &+[v[i]*BS[i] : i in [1..#BS]])/g : v in V];

  elif #D gt 0 then
    assert #D eq 1 and D[1,1] eq eps;
    B := restriction_of_scalars([qExpansion(f,n) : f in D[1,2]], F, n);
  end if;

  if not Cuspidal then
    B cat:= restriction_of_scalars(weightkeisensteinseries(eps, k, n), F, n);
  end if;

  assert forall{f : f in B | AbsolutePrecision(f) ge n};
  err := O(R.1^n);
  B := [f + err : f in B];

  return B;

end intrinsic;


/*********************************************************************************

// TO DO (??)
intrinsic DihedralSubspace(M::ModFrm) -> ModFrm
{For a space M of modular forms of weight 1, returns the subspace spanned 
 (over some base extension) by cuspidal eigenforms that arise from dihedral 
 Galois representations (or twists of these)} 
  // Is there a reason to use WAS's MakeSubspace rigmarole for this?  Probably yes.
end intrinsic;


///////////////////////////////////////////////////////////////////////////////
//   TESTING
///////////////////////////////////////////////////////////////////////////////

// Sequence of tuples for level N, or for character chi
function w1forms(a,results) 
   if Type(a) eq RngIntElt then
      N := a;
      ans := [];
      for tup in results do 
        if tup[1] eq N then 
           Append( ~ans, tup); end if; end for;
      return ans;
   elif Type(a) eq GrpDrchElt then
      chi := a;
      N := Modulus(chi);
      chis := Eltseq(chi);
      for tup in results do 
        if tup[1] eq N and tup[2] eq chis then 
           return tup[6]; end if; end for;
   end if;
   error "bad type";
end function;

function N_chi(tup)
   N := tup[1]; 
   mu := tup[2];
   Chi := DirichletGroup(N, CyclotomicField(mu));
   assert Exponent(Chi) eq mu;
   chi := Chi! tup[3];
   return N, chi;
end function;

// extend the power series f to precision n, assuming it's in M_1(chi)
function standardw1(prec)
   chi4 := DirichletGroup(4).1;
   h := HalfIntegralWeightForms(4, 1/2).1;
   return PowerSeries(h,prec)^2, chi4;
end function;

intrinsic compare_dims(first::.,last::.,results::.) -> .
{}
   for N := first to last do "\n", N; 
     Chi := FullDirichletGroup(N);
     for tup in w1forms(N,results) do 
       chi := Chi! tup[3]; printf "%o of order %o   ",chi,Order(chi);
       dim := tup[5]*EulerPhi(Order(chi));
       S := CuspidalSubspace(ModularForms(chi,1));
//time       printf "Sturm bound = %o    ", PrecisionBound(S);
time       assert Dimension(S) eq dim; 
       printf "dim=%o    \n", dim;
time       printf "%o\n", [dim,PrecisionBound(S:Exact)-1]; 
     end for; 
   end for;
   return true;
end intrinsic;

// Check that it reproduces the exact same data as in Kevin's file.
// However, when called this way it does things differently ...

intrinsic compare(first::.,last::.,results::.) -> .
{}
   for N := first to last do 
     "\n", N;
     data := w1forms(N,results);
     computed := formsdata0(N : use_mod_p_option:=false);
     assert #computed eq #data;
     for i := 1 to #data do 
       ctup := computed[i];
       V := ctup[4];
       found_it := exists(dtup){tup: tup in data | tup[3] eq Eltseq(ctup[1])};
       assert ctup[2] eq dtup[4] and ctup[3] eq dtup[5] and dtup[5] eq Dimension(V);  // dimensions
       R := BaseRing(V);
       dqs := dtup[6];
       for j := 1 to #dqs do 
         dq := dqs[j];
         coeffs_dq := [Coefficient(dq,k) : k in [1 .. AbsolutePrecision(dq)-1]];
         assert coeffs_dq eq Eltseq(V.j); 
         print "okay with", dq;
     end for; end for; 
   end for;
   return true; 
end intrinsic;
****************************************************************************************************/
