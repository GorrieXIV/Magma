freeze;

function go(f,p) E,t:=Eltseq(f); E:=[0 : i in [2..t]] cat E;
 E:=E cat [0 : i in [#E+1..AbsolutePrecision(f)-1]];
 E:=[E[i] : i in [1..p-1]]; return E; end function;

function clearum(I) E,t:=Eltseq(I); E:=[0 : i in [2..t]] cat E;
 E:=E cat [0 : i in [#E+1..AbsolutePrecision(I)-1]];
 l:=LCM([Denominator(Rationals()!e) : e in E]); E:=[Integers()!(e*l) : e in E];
 g:=GCD([e : e in E]); E:=[Integers()!(e/g) : e in E]; return E; end function;

function clearit(E) E:=Eltseq(E);
 l:=LCM([Denominator(Rationals()!e) : e in E]); E:=[Integers()!(e*l) : e in E];
 g:=GCD([e : e in E]); E:=[Integers()!(e/g) : e in E]; return E; end function;

function block_lll(M)
 nr:=NumberOfRows(M); nc:=NumberOfColumns(M); ch:=Round(nr/50);
 if ch eq 0 then return LLL(M); end if;
 vprintf ModularCurve: "Semi-reducing %o blocks --- %o total rows\n",ch,nr;
 v:=[0] cat [Round(nr*i/ch) : i in [1..ch]]; VJ:=VerticalJoin;
 for i in [1..ch] do L:=LLL(Submatrix(M,v[i]+1,1,v[i+1]-v[i],nc));
  vprintf ModularCurve: "Block %o is reduced\n",i;
  if i eq 1 then J:=L; else J:=VerticalJoin(J,L); end if; end for;
 return J; end function;

function clunk(N,A : Raw:=false, Reduce:=false)
 assert &and[a gt 1 and N mod a eq 0 and Gcd(a,N div a) eq 1 : a in A];
 vprintf ModularCurve: "Computing X0(%o) quotiented by Atkin-Lehner %o\n",N,A;
 M:=CuspidalSubspace(ModularForms(N,2)); d:=2; dim:=Dimension(M);
 if dim eq 0 then return ProjectiveSpace(Rationals(),1); end if;
 psi:=N*&*[1+1/f[1] : f in Factorization(N)]; prec:=Max(200,Ceiling(N*4*2/12));
 vprintf ModularCurve: "Using %o terms of q-expansion\n",prec; // 4 worst case
 B:=qExpansionBasis(M,prec);
 S<q>:=Parent(B[1]); HYPER:=false;
 if #A ne 0 then vprintf ModularCurve: "Quotienting by Atkin-Lehner\n";
  AL:=[AtkinLehnerOperator(M,al) : al in A]; J,T:=Diagonalization(AL);
  B:=ChangeRing(Matrix([B]),PowerSeriesRing(Rationals()));
  B:=Eltseq(ChangeRing(T,Parent(B[1][1]))*Transpose(B));
  B:=[B[i] : i in [1..#B] | &and[a[i][i] eq +1 : a in J]]; end if; g:=#B;
 vprintf ModularCurve: "Genus is %o\n",g;
 if g ge 50 and Reduce then
  "*** WARNING *** Reducing coefficient size might be infeasible";
 elif g ge 40 and Reduce then
  "*** WARNING *** Reducing coefficient size will be time-consuming"; end if;
 if g eq 0 then return ProjectiveSpace(Rationals(),1); 
 elif g eq 1 then 
    // Steve did this case 
    newform_pieces := M`mf_modular_symbols[3][1]`newform_decomposition;
    if #newform_pieces eq 1 then 
       return EllipticCurve(AssociatedNewSpace(M`mf_modular_symbols[3][1])); end if; 
    // try 1-dimensional newforms
    for nf in [nf : nf in newform_pieces | IsNew(nf) and Dimension(nf) eq 1] do 
      qexp := nf`qexpbasis[2][1];
      if Valuation( qexp - Parent(qexp)! B[1] ) ge PrecisionBound(M) then 
         return EllipticCurve(nf); end if; end for;
    // it must be an oldform ...
    V, VtoM := VectorSpace(M);
    for nf in [nf : nf in newform_pieces | not IsNew(nf)] do 
      qexps := nf`qexpbasis[2];
      q := Universe(qexps).1;
      W := sub< V | [ (M!( f+O(q^PrecisionBound(M)) )) @@ VtoM : f in qexps] >;
      if (M!B[1]) @@ VtoM in W then 
         return EllipticCurve(nf`associated_new_space); end if; end for;
    error "Failed to identify elliptic curve";
 elif g le 6 then vprint ModularCurve: "Hyperelliptic test --- need HermiteForm";
  L:=Matrix([clearum(b) : b in B]); H:=HermiteForm(L);
  T:=[(S!([0] cat Eltseq(H[i])))+O(q^(3*(g+10))) : i in [1..NumberOfRows(H)]];
  /* 
     added mch - 12/03/07 - the test was just for the case when the point
     at infinity on the quotient is NOT a Weierstrass point. Code slightly
     adapted to also handle the case when it is a Weierstrass point. Don't
     know if this ever happens in practise, but better safe than sorry!
  */
  inf := 0;
  if Valuation(T[#T]) eq g and Valuation (T[#T-1]) eq g-1 then
   vprintf ModularCurve: "Testing forms of order %o and %o\n",g,g-1;
   inf := 2;
  elif Valuation(T[#T]) eq 2*g-1 and Valuation (T[#T-1]) eq 2*g-3 then
   vprintf ModularCurve: "Testing forms of order %o and %o\n",2*g-1,2*g-3;
   // in fact, in this case the quotient is DEFINITELY hyperelliptic!
   inf := 1;
  end if;
  if inf gt 0 then
   ff:=S!([0] cat Eltseq(L[#T-1])); gg:=S!([0] cat Eltseq(L[#T]));
   X:=T[#T-1]/T[#T]; Y:=q*Derivative(X)/T[#T]; C:=[]; W:=Y^2;
   for i in [0..2*g+inf] do w:=2*g+inf-i; T:=X^w;
    c:=-Coefficient(W,(inf-3)*w)/Coefficient(T,(inf-3)*w); W:=W+c*T; 
   C cat:=[c]; end for;
   P:=-Polynomial(Reverse(C)); r:=Evaluate(P,X)-Y^2;
   if Valuation(r) ge AbsolutePrecision(r) then
    vprint ModularCurve: "Curve is described by hyperelliptic equations";
    return MinimalWeierstrassModel(HyperellipticCurve(P)); end if; end if;
  vprint ModularCurve: "Curve is not hyperelliptic"; end if; assert g ge 3;
 vprint ModularCurve: "Applying LLL"; L:=LLL(Matrix([clearum(b) : b in B]));
 B:=[(S!([0] cat Eltseq(L[i])))+O(q^prec) : i in [1..NumberOfRows(L)]];
 EQ:=[]; P<[x]>:=ProjectiveSpace(Rationals(),g-1);
 if g eq 3 then d:=4; end if; if g eq 4 or g eq 5 then d:=3; end if;
 vprintf ModularCurve: "Using polynomials of degree %o\n",d;
 F:=[]; V:=[]; C:=[[i : i in x] : x in Multisets({i : i in [1..g]},d)];
 for c in C do F cat:=[&*[B[i] : i in c]]; V cat:=[&*[P.i : i in c]]; end for;
 p:=Min([AbsolutePrecision(e) : e in F]); F:=Matrix([go(e,p) : e in F]);
 vprint ModularCurve: "Have products --- now finding relations";
 K:=Kernel(F); d:=Dimension(K); K:=Matrix([clearit(b) : b in Basis(K)]);
 if not Raw then K:=block_lll(K); end if;
 if Reduce then vprintf ModularCurve: "LLL-reducing %o relations\n",d;
  if g ge 60 then "** WARNING ** Coefficient reduction looks hopeless"; end if;
  K:=LLL(K : Delta:=0.999, Proof:=false); end if;
 v:=Vector(V); EQ cat:=[InnerProduct(K[i],v) : i in [1..NumberOfRows(K)]];
 vprint ModularCurve: "Have equations --- computing curve";
 C:=Curve(P,EQ); assert Degree(C) eq 2*g-2; return C; end function;
//Mike claims that quadrics need not be sufficient if there are trisecants

intrinsic 
X0NQuotient(N::RngIntElt,A::[RngIntElt] : Raw:=false, Reduce:=false) -> Crv
{Same as ModularCurveQuotient}
   return ModularCurveQuotient(N,A : Raw:=Raw, Reduce:=Reduce );
end intrinsic;

intrinsic
 ModularCurveQuotient(N::RngIntElt,A::[RngIntElt] : Raw:=false, Reduce:=false) -> Crv
{The canonical embedding of the quotient curve X0(N)/<G> where G is the group of automorphisms 
 generated by Atkin-Lehner involutions corresponding to the given list of integers A.}
 require &and[a gt 1 : a in A]: "Atkin-Lehner's must be > 1";
 require &and[N mod a eq 0 and Gcd(a,N div a) eq 1 : a in A]:
  "Atkin-Lehner's must have gcd(Q,N/Q)=1";
 return clunk(N,A : Raw:=Raw, Reduce:=Reduce); end intrinsic;
