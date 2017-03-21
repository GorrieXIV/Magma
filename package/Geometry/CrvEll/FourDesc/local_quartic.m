freeze;

declare verbose LocalQuartic,2;
import "hints.m": GetHints4Descent,ROOTS;

function GeneratorsForQp2(p)
 if (p eq 2) then return [2,3,5]; end if; F:=GF(p); x:=Random(F);
 while KroneckerSymbol(Integers()!x,p) ne -1 do x:=Random(F); end while;
 return [p,Integers()!x]; end function;

function NFHeight(eps) E:=ChangeUniverse(Eltseq(eps),Rationals());
 return Max([Abs(Numerator(x)) : x in E] cat [Denominator(x) : x in E]);
 end function;

function RealLabels(eps)
 Q := PolynomialRing(Rationals()); y := Q.1; NF:=quo<Q|Q!Modulus(Parent(eps[1]))>;
 zeropad:=func<S,n | S cat [Universe(S)|0 : k in [#S+1..n]]>;
 fluff:=func<a | NF!zeropad(Eltseq(a),4)>; f2:=Modulus(NF);
 R:=RealField(Ceiling(Max([Log(NFHeight(x))/Log(10) : x in eps])*4+50));
 vprintf LocalQuartic,1 : "Computing real labels in %o\n",R;
 PR:=PolynomialRing(R); rts:=Roots(PR!f2); // f2:ay^2=x^4+bx^3+cx^2+dx+e
 assert &and[t[2] eq 1 : t in rts]; // check it really does have 4 roots
 ar:=Sort([R!Real(t[1]) : t in rts]); homs:=[hom<NF -> R | a> : a in ar];
 return [[Sign(h(fluff(e))) : h in homs] : e in eps]; end function;

function LocalImageSize(f,p) // NGens of Im ( C/2E -> K*/Q*K*^2 )
 x:=Parent(f).1; e:=x^3-27*QuarticIInvariant(f)*x-27*QuarticJInvariant(f);
 W:=3*Valuation(Discriminant(f),p)+100;
 pr:=PolynomialRing(pAdicField(p,W)); nl:=#ROOTS(pr!e);
 size:=Valuation(1+nl,2); // number of generators of E(Qp)/2E(Qp)
 ql:=[Degree(k[1]) : k in Factorisation(pr!f)]; 
 corr:=&or[t eq 1 : t in ql]; // if quartic has no linear factor, sub one
 if not (corr) then size-:=1; end if; 
 if (p eq 2) then size+:=1; end if; // if p = 2, add one
 return size; end function;

procedure try_to_add(x,tau,~kfel,~kgens,~kexpanded,G,str)
 if not (tau in kexpanded) then
  if (kfel eq {}) then
   vprintf LocalQuartic,2: "%o Adding new local root %o from x=%o\n",str,tau,x;
   kfel:={tau}; kexpanded:=kfel;
  else fel:=Random(kfel);
   vprintf LocalQuartic,2:
    "%o adding new local generator %o from x=%o\n",str,tau+fel,x;
   kgens join:={tau+fel};
   kexpanded:={fel+&+t : t in Subsets(kgens)}; end if; end if; end procedure;

procedure IOD2(f,~kf,~kg,~ke,M2,beta,emb,s,done)
 x:=Parent(f).1; PZ:=PolynomialRing(Integers()); f:=PZ!f; X:=PZ.1;
 f:=PZ!((PolynomialRing(Rationals())!f)/4^(Valuation(Content(f),2) div 2));
 t:=2^(Valuation(LeadingCoefficient(f),2)+2); // Stoll bug? he has t=4
 // need g for 127946489*x^4-14356364385*x^2+357971176450
 g:=PZ!Reverse(Eltseq(f)); u:=2^(Valuation(LeadingCoefficient(g),2)+2);
 A:=[<PZ!(u^Degree(g)*Evaluate(g,x/u)),0,1/u,0,false>,
     <PZ!(t^Degree(f)*Evaluate(f,x/t)),0,1/t,0,true>];     
 EQ:=ExactQuotient;
 while not IsEmpty(A) do last:=A[#A];
 Prune(~A);
  f,xi0,a,d,b:=Explode(last); df:=Derivative(f);
  for xi in GF(2) do fx:=Evaluate(f,xi); xi1:=Integers()!xi;
   if fx eq 0 then fx1:=Evaluate(df,xi);
    if fx1 eq 0 then
     if Evaluate(f,Integers(4)!xi1) eq 0 then
      A:=[<EQ(Evaluate(f,xi1+2*X),4),xi0+a*xi1,2*a,d+1,b>] cat A; end if;
    else //fx1 ne 0
     xi1+:=Integers()!Evaluate(f,Integers(4)!xi1);
     xi1+:=Integers()!(4+Evaluate(f,Integers(8)!xi1));
     A:=[<EQ(Evaluate(f,xi1+8*X),4),xi0+a*xi1,8*a,d+1,b>] cat A; end if;
   else // fx ne 0
    for xi2 in [Integers(8) | xi1+i : i in [0,2,4,6]] do
     if Evaluate(f,xi2) eq 1 then u:=xi0+a*Integers()!xi2;
      if b then try_to_add(u,emb(s(u-beta)),~kf,~kg,~ke,M2,"IOD2");
      else if u ne 0 then
       try_to_add(1/u,emb(s(1/u-beta)),~kf,~kg,~ke,M2,"IOD2"); end if; end if;
      if #ke eq done then return; end if;
     end if; end for; end if; end for; end while; return; end procedure;

function LocalPoints(f,p : EtaleAlgebra:=0)
 f:=PolynomialRing(Rationals())!f; L:=LeadingCoefficient(f);
 lis:=LocalImageSize(f,p);
 if EtaleAlgebra cmpne 0 then  // Sebastian inserted this for 8-descent.
  N<alpha>:=EtaleAlgebra; qludge:=BaseRing(N);
  qludgep:=p*Integers(qludge); beta:=alpha;
 else
  f2:=L^3*Evaluate(f,Parent(f).1/L); 
  vprintf LocalQuartic,1: "At %o, local image #gens=%o\n",p,lis;
  qludge:=NumberField(Polynomial([0,1]):DoLinearExtension);
  qludgep:=p*MaximalOrder(qludge);
  N<alpha>:=quo<PolynomialRing(qludge) | f2>; beta:=alpha/L; end if;
 s,S:=LocalTwoSelmerMap(N, qludgep); M:=Codomain(s);
 e:=GeneratorsForQp2(p); M2,emb:=quo<M|[s(ee) : ee in e]>;

 kfel:={}; kgens:={}; kexpanded:={}; 
 W:=3*Valuation(Discriminant(f),p)+100; pp:=pAdicField(p,W);
 bpts:=ROOTS(PolynomialRing(pp)!f); _,iso:=AbsoluteAlgebra(N);
 vprintf LocalQuartic,2: "Number of branch points is %o\n",#bpts;
 for R in bpts do r:=Rationals()!R;
  av:=iso(r-beta); aw:=iso(Evaluate(Derivative(f),r));
  es:=[Eltseq( 2*tp`vmap(av[tp`i]) gt W select
	       tp`map(aw[tp`i]) else tp`map(av[tp`i]) ) : tp in S ];//es;
  smap:=M!&cat es;
  try_to_add(r,emb(smap),~kfel,~kgens,~kexpanded,M2,"BPTS"); end for;
 vprintf LocalQuartic,2: "Branch points give %o local generators\n",#kgens;
 HINTS,t1,t2:=GetHints4Descent(f,p,4*Valuation(Discriminant(f),p)+150);
 vprintf LocalQuartic,2: "Size of hints is %o\n",#HINTS;
 for x in HINTS do
  if (IsSquare(pp!Evaluate(f,x))) then
   try_to_add(x,emb(s(x-beta)),~kfel,~kgens,~kexpanded,M2,"HINT");
  end if; end for;
 if (#kgens ne lis or kfel eq {}) then
  if p eq 2 then IOD2(f,~kfel,~kgens,~kexpanded,M2,beta,emb,s,2^lis); end if;
 end if;
////////////////////////////////////////////////////////////////////////
 if (#kgens ne lis or kfel eq {}) then "FAILURE OF NORMAL METHODS"; end if;
 x:=0; delta:=1; region:=250; dellim:=4; iters:=0; delp:=0;
 while (#kgens ne lis or kfel eq {}) do x:=x+delta; /*should never occur*/
  if (IsSquare(pp!Evaluate(f,x))) then
   try_to_add(x,emb(s(x-beta)),~kfel,~kgens,~kexpanded,M2,"ITER"); end if;
  iters:=1+iters;
  if (iters gt region*p/delta) then
   vprintf LocalQuartic,2: "Iteration: delta=%o (x = %o): reducing\n",delta,x;
   delta:=delta/p; iters:=0; delp:=delp+1;
   if (delp ge dellim) then delp:=0; dellim:=dellim+1;
    region:=p^4*region; delta:=1; x:=0; end if; end if; end while;
////////////////////////////////////////////////////////////////////////
 deabs:=func<t | Vector(GF(2),Eltseq(t))>; zz:=func<t | deabs(emb(s(t)))>;
 return // Sebastian tacked on the 4th and 5th return values
   <Explode([deabs(k) : k in kfel]),{deabs(t):t in kgens}>,N,zz,kgens,s*emb;
end function;

// Sebastian added this

function LocalImageOfC2(f, p : EtaleAlgebra:=0)
//               (f::RngUPolElt, p::RngIntElt : Algebra:=false) -> SetEnum, Map
// {Returns the description of the subgroup of K_p* / Q_p*K_p*^2, where ..}
 _,_,_,kgens,res_p := LocalPoints(f,p: EtaleAlgebra:=EtaleAlgebra);
 return kgens, res_p;
end function;
