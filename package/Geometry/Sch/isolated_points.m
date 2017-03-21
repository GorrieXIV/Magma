
freeze;

declare verbose IsolatedPoints,1;

function linear_elim0(C,v,n) assert Degree(C[n],v) eq 1;
 u:=-Coefficient(C[n],v,0)/Coefficient(C[n],v,1);
 return [Evaluate(c,v,u) : c in C],u; end function;

function elim_linear_method(C) RR:=Parent(C[1]); r:=Rank(RR); c:=#C;
 DEG:=[[Degree(C[i],RR.j) : j in [1..r]] : i in [1..c]]; // DEG;
 BOOL:=[[Degree(C[i],RR.j) eq 1 and Monomials(Coefficient(C[i],RR.j,1)) eq [1]
	    : j in [1..r]] : i in [1..c]];
 if not &or &cat BOOL then return C,[]; end if;
 TOTAL:=[TotalDegree(C[i]) : i in [1..c]];
 SUM:=[&+[Degree(C[i],RR.j) : j in [1..r]] : i in [1..c]];
 _,eqno:=Min([(&or BOOL[i]) select <TOTAL[i],SUM[i]> else <10^10,0>
							     : i in [1..c]]);
 MAX:=[Max([Degree(C[i],RR.j) : i in [1..c]]) : j in [1..r]];
 VERT:=[&+[Degree(C[i],RR.j) : i in [1..c]] : j in [1..r]];
 _,w:=Min([BOOL[eqno][j] select <MAX[j],VERT[j]> else <10^9,0> : j in [1..r]]);
 var:=RR.w; vprintf IsolatedPoints:"Eliminating %o from eqn %o\n",var,eqno;
 NEW:=linear_elim0(C,var,eqno); RECURSE,ARR:=elim_linear_method(NEW);
 return RECURSE,ARR cat [<var,eqno>]; end function;

function linear_elim(E) P:=Parent(E[1]);
 for j in [1..#E] do for i in [1..Rank(P)] do
  if Degree(E[j],P.i) ne 1 then continue; end if;
  c:=Coefficient(E[j],P.i,1); if Monomials(c) ne [1] then continue; end if;
  return true,P.i,j,linear_elim0(E,i,j); end for; end for;
 return false,_; end function;

function EliminateLinears(C) I:=[];
 while true do b,w,n,N:=linear_elim(C); if not b then break; end if;
  I cat:=[<w,n>]; C:=N; end while; return C,I; end function;

function elim_specific_linear(E,v)
 for j in [1..#E] do if Degree(E[j],v) ne 1 then continue; end if;
  c:=Coefficient(E[j],v,1); if Monomials(c) ne [1] then continue; end if;
  A,w:=linear_elim0(E,v,j); return true,A,j,w; end for;
 return false,_,_; end function;

function elim_lin_via_list(C,L) I:=[];
 for l in L do b,N,n:=elim_specific_linear(C,l);
 if b then C:=N; I cat:=[<l,n>]; end if; end for; return C,I; end function;

function exclude_zeros(C) return [c : c in C | c ne 0]; end function;

function clear_denom(c) // assumes over Q
 return c*Lcm([Denominator(x) : x in Coefficients(c)]); end function;

function clear_denom_and_exclude_zeros(C) // assumes over Q
 return [clear_denom(c) : c in exclude_zeros(C)]; end function;

function useful_vars(C) assert #C ne 0; A:=[]; P:=Parent(C[1]);
 for i in [1..Rank(P)] do D:=[Degree(c,P.i) : c in C];
  if Set(D) ne {0} then A cat:=[i]; end if; end for; return A; end function;

function min_var(E) assert #E ne 0; P:=Parent(E[1]); V:=useful_vars(E);
 PP<[U]>:=PolynomialRing(BaseRing(P),#V);
 v:=[g eq 0 select 0 else PP.g where g:=Index(V,i) : i in [1..Rank(P)]];
 C:=[Evaluate(e,v) : e in E]; return C,v; end function;

function elim_strict_linear(C : LINEAR:=[])
 vprint IsolatedPoints: "Eliminating strict linear terms";
 if #LINEAR ne 0 then C,lin:=elim_lin_via_list(C,LINEAR);
  X:=[u : u in LINEAR | not u in [l[1] : l in lin]];
  if #X ne 0 then "Did not eliminate",X; end if;
 else C,lin:=EliminateLinears(C); end if; return C,lin; end function;

function linear_elim(E) P:=Parent(E[1]);
 for j in [1..#E] do for i in [1..Rank(P)] do
  if Degree(E[j],P.i) ne 1 then continue; end if;
  c:=Coefficient(E[j],P.i,1); if Monomials(c) ne [1] then continue; end if;
  return true,P.i,j,linear_elim0(E,i,j); end for; end for;
 return false,_; end function;

function Variables(R) return [R.i : i in [1..Rank(R)]]; end function;

intrinsic LinearElimination(S::Sch : EliminationOrder:=[]) -> Map
{Given a scheme, return a map from a scheme S to it such that S has
 variables that appear strictly linearly iteratively removed}
 COEFF:=DefiningEquations(S); LIN:=EliminationOrder;
 if #LIN ne 0 then LSYS,LIN_ELIM:=elim_strict_linear(COEFF : LINEAR:=LIN);
 else LSYS,LIN_ELIM:=elim_linear_method(COEFF); end if;
 RR:=Parent(COEFF[1]); w:=[RR.i : i in [1..Rank(RR)]];
 SC:=[Evaluate(c,w) : c in COEFF]; A:=[RR.i : i in [1..Rank(RR)]];
 for v in LIN_ELIM do k:=Index(A,v[1]); SC,r:=linear_elim0(SC,RR.k,v[2]);
  w[k]:=r; for i in [1..#w] do w[i]:=Evaluate(w[i],w); end for; end for;
 // "assert" LSYS eq [Evaluate(c,w) eq 0 : c in COEFF];
 NSYS:=clear_denom_and_exclude_zeros([Evaluate(c,w) : c in COEFF]);
 NSYS,left:=min_var(NSYS); S2:=Scheme(AffineSpace(Parent(NSYS[1])),NSYS);
 R2:=Variables(Parent(NSYS[1]));
 vars:=[RR.Index(left,R2[i]) : i in [1..#R2]];
 w:=[Evaluate(ww,left) : ww in w];
 mp:=map<S2->S|w,vars : Check:=false>; return mp; end intrinsic;

////////////////////////////////////////////////////////////////////////

function SqfreeResultant(E1,E2,v,b) R:=Resultant(E1,E2,v);
 if b eq false or R eq 0 then return R; end if;
 return &*[Parent(v)| u[1] : u in SquarefreeFactorization(Resultant(E1,E2,v))];
 end function;

function elim_via_resultant(E,R,NAMES,b) RR:=Parent(E[1]);
 for var in R do
  _,eqno:=Min([<d eq 0 select Infinity() else d
                           where d:=Degree(e,var),TotalDegree(e)> : e in E]);
  varname:=NAMES[Index([n[2] : n in NAMES],var)][1];
 vprintf IsolatedPoints: "Eliminate %o from eqno %o: degree %o\n",
                          varname,eqno,Degree(E[eqno],var);
  E:=[SqfreeResultant(E[j],E[eqno],var,b) : j in [1..#E] | j ne eqno]; end for;
 return E; end function;

function elim_deg12_res(C,NAMES,b)
 RR:=Parent(C[1]); r:=Rank(RR);
 DEG:=[[Degree(C[i],RR.j) : j in [1..r]] : i in [1..#C]]; // DEG;
 B1:=[[Degree(C[i],RR.j) eq 1 : j in [1..r]] : i in [1..#C]];
 TOTAL:=[TotalDegree(C[i]) : i in [1..#C]];
 if &or &cat B1 then // want to break ties better ?
  _,eqno:=Min([(&or B1[i]) select TOTAL[i] else 10^10 : i in [1..#C]]);
  var:=RR.Index(B1[eqno],true);
 else MAX:=[Max([Degree(C[i],RR.j) : i in [1..#C]]) : j in [1..r]];
      if Min([m : m in MAX | m ne 0]) ne 2 then return C,[]; end if;
      VARS:=[MAX[j] eq 2 : j in [1..r]];
      SUM:=[&+[VARS[j] select Degree(C[i],RR.j) else 10^10 : i in [1..#C]]
	       : j in [1..r]]; _,w:=Min(SUM); var:=RR.w;
      DEG:=[d ge 1 select d else 10^9 where d:=Degree(C[i],var):i in [1..#C]];
      _,eqno:=Min([<DEG[i],TOTAL[i]> : i in [1..#C]]); end if;
 varname:=NAMES[Index([n[2] : n in NAMES],var)][1];
 vprintf IsolatedPoints: "Eliminate %o from eqno %o: degree %o\n",
	                  varname,eqno,Degree(C[eqno],var);
 NEW:=[SqfreeResultant(C[j],C[eqno],var,b) : j in [1..#C] | j ne eqno];
 RECURSE,ARR:=elim_deg12_res(NEW,NAMES,b);
 return RECURSE,ARR cat [var]; end function;

function elim_via_res(C,mp : RESULTANT:=[],FACTOR:=true)
 vprint IsolatedPoints: "Eliminating via resultants";
 imp:=Inverse(mp); PR:=Ambient(Domain(mp)); DOM:=Parent(C[1]);
 NAMES:=[<mp(PR.i),PR.i> : i in [1..Dimension(PR)]];
 VARS:=[RING.i : i in [1..Rank(RING)]] where RING:=Parent(C[1]);
 if FACTOR then C:=[&*[DOM| u[1] : u in SquarefreeFactorization(c)] : c in C];
  C:=[clear_denom(c) : c in C]; end if;
 if #RESULTANT ne 0 then eRES:=[imp(r) : r in RESULTANT];
  BAD:=[r : r in RESULTANT | not IsMonomial(imp(r))]; // check if this works !
  if #BAD ne 0 then printf "Already eliminated were";
   for b in BAD do printf " %o",b; end for; ""; end if;
  eRES:=[x : x in eRES | x ne 0]; RES_IND:=[Index(VARS,r) : r in eRES];
  mSYS:=elim_via_resultant(C,eRES,NAMES,FACTOR);
 else mSYS,RES_IND:=elim_deg12_res(C,NAMES,FACTOR);
      RES_IND:=[Index(VARS,r): r in RES_IND]; end if;
 mSYS:=clear_denom_and_exclude_zeros(min_var(mSYS));
 return mSYS,C,RES_IND; end function;

////////////////////////////////////////////////////////////////////////

function local_sol_check(sol,JAC,p,RES_SYS,RES_IND,mp)
 if #RES_IND ne 0 then
  PR:=PolynomialRing(GF(p),#RES_IND); j:=1; k:=1; ss:=[PR|];
  for i in [1..#RES_SYS] do
   if i in RES_IND then ss cat:=[PR.j]; j:=j+1;
   else ss cat:=[sol[k]]; k:=k+1; end if; end for;
  RS:=[Evaluate(s,ss) : s in RES_SYS]; V:=Variety(Ideal(RS));
 // 0-dim in general? might be better to loop over variables ? seems no matter
  PTS:=[Evaluate(ss,[c : c in pts]) : pts in V];
 else PTS:=[Eltseq(sol)]; end if; SOL:=[];
 for pt in PTS do
  if Rank(Evaluate(JAC,Eltseq(pt))) ne Ncols(JAC) then continue; end if;
  fsol:=[Evaluate(f,pt) : f in DefiningEquations(mp)];
  vprintf IsolatedPoints: "Found local %o -> %o\n",sol,fsol;
  SOL cat:=[fsol]; end for; return SOL; end function;

function local_loop(S,p,RS,RI,JAC,mp)
 SOL:=[]; vprint IsolatedPoints: "Look for liftable local solutions";
 _<[x]>:=PolynomialRing(GF(p),#S); vec:=[x[i] : i in [1..#S]];
 E:=[Evaluate(s,vec) : s in S]; // should sort E by complexity, somehow
 Sort(~E,func<a,b|TotalDegree(a)-TotalDegree(b)>); //[TotalDegree(e) : e in E];
 for v in VectorSpace(GF(p),#S) do
  if not forall{ 0 : e in E | Evaluate(e,Eltseq(v)) eq 0}
   then continue; end if;
  SOL cat:=local_sol_check(v,JAC,p,RS,RI,mp); end for;
 return SOL; end function;

function uniquify_eseq(E) R:=[];
 for i in [1..#E] do if not E[i] in R then R cat:=[E[i]]; end if; end for;
 return R; end function;

function find_local(SCH,PRIMES : RES:=[],LIN:=[],FACTOR:=true) GLOB:=[* *];
 mp:=LinearElimination(SCH : EliminationOrder:=LIN);
 LSYS:=uniquify_eseq(DefiningEquations(Domain(mp)));
 error if not (#LSYS ne 0 and #LSYS ge Rank(Parent(LSYS[1]))),
 "After linear elimination, #variables exceeds #equations";
 JAC:=JacobianMatrix(LSYS);
 mSYS,RES_SYS,RES_IND:=elim_via_res(LSYS,mp : RESULTANT:=RES);
 mSYS:=uniquify_eseq(mSYS);
 error if not (#mSYS ge Rank(Parent(mSYS[1]))),
 "After resultant elimination, #variables exceeds #equations";
 vprint IsolatedPoints:
   "Degrees",[[Degree(E,v) : E in mSYS] : v in Variables(Parent(mSYS[1]))];
 for p in PRIMES do vprint IsolatedPoints: "Trying prime",p;
  SOL:=local_loop(mSYS,p,RES_SYS,RES_IND,JAC,mp);
  GLOB cat:=[* x : x in SOL *]; end for; // could be different p
 return GLOB; end function;

intrinsic IsolatedPointsFinder
(S::Sch[FldRat],PRIMES::[RngIntElt] : LinearElimination:=[],
        ResultantElimination:=[],FactorizationInResultant:=true) -> List
{Try to find isolated points of a scheme modulo a prime.
 Returns points modulo the primes such that the Jacobian is full rank.
 The number of equations must be >= the number of variables for the scheme.}
 if #PRIMES eq 0 then return []; end if;
 COEFF:=DefiningEquations(S);
 require IsAffine(S) and Dimension(Ambient(S)) le #COEFF:
 "Number of variables should be >= the number of equations, and S be affine";
 return find_local(S,PRIMES : LIN:=LinearElimination,
		   RES:=ResultantElimination,FACTOR:=FactorizationInResultant);
 end intrinsic;

////////////////////////////////////////////////////////////////////////

function iter_lift(vec,SYS,JAC) d:=#SYS;
 J:=Matrix(d,d,[Evaluate(j,vec) : j in Eltseq(JAC)]);
 INV:=J^(-1); m:=INV*Matrix(d,1,([Evaluate(r,vec) : r in SYS]));
 return Eltseq(Vector(vec)-Vector(m)); end function;

function lift_step(sol,i,SYS,JAC)
 p:=Integers()!UniformizingElement(Parent(sol[1]));
 pr:=Min([AbsolutePrecision(u) : u in sol]); if i gt 1 then pr:=pr*2; end if;
 K:=pAdicField(p,pr); vec:=[K!Integers()!u : u in sol];
 return iter_lift(vec,SYS,JAC); end function;

function padic_algdep(x,d) v:=Precision(x);
 p:=Integers()!UniformizingElement(Parent(x)); B:=p^v;
 R:=[Integers()!(x^i) : i in [1..d]] cat [B] cat [0 : i in [1..d]];
 for j in [1..d] do
  S:=[0 : i in [1..2*d+1]]; S[j]:=-1; S[j+d+1]:=B; R cat:=S; end for;
 return Transpose(Matrix(d+1,2*d+1,R)); end function;

intrinsic PowerRelation(alpha::FldPadElt,n::RngIntElt) -> RngUPolElt
{Given a p-adic number over Q_p, return a degree n relation for its powers}
 require AbsoluteInertiaDegree(Parent(alpha)) eq 1 and
         AbsoluteRamificationDegree(Parent(alpha)) eq 1: "Must be over Q_p";
 return Polynomial(Eltseq(LLL(padic_algdep(alpha,n) : Delta:=0.9999)[1]));
 end intrinsic;

function padic_dep_in_roots(x,alpha,d) v:=Precision(x);
 p:=Integers()!UniformizingElement(Parent(x)); B:=p^v;
 R:=[Integers()!(alpha^i) : i in [1..d-1]]
     cat [-Integers()!x,B] cat [0 : i in [1..d]];
 for j in [1..d] do
  S:=[0 : i in [1..2*d+1]]; S[j]:=-1; S[j+d+1]:=B; R cat:=S; end for;
 return Transpose(Matrix(d+1,2*d+1,R)); end function;

function findpoly(x,d) // up to degree d
 return Polynomial(Eltseq(LLL(padic_algdep(x,d) : Delta:=0.9999)[1]));
 end function;

function square_system(SYS,JAC,pt)
 if Nrows(JAC) eq Ncols(JAC) then return SYS,JAC; end if;
 SYS,p:=Sort(SYS,func<a,b|TotalDegree(b)-TotalDegree(a)>); SIG:=Eltseq(p);
 JAC:=JacobianMatrix(SYS); B:=Matrix(Basis(Kernel(Evaluate(JAC,pt))));
 W:=[Min([c : c in [1..Ncols(JAC)] | B[r][c] ne 0]) : r in [1..Nrows(B)]];
 vprintf IsolatedPoints: "At %o: ignore equations %o\n",pt,[SIG[w] : w in W];
 SYS:=[SYS[w] : w in [1..Nrows(JAC)] | not w in W]; JAC:=JacobianMatrix(SYS);
 return SYS,JAC; end function;

function lift_local(SYS,JAC,pt : LIFT:=10,DEG:=32,OPT:=false,DEG_LIST:=[])
 p:=Characteristic(Parent(pt[1])); Kp:=pAdicField(p,2);
 sol:=ChangeUniverse(pt,Kp); k:=0;
 if #DEG_LIST eq 0 then Degrees:=[];
  while 2^k le DEG do A:=[2^k,2*2^k,3*2^k,4*2^k];
   Degrees cat:=[a : a in A | a le DEG]; k:=k+1; end while;
   Degrees:=Remove(Sort(SetToSequence(Set(Degrees cat [DEG]))),1);
 else Degrees:=DEG_LIST; end if;
 ORIG_SYS:=SYS; SYS,JAC:=square_system(SYS,JAC,pt);
 SAVE:=[PolynomialRing(Rationals())|0 : i in [1..#sol]];
 for l in [1..LIFT] do vprint IsolatedPoints: "lift",l;
  sol:=lift_step(sol,l,SYS,JAC); if l lt 7 then continue; end if;
  POLY:=[findpoly(s,1) : s in sol]; // find rat sols separately
  if &and[Degree(f) eq 1 : f in POLY] then
   rat:=[Roots(f,Rationals())[1][1] : f in POLY];
   if &and[Evaluate(e,rat) eq 0 : e in SYS] then return rat; end if; end if;
   if #[x : x in SAVE | x eq 0] eq 0 then
    Degrees:=[Max([Degree(f) : f in SAVE])]; end if;
  for d in Degrees do W:=[w : w in [1..#sol] | SAVE[w] eq 0];
   if #W eq 0 then _,w:=Max([Degree(f) : f in SAVE]); else w:=Min(W); end if;
   f:=findpoly(sol[w],d); FAC:=Factorization(f);
   FAC:=[f[1] : f in FAC | RelativePrecision(Evaluate(f[1],sol[w])) eq 0];
   if #FAC ne 1 then continue d; end if; f:=FAC[1]; u:=Degree(f);
   SIZE:=&+[x^2 : x in Coefficients(f)]; rat:=(u+1)*Log(SIZE)/(2^l*Log(p));
   vprintf IsolatedPoints: "Coord %o Deg %o Ratio %o\n",w,u,rat;
   if rat ge 1.75 then continue; end if; SAVE[w]:=f;
   K<theta>:=NumberField(f); A:=[];
   for i in [1..#sol] do if i eq w then A cat:=[K.1]; continue; end if;
    v:=LLL(padic_dep_in_roots(sol[i],sol[w],u))[1];
    if v[u+1] eq 0 then continue d; end if;
     ratio:=(u+1)*Log(&+[x^2 : x in Eltseq(v)])/(2^l*Log(p));
     vprint IsolatedPoints: "Coordinate",i,ratio;
     if ratio ge 1.95 then continue d; end if;
     A cat:=[&+[v[i]*K.1^(i-1) : i in [1..u]]/v[u+1]]; end for;
   if not &and[Evaluate(e,A) eq 0 : e in ORIG_SYS] then continue; end if;
   if OPT then vprint IsolatedPoints: "Optimising field representation";
    // _:=Order(A); // helps with MaximalOrder?, but need to clear denoms?
    O<theta>,mp:=OptimisedRepresentation(K : PartialFactorisation);
    A:=[mp(a) : a in A]; assert &and[Evaluate(e,A) eq 0 : e in SYS]; end if;
   return A; end for; end for;
 vprint IsolatedPoints: "No point found"; return [];  end function;

intrinsic IsolatedPointsLifter
(S::Sch[FldRat],pt::[FldFinElt] :
 LiftingBound:=10,DegreeBound:=32,OptimizeFieldRep:=false,DegreeList:=[])
 -> BoolElt,Pt
{Given a local liftable point of a suitable scheme,
 try to lift it to a global solution.}
 EQS:=[f : f in DefiningEquations(S) | f ne 0]; d:=Dimension(Ambient(S));
 require IsAffine(S) and d le #EQS:
 "Number of variables should be <= the number of equations, and S be affine";
 require #pt eq d: "Point must be same length as ring dimension";
 require &and[Evaluate(c,pt) eq 0 : c in EQS]: "Point is not local solution"; 
 JAC:=JacobianMatrix(EQS);
 require Rank(Evaluate(JAC,pt)) eq d: "Jacobian must be maximal rank";
 ANS:=lift_local(EQS,JAC,pt : LIFT:=LiftingBound,DEG:=DegreeBound,
		              OPT:=OptimizeFieldRep,DEG_LIST:=DegreeList);
 if #ANS eq 0 then return false,_; end if;
 return true,S(Parent(ANS[1]))!ANS; end intrinsic;

function lift_local_to_minpolys(SYS,JAC,pt : LIFT:=10,DEG:=32,DEG_LIST:=[])
 p:=Characteristic(Parent(pt[1])); Kp:=pAdicField(p,2);
 sol:=ChangeUniverse(pt,Kp); k:=0;
 if #DEG_LIST eq 0 then Degrees:=[];
  while 2^k le DEG do A:=[2^k,2*2^k,3*2^k,4*2^k];
   Degrees cat:=[a : a in A | a le DEG]; k:=k+1; end while;
  Degrees:=Remove(Sort(SetToSequence(Set(Degrees cat [DEG]))),1);
 else Degrees:=DEG_LIST; end if;
 ORIG_SYS:=SYS; SYS,JAC:=square_system(SYS,JAC,pt);
 SAVE:=[PolynomialRing(Rationals())|0 : i in [1..#sol]];
 for l in [1..LIFT] do vprint IsolatedPoints: "lift",l;
  sol:=lift_step(sol,l,SYS,JAC); if l lt 7 then continue; end if;
  POLY:=[findpoly(s,1) : s in sol]; // find (totally) rat sols separately
  if &and[Degree(f) eq 1 : f in POLY] then
   rat:=[Roots(f,Rationals())[1][1] : f in POLY];
   if &and[Evaluate(e,rat) eq 0 : e in SYS] then return POLY; end if; end if;
  for d in Degrees do ANS:=[];
   for w in [1..#sol] do
    if SAVE[w] ne 0 then ANS cat:=[SAVE[w]]; continue; end if;
    f:=findpoly(sol[w],d); FAC:=Factorization(f);
    FAC:=[f[1] : f in FAC | RelativePrecision(Evaluate(f[1],sol[w])) eq 0];
    if #FAC ne 1 then continue d; end if; f:=FAC[1]; u:=Degree(f);
    SIZE:=&+[x^2 : x in Coefficients(f)]; rat:=(u+1)*Log(SIZE)/(2^l*Log(p));
    vprintf IsolatedPoints: "Coord %o Deg %o Ratio %o\n",w,u,rat;
    if rat ge 1.75 then continue d; end if; ANS cat:=[f]; SAVE[w]:=f; end for;
   return ANS; end for; end for;
 vprint IsolatedPoints: "No point found"; return [];  end function;

intrinsic IsolatedPointsLiftToMinimalPolynomials
(S::Sch[FldRat],pt::[FldFinElt] :
 LiftingBound:=10,DegreeBound:=32,DegreeList:=[]) -> BoolElt,SeqEnum
{Given a local liftable point of a suitable scheme,
 attempt to return a sequence of minimal polynomials for the coordinates.}
 EQS:=DefiningEquations(S); d:=Dimension(Ambient(S));
 require IsAffine(S) and d le #EQS:
 "Number of variables should be <= the number of equations, and S be affine";
 require #pt eq #EQS: "Point must be same length as ring dimension";
 require &and[Evaluate(c,pt) eq 0 : c in EQS]: "Point is not local solution"; 
 JAC:=JacobianMatrix(EQS);
 require Rank(Evaluate(JAC,pt)) eq d: "Jacobian must be maximal rank";
 ANS:=lift_local_to_minpolys
       (EQS,JAC,pt : LIFT:=LiftingBound,DEG:=DegreeBound,DEG_LIST:=DegreeList);
 if #ANS eq 0 then return false,_; end if;
 return true,ANS; end intrinsic;

// TODO: allow schemes over number fields
