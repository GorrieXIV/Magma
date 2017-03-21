freeze;

function isogk_13_R4(t) return 5*t^4+55*t^3+260*t^2+583*t+537; end function;
function isogk_13_R3(t)
 return 5*t^6+80*t^5+560*t^4+2214*t^3+5128*t^2+6568*t+3373; end function;
function isogk_13_R2(t) return
 5*t^8+110*t^7+1045*t^6+5798*t^5+20508*t^4+47134*t^3+67685*t^2+54406*t+17581;
end function;
function isogk_13_R1(t) return
 t^10+27*t^9+316*t^8+2225*t^7+10463*t^6+34232*t^5+78299*t^4+
 122305*t^3+122892*t^2+69427*t+16005; end function;
function isogk_13_R0(t) return
 t^14+38*t^13+649*t^12+6844*t^11+50216*t^10+271612*t^9+1115174*t^8+
 3520132*t^7+8549270*t^6+15812476*t^5+21764840*t^4+21384124*t^3+
 13952929*t^2+5282630*t+854569; end function;

function isogkernel(x,t,T,l)
 case l: when 2: return x+(192+3*t)*T; when 3: return x+(3*t+81)*T;
  when 5: return x^2+6*(t^2+22*t+125)*x*T+9*(t^2+22*t+89)*(t^2+22*t+125)*T^2;
  when 7: return x^3+9*(t^2+13*t+49)*x^2*T+
                 27*(t^2+13*t+33)*(t^2+13*t+49)*x*T^2+
                 27*(t^2+13*t+49)*(t^4+26*t^3+219*t^2+778*t+881)*T^3;
  when 13: P:=t^2+5*t+13; Q:=t^2+6*t+13;
   t5:=18*P*Q; t4:=27*P*Q*isogk_13_R4(t);
   t3:=108*P*Q^2*isogk_13_R3(t); t2:=243*P^2*Q^2*isogk_13_R2(t);
   t1:=1458*P^2*Q^3*isogk_13_R1(t); t0:=729*P^2*Q^3*isogk_13_R0(t);
   return x^6+t5*x^5*T+t4*x^4*T^2+t3*x^3*T^3+t2*x^2*T^4+t1*x*T^5+t0*T^6;
 else error "(l-1) does not divides 12"; end case; end function;

function isogkernel_char2(x,t,l)
 case l: when 3: return (x+1/(t+1));
  when 5: return (x^2-x/(t+1)+1/(t+1)^3);
  when 7: return (x^3+t/(t^2+t+1)*x^2+(t+1)/(t^2+t+1)^2*x+1/(t^2+t+1)^3);
  when 13: return x^6+1/(t+1)*x^5+t*(t^3+t+1)/(t+1)^3/(t^2+t+1)^2*x^4+
            t/(t+1)^3/(t^2+t+1)^2*x^3+(t^4+t^3+1)/(t+1)^6/(t^2+t+1)^4*x^2+
            1/(t+1)^7/(t^2+t+1)^4*x+1/(t+1)^9/(t^2+t+1)^6;
 else error "(l-1) does not divides 12"; end case; end function;

function isogkernel_char3(x,T,t,l)
 case l: when 2: return (x+T); when 5: return (x^2-(t+1)*x*T+(t-1)*T^2);
 when 7:
 return (x^3-(t+1)*(t-1)^2*x^2*T+(t+1)*(t-1)^4*x*T^2-(t-1)^4*(t^2+t-1)*T^3);
 when 13:
 return x^6-(t+1)^2*(t-1)*(t^2+1)*x^5*T+(t+1)^4*(t-1)*(t^2+1)^2*x^4*T^2-
         t*(t+1)^4*(t^7-t^6+t^5+t^4-t^3+t^2-t+1)*x^3*T^3+
         (t+1)^6*(t-1)*(t^2+1)*(t^5-t^4+1)*x^2*T^4-
         (t+1)^10*(t-1)*(t^2+1)^2*x*T^5+(t+1)^8*(t^7+t^6+t^5-t^4-t^3-t+1)*T^6;
 else error "(l-1) does not divides 12"; end case; end function;

function c4poly(t,l)
 case l: when 2: return (t+16)*(t+64);
  when 3: return (t+3)*(t+27); when 5: return (t^2+10*t+5)*(t^2+22*t+125);
  when 7: return (t^2+5*t+1)*(t^2+13*t+49);
  when 13: return (t^2+5*t+13)*(t^2+6*t+13)*(t^4+7*t^3+20*t^2+19*t+1);
 else error "(l-1) does not divides 12"; end case; end function;

function c6poly(t,l)
 case l: when 2: return (t-8)*(t+64)^2; when 3: return (t+27)*(t^2+18*t-27);
  when 5: return (t^2+4*t-1)*(t^2+22*t+125)^2;
  when 7: return (t^4+14*t^3+63*t^2+70*t-7)*(t^2+13*t+49);
  when 13: return (t^2+5*t+13)*(t^2+6*t+13)^2*
                  (t^6+10*t^5+46*t^4+108*t^3+122*t^2+38*t-1);
 else error "(l-1) does not divides 12"; end case; end function;

function jnumerC(x,l)
 case l: when 2: return (x+16); when 3: return (x+3);
  when 5: return (x^2+10*x+5); when 7: return (x^2+5*x+1);
  when 13: return (x^4+7*x^3+20*x^2+19*x+1);
 else error "(l-1) does not divides 12"; end case; end function;

function jnumerL(x,l)
 case l: when 2: return 1; when 3: return (x+27); when 5: return 1;
         when 7: return (x^2+13*x+49); when 13: return (x^2+5*x+13);
 else error "(l-1) does not divides 12"; end case; end function;

function jnumer(x,l) return jnumerC(x,l)^3*jnumerL(x,l); end function;

function getkernel(t,x,c4,c6,l)
 Ts:=SetToSequence(Set([v[1]: v in Roots(x^2-c4/c4poly(t,l))]) meet
		   Set([v[1]: v in Roots(x^3-c6/c6poly(t,l))]));
 assert #Ts eq 1; return isogkernel(x,t,Ts[1],l); end function;

function getkernel_j0(t,x,c6,l)
 Us:=SetToSequence(Set([v[1]: v in Roots(x^3-c6/c6poly(t,l))]));
 return [isogkernel(x,t,U,l) : U in Us]; end function;
function getkernel_j1728(t,x,c4,l)
 Us:=SetToSequence(Set([v[1]: v in Roots(x^2-c4/c4poly(t,l))]));
 return [isogkernel(x,t,U,l) : U in Us]; end function;

function getkernel_j0_extra(t,x,c6,l)
 case l: when 3: return [x];
 when 7: 
  return [x^3+27*c6/(t^4+14*t^3+63*t^2+70*t-7)*(t^4+26*t^3+219*t^2+778*t+881)];
 when 13: C6:=(t^6+10*t^5+46*t^4+108*t^3+122*t^2+38*t-1);
  return [x^6+108*c6*isogk_13_R3(t)/C6*x^3+
          729*c6^2*isogk_13_R0(t)/(t^2+6*t+13)/C6^2];
 else error "not 3,7,13 in j0_extra"; end case; end function;

function getkernel_j1728_extra(t,x,c4,l)
 case l: when 2: return [x];
 when 5: return [x^2+9*c4*(t^2+22*t+89)/(t^2+10*t+5)];
 when 13: C4:=(t^4+7*t^3+20*t^2+19*t+1);
  return [x^6+27*c4*isogk_13_R4(t)/C4*x^4+243*c4^2*isogk_13_R2(t)/C4^2*x^2+
          729*c4^3*isogk_13_R0(t)/(t^2+5*t+13)/C4^3];
 else error "not 2,5,13 in j1728_extra"; end case; end function;

function getkernel_char2(t,x,a2,a6,l)
 return isogkernel_char2(x,t,l); end function;
function getkernel_char3(t,x,a2,a6,l) U:=a2/(jnumerC(t,l)*jnumerL(t,l));
 return isogkernel_char3(x,U,t,l); end function;

function isogeny_j0_char2(E,l) error "Yet to be implemented"; end function;
function isogeny_j0_char3(E,l) error "Yet to be implemented"; end function;

function isogeny_j0(E,l) x:=PolynomialRing(BaseField(E)).1;
 _,_,_,_,a6:=Explode(aInvariants(E)); c6:=-a6/54;
 R:=[r[1] : r in Roots(jnumer(x,l))];
 K1:=&cat[getkernel_j0(r,x,c6,l): r in R | c6poly(r,l) ne 0];
 K2:=&cat[getkernel_j0_extra(r,x,c6,l): r in R | c6poly(r,l) eq 0];
 return (K1 cat K2); end function;
function isogeny_j1728(E,l) x:=PolynomialRing(BaseField(E)).1;
 _,_,_,a4,_:=Explode(aInvariants(E)); c4:=-a4/27;
 R:=[r[1] : r in Roots(jnumer(x,l)-1728*x)];
 K1:=&cat[getkernel_j1728(r,x,c4,l): r in R | c4poly(r,l) ne 0];
 K2:=&cat[getkernel_j1728_extra(r,x,c4,l): r in R | c4poly(r,l) eq 0];
 return (K1 cat K2); end function;

function isogeny_g0(E,l) j:=jInvariant(E);
 if j eq 0 then return isogeny_j0(E,l); end if;
 if j eq 1728 then return isogeny_j1728(E,l); end if;
 _,_,_,a4,a6:=Explode(aInvariants(E)); c4:=-a4/27; c6:=-a6/54;
 x:=PolynomialRing(BaseField(E)).1; R:=Roots(jnumer(x,l)-x*j);
 return [getkernel(r[1],x,c4,c6,l): r in R]; end function;

function isogeny_same(E,l) error "Yet to be implemented"; end function;
function isogeny_generic(E,l) error "Yet to be implemented"; end function;
function isogeny_char2(E,l) j:=jInvariant(E);
 if j eq 0 then return isogeny_j0_char2(E,l); end if;
 a1,a2,_,_,a6:=Explode(aInvariants(E)); assert a1 eq 1;
 x:=PolynomialRing(BaseField(E)).1; R:=Roots(jnumer(x,l)-x*j); //MULT ROOT?
 return [getkernel_char2(r[1],x,a2,a6,l) : r in R]; end function;

function isogeny_char3(E,l) j:=jInvariant(E);
 if j eq 0 then return isogeny_j0_char3(E,l); end if;
 _,a2,_,_,a6:=Explode(aInvariants(E)); 
 x:=PolynomialRing(BaseField(E)).1; R:=Roots(jnumer(x,l)-x*j); //MULT ROOT?
 return [getkernel_char3(r[1],x,a2,a6,l) : r in R]; end function;

function isogeny_kernels(E,l) c:=Characteristic(BaseField(E));
 if c eq l then return isogeny_same(E,l); end if;
 if (12 mod (l-1)) eq 0 then
  if c eq 2 then return isogeny_char2(E,l);
  elif c eq 3 then return isogeny_char3(E,l);
  else return isogeny_g0(E,l); end if; end if;
 return isogeny_generic(E,l); end function;

function c4c6Model(E) a1,a2,a3,a4,a6:=Explode(aInvariants(E));
 F:=EllipticCurve([0,4*a2+a1^2,0,16*a4+8*a1*a3,64*a6+16*a3^2]);
 mEF:=Isomorphism(E,F,[0,a1,4*a3,2]); _,a2,_,a4,a6:=Explode(aInvariants(F));
 G:=EllipticCurve([0,0,0,-27*a2^2+81*a4,54*a2^3-243*a2*a4+729*a6]);
 mFG:=Isomorphism(F,G,[3*a2,0,0,3]); return G,mEF*mFG; end function;

function allisogs(E,l) c:=Characteristic(BaseRing(E)); assert IsPrime(l);
 if c ne 2 and c ne 3 then W,m:=c4c6Model(E);
 else W,m:=SimplifiedModel(E); end if;
 idata:=IsomorphismData(Inverse(m)); K:=isogeny_kernels(W,l); R:=[];
 for k in K do C,im:=IsogenyFromKernel(W,k : Check:=false);
  _,m3:=Transformation(C,idata); R:=R cat [m*im*m3]; end for;
 return R; end function;
