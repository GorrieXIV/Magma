freeze;

declare verbose Large, 1;

// if number of minors to be calculated exceeds this value, then avoid 
// directly evaluating determinats, use a different rank-based procedure 
Limit := 10000; 

/* original implementation by Jack Button of procedure to decide if a finitely 
   presented group is large: does it have a finite index subgroup that 
   has a surjective homomorphism to a nonabelian free group?
   Algorithm is one-sided: "yes" is always correct; "no" may be incorrect.
 
   Button, J. O.
   Proving finitely presented groups are large by computer. 
   Exp. Math. 20 (2011), no. 2, 153-168. 

   mildly revised by Eamonn O'Brien, November 2013 
*/

// Cornacchia type algorithm to express a coprime integer x mod p 
// (p not necessarily prime) as a "fraction" 
// x=b*inverse(d) mod p for b,d small in modulus
// Rarely used: for TFRank=3 it aims to convert a candidate homomorphism mod p 
// into a candidate homomorphism with integer coefficients

function corn(p,x)
   if x eq 0 then return [0,1]; end if;
   sq:=Sqrt(p);
   a:=p; b:=x;
   while b gt sq do 
      while b le a do
        a-:=b;
      end while; 
      c:=a; a:=b; b:=c;
   end while;
   d:=(b*InverseMod(x,p)) mod p;
   if d ge sq then d:=d-p; end if;
   return([b,d]);
end function;
   
// routine to "box" a multivariate polynomial modulo n: namely, change the 
// polynomial so that all coefficients in each monomial are reduced modulo n
// Rarely used, but when TFRank=3 and no homomorphisms have been
// found with a 0 coefficient then it helps to look for other
// homomorphisms (but is probably better for eliminating all others
   
function box(f,C,t,n)
   if C eq 0 then R:=Integers(); else R:=Integers(C); end if;
   P:=PolynomialRing(R,t);
   g:=P!0;
   
   Co:=Coefficients(f);
   Mo:=Monomials(f);
   
   for i:=1 to #Co do
      L:=Exponents(Mo[i]);
      N:=[];
      for j:=1 to t do
         N[j]:= L[j] mod n;
      end for;
      x:=Monomial(P,N);
      g+:=Co[i]*x;
   end for;
   
   return g;
end function;
   
// Routine that is (rarely) invoked for TFRank more than 2.
// Input is a multivariate polynomial over Z of degree t.
// It then takes a small prime p, calls the "box" function and tries out all 
// homomorphisms mod p. If it finds no solutions for a particular p then it 
// concludes that no homomorphisms can work.
// If it finds more than one solution mod p then this is not particularly helpful.
// If it finds exactly one then it uses the Cornacchia type function  corn
// to guess the solution in integers and //then tests this homomorphism on the 
// polynomial, returning either no or the homomorphism (which is then tested on
// the other determinants)
// Rarely invoked because it is only currently called when TFRank=3, 
// and even then it needs a single determinant that has so far been tested 
// and failed to have any successful homomorphisms. Therefore only likely to 
// arise in the deficiency 1 case when there is only one determinant, and is only 
// likely to give a positive answer if there is a unique successful homomorphism.
   
function cray(PP,t)
   Z:=IntegerRing();
   C:=0;
   Ring:=Z; 
   P:=PolynomialRing(Ring,t);
   P1:=PolynomialRing(Ring,1);
   Pone:=PolynomialRing(Ring);
   
   mm:=1;
   for i:=1 to t do
      Co:=Coefficients(PP,i); 
      mm:=Max(mm,#Co);
   end for;
   
   ip:=2; p:=3; pr:=1; Wn:=[];
   
   while pr le 80*(mm)^2 do
      //idea for 110: avoid "accidentals" at 2,3,5,7 giving multiple
      //values (and 3*5*7 less than 80)
   
      //now ignoring 2 as it's too much of a special case and too likely
      //to yield false positives
      v:=[];
      v[1]:=1;
      for i:= 2 to t do
         Append(~v,0);
      end for;
      g:=box(PP,C,t,p); flp:=0; 
   
      if p ne 2 then
         for i:=1 to t do
            for j:=1 to i-1 do v[j]:=0; end for;
            v[i]:=1;
            while v[i] eq 1 do
               u:=[];
               for j:=1 to t do Append(~u,P1.1^v[j]); end for;
               h:=hom<P->P1|u>;
               b:=box(h(g),0,1,p);
               if Content(b) ne 1 and v[t]eq 1 then  
                  ap:=Append(v,p); 
                  An:=v; Anp:=p; Anc:=Content(b); 
                  Append(~ap,Content(b)); 
                  Append(~Wn,ap); 
                  flp+:=1;
               end if; 
               for j:=1 to i do
                  if v[j] lt p-1 then 
                     v[j]+:=1;
                     for k:=1 to j-1 do v[k]:=0; end for;
                     break;
                  end if;
               end for;
            end while;
         end for;
       end if;
   
       if flp eq 0 then return [0]; end if;
       if flp eq 1 then 
          Try:=[]; bse:=1;
          for i:=1 to t-1 do
             corney:=corn(p,An[i]);
             ase:=bse;
             bse:=LCM(bse,corney[2]);
             Append(~Try,((corney[1]*bse) div corney[2]));
             for ii:=1 to i-1 do
                Try[ii]*:=(bse div ase);;  
             end for;
          end for;
          Append(~Try,bse);
   
          vprint Large: "Will try homomorphism",Try;
   
          F:=FunctionField(Ring);
          HH:=[];
          for i:=1 to t do
             Append(~HH,F.1^Try[i]);
          end for;
   
          trr:=hom<P->F|HH>;
          trrr:=trr(PP);
   
          cntt:=Content(Pone!(Numerator(trrr)));
          if cntt eq 1 then return [0]; else return Try; end if;
       end if;         
       pr*:=p; ip+:=1; p:=NthPrime(ip);
   end while;  
   return [0];
end function;
   
// This function is for the case where TFRank=2. 
// It is guaranteed (assuming no bugs, enough time and memory...)
// to find a successful homomorphism, if one or many exist, or to
// confirm that none exist.
// Input is the Alexander matrix, columns and rows, images of the
// generators under abelianisation and the number of a generator 
// with infinite image in the abelianisation.
// It first tests the homomorphisms [0,1] and [1,0] and then uses
// a Chinese remainder type process to compile a finite list of
// possible successful homomorphisms, which are then checked.
// Generally quite fast, but often generates a fairly big list to 
// check, with all but the first few rarely successful. Sometimes
// homomorphisms with large coefficients can be slow to check, but
// at least the output says which one has been reached.
   
function input(AP,g,r,I,th)
   Ring:=Integers();
   C:=0;
   
   def:=r-g+1;
   P:=PolynomialRing(Ring,2);
   
   MM:=[]; AV:=I[th];
   for h:=1 to 2 do
      if I[th][h] lt 0 then 
         Append(~MM,-I[th][h]); AV[h]:=0;
      else   
         Append(~MM,0);
      end if; 
   end for;
   AV:=ElementToSequence(AV);
   
   Mon:=Monomial(P,MM)-Monomial(P,AV);
   
   Ctlst:=[[],[]]; AXS:=[]; Ctend:=[0,0]; Std:=[];  
   for h:=1 to 2 do
      Polyhere:=PolynomialRing(Ring);
      if h eq 1 then                           
         vprint Large: "Trying homomorphism [0,1]";
         homhere:=hom<P->Polyhere|1,Polyhere.1>;
         tht:=0;
         for j:=1 to g do
            if I[j][2] ne 0 then tht:=j; break; end if; 
         end for;
      else
         vprint Large: "Trying homomorphism [1,0]";
         homhere:=hom<P->Polyhere|Polyhere.1,1>;
         tht:=0;
         for j:=1 to g do
            if I[j][1] ne 0 then tht:=j; break; end if;
         end for;
      end if;
   
      DDH:=ZeroMatrix(Polyhere,r,g);
   
      for k:=1 to r do
         for l:=1 to g do
            DDH[k,l]+:=homhere(AP[k,l]);
         end for;
      end for;
      flg:=0; Cc:=0;
    
      if h eq 1 then
         RR:={x: x in [1..r]};
         RWS:=Subsets(RR,def); 
         RWS:=SetToSequence(RWS);
      end if;

      RmC:=RemoveColumn(DDH,tht);
   
      for k:=1 to #RWS do
         RmCR:=RmC;
         RST:=Sort(SetToSequence(RWS[k]));
         for l:=1 to def do
            RmCR:=RemoveRow(RmCR,RST[def-l+1]); 
         end for;                              
         DDD:=Determinant(RmCR);
   
         Ctddd:=Content(DDD); 
         Append(~Ctlst[h],Ctddd);
         Cc:=GCD(Cc,Content(DDD));
   
         if Cc eq 1 then 
            Ctend[h]:=Content(DDD);
            Append(~Std,k);
            if h eq 1 then 
               Ctstff:=[k,Ctend[1]+1]; Pat:=RST; 
            elif [k,Ctend[2]+1] ne Ctstff then
               Ctstff[#Ctstff]:= 0;
            end if;
            flg+:=1; break; 
         end if;
      end for;

      if flg eq 0 then 
         vprint Large: "Yes modulo",Cc;
         return [1]; 
      end if;
   end for;
   
   MMCR:=RemoveColumn(AP,th);
   RST:=Sort(SetToSequence(RWS[Std[1]]));
   for l:=1 to def do
      MMCR:=RemoveRow(MMCR,RST[def-l+1]);
   end for;
                   
   vprint Large: "No, so calculating a full determinant";
   FP:=Determinant(MMCR);
   
   FP:=P!FP div (Mon);
   Append(~AXS,FP);
   
   if Std[1] eq Std[2] then                
      Append(~AXS,FP);
   else 
      MMCR:=RemoveColumn(AP,th);
      RST:=Sort(SetToSequence(RWS[Std[2]]));
      for l:=1 to def do
         MMCR:=RemoveRow(MMCR,RST[def-l+1]);
      end for;
                   
      vprint Large: "Calculating another full determinant";
      FP:=Determinant(MMCR);
   
      FP:=P!FP div (Mon);
      Append(~AXS,FP);
   end if;
   
   vprint Large: "Looking for other possible homomorphisms";         
   Co:=Coefficients(AXS[2],1); h1:=1;
   
   ip:=1; p:=2; q:=2;
   while p le #Co do
      while q le #Co do
         Cq := [Co[k]: k in [1..q]];
   
         for j:= q+1 to #Co do
            Cq[((j-1) mod q)+1]+:=Co[j];
         end for;
   
         tq:=0; ct:=0; 
         for j:=1 to q do
            ct:=GCD(ct,Evaluate(Cq[j],[1,1]));
            flgag:=0;
            if ct ne 0 then 
               for k:=1 to #PrimeDivisors(ct) do
                  if Ctend[2] mod PrimeDivisors(ct)[k] ne 0 then 
                     flgag+:=1; break;
                  end if;
               end for;
            else 
               flgag+:=1;
            end if;
            if flgag eq 0 then tq+:=1; break; end if;
         end for;
         if tq eq 0 then h1*:=p; end if;
         q*:=p;
      end while;
      ip+:=1; p:=NthPrime(ip); q:=p; 
   end while;
   
   Co:=Coefficients(AXS[1],2); h2:=1;
   
   ip:=1; p:=2; q:=2;
   while p le #Co do
      while q le #Co do
         Cq:=[];
         for k:=1 to q do
            Append(~Cq,Co[k]);
         end for;
         for j:= q+1 to #Co do
            Cq[((j-1) mod q)+1]+:=Co[j];
         end for;
         tq:=0; ct:=0;
         for j:=1 to q do
            ct:=GCD(ct,Evaluate(Cq[j],[1,1]));
            flgag:=0;
            if ct ne 0 then 
               for k:=1 to #PrimeDivisors(ct) do
                  if Ctend[1] mod PrimeDivisors(ct)[k] ne 0 then 
                     flgag+:=1; break;
                  end if;
               end for;
            else 
               flgag+:=1;
            end if;
            if flgag eq 0 then tq+:=1; break; end if;
         end for;
         if tq eq 0 then h2*:=p; end if;
         q*:=p;
      end while;
      ip+:=1; p:=NthPrime(ip); q:=p;
   end while;
   
   vprint Large: "Must be divisors of",[h2,h1];
   
   D1:=Divisors(h1); D2:=Divisors(h2);
   
   Fun:=FunctionField(Integers()); 
   for j:=1 to #D1 do
      for k:=1 to #D2 do
         if GCD(D2[k],D1[j]) eq 1 then
            vprint Large: "Trying",[-D2[k],D1[j]]; 
            cgoa:= 0; 
            Rnghere:=Integers();
            Fld:=FunctionField(Rnghere);
            Hmhere:=hom<P->Fld|Fld.1^-D2[k],Fld.1^D1[j]>;
            ZH:=ZeroMatrix(Fld,r,g);
            for l:=1 to r do
               for m:=1 to g do
                  ZH[l,m]+:=Hmhere(AP[l,m]);
               end for;
            end for;
            flg:=0;
            the:=0;                   
            for l:=1 to g do                      
               if D1[j]*I[l][2]-D2[k]*I[l][1] ne 0 then the:=l; break; end if;
            end for;   
            ZHC:=RemoveColumn(ZH,the);
            for m:=1 to #RWS do
               ZHCR:=ZHC;
               RST:=Sort(SetToSequence(RWS[m]));
               for l:=1 to def do
                  ZHCR:=RemoveRow(ZHCR,RST[def-l+1]); 
               end for;                              
               NDR:=Numerator(Determinant(ZHCR));
               if NDR ne 0 then 
                  Conthere:= Content(PolynomialRing(Rnghere)!NDR);
                  cgoa:=GCD(cgoa,Conthere);
               end if;
               if cgoa eq 1 then 
                  flg+:=1; 
                  if m ne Ctstff[1] or Conthere ne 1 then
                     Ctstff[#Ctstff]:=0;
                  end if;  
                  break;
               end if;
            end for;                   
   
            if flg eq 0 then 
               vprint Large: "Yes modulo",cgoa;
               return [1]; 
            end if;
   
            vprint Large: "Trying",[D2[k],D1[j]];
            cgoa:= 0; 
            Rnghere:=Integers();
   
            Fld:=FunctionField(Rnghere);
            Hmhere:=hom<P->Fld|Fld.1^D2[k],Fld.1^D1[j]>;
            ZH:=ZeroMatrix(Fld,r,g);
            for l:=1 to r do
               for m:=1 to g do
                  ZH[l,m]+:=Hmhere(AP[l,m]);
               end for;
            end for;
            flg:=0;
   
            the:=0;                   
            for l:=1 to g do                      
               if D1[j]*I[l][2]+D2[k]*I[l][1] ne 0 then the:=l; break; end if;
            end for;                        
   
            ZHC:=RemoveColumn(ZH,the);
            for m:=1 to #RWS do
               ZHCR:=ZHC;
               RST:=Sort(SetToSequence(RWS[m]));
               for l:=1 to def do
                  ZHCR:=RemoveRow(ZHCR,RST[def-l+1]); 
               end for;                              
   
               NDR:=Numerator(Determinant(ZHCR));
                      
               if NDR ne 0 then 
                  Conthere:= Content(PolynomialRing(Rnghere)!NDR);
                  cgoa:=GCD(cgoa,Conthere);
               end if;
               if cgoa eq 1 then 
                  flg+:=1; 
                  if m ne Ctstff[1] or Conthere ne 1 then 
                     Ctstff[#Ctstff]:=0; 
                  end if;  
                  break;
               end if;
            end for;
   
            if flg eq 0 then 
               vprint Large: "Yes modulo",cgoa;         
               return [1]; 
            end if;
         end if;
      end for;
   end for;
   
   stdo:=LCM(Ctend[1],Ctend[2]);
   if stdo eq 1 then 
      if Ctstff[#Ctstff] eq 0 then 
         return [0];
      else  
         Append(~Pat,2); 
         return Pat;
      end if; 
   end if;

   Cf:=PrimeDivisors(stdo);
   vprint Large: "Also need to try mod",[Cf];
   for cf:=1 to #Cf do
      vprint Large: "Looking mod",Cf[cf];      
      AXS:=[];      
      Ringyhere:=Integers(Cf[cf]);       
      Polyhere:=PolynomialRing(Ringyhere);
      Polyhere2:=PolynomialRing(Ringyhere,2);
      APC:=ChangeRing(RemoveColumn(AP,th),Polyhere2);
      for h:=1 to 2 do
         for k:=1 to #RWS do
            if Ctlst[h][k] mod Cf[cf] ne 0 then
               APCR:=APC;
               RST:=Sort(SetToSequence(RWS[k]));
               for l:=1 to def do
                  APCR:=RemoveRow(APCR,RST[def-l+1]);
               end for;                          
               vprint Large: "Calculating a full determinant";
               Append(~AXS,Determinant(APCR));
               break; 
            end if;
         end for;
      end for;
            
      vprint Large: "Looking for possible homomorphisms";         
      Co:=Coefficients(AXS[2],1); h1:=1;
      ip:=1; p:=2; q:=2;
      while p le #Co do
         while q le #Co do
            Cq:=[];
            for k:=1 to q do
               Append(~Cq,Co[k]);
            end for;
            for j:= q+1 to #Co do
               Cq[((j-1) mod q)+1]+:=Co[j];
            end for;
            tq:=0; ct:=0; 
            for j:=1 to q do
               if Evaluate(Cq[j],[1,1]) ne 0 then
                  tq+:=1; break;
               end if;
            end for;
            if tq eq 0 then h1*:=p; end if;
            q*:=p;
         end while;
         ip+:=1; p:=NthPrime(ip); q:=p; 
      end while;
   
      Co:=Coefficients(AXS[1],2); h2:=1;
      ip:=1; p:=2; q:=2;
   
      while p le #Co do
         while q le #Co do
            Cq:=[];
            for k:=1 to q do
               Append(~Cq,Co[k]);
            end for;
            for j:= q+1 to #Co do
               Cq[((j-1) mod q)+1]+:=Co[j];
            end for;
   
            tq:=0; ct:=0;
            for j:=1 to q do
               if Evaluate(Cq[j],[1,1]) ne 0 then 
                  tq+:=1; break;
               end if;
            end for;
            if tq eq 0 then h2*:=p; end if;
            q*:=p;
         end while;
         ip+:=1; p:=NthPrime(ip); q:=p;
      end while;
   
      vprint Large: "Must be divisors of",[h2,h1];
      D1:=Divisors(h1); D2:=Divisors(h2);
      Fun:=FunctionField(Ringyhere); 
   
      for j:=1 to #D1 do
         for k:=1 to #D2 do
            if GCD(D2[k],D1[j]) eq 1 then
               Hm:=hom<P->Fun|Fun.1^-D2[k],Fun.1^D1[j]>;
               Hmm:=hom<P->Fun|Fun.1^D2[k],Fun.1^D1[j]>;
               vprint Large: "Trying",[-D2[k],D1[j]];                   
               ZH:=ZeroMatrix(Fun,r,g);
               for l:=1 to r do
                   for m:=1 to g do
                      ZH[l,m]+:=Hm(AP[l,m]);
                   end for;
               end for;
               flg:=0;
   
               the:=0;                   
               for l:=1 to g do                      
                  if D1[j]*I[l][2]-D2[k]*I[l][1] ne 0 then 
                     the:=l; break;
                  end if;
               end for;   
               ZHC:=RemoveColumn(ZH,the);                   
                
               for m:=1 to #RWS do
                  ZHCR:=ZHC;
                  RST:=Sort(SetToSequence(RWS[m]));
                  for l:=1 to def do
                     ZHCR:=RemoveRow(ZHCR,RST[def-l+1]);
                  end for;                          
                  NDR:=Numerator(Determinant(ZHCR));
                  if NDR ne 0 then 
                     flg+:=1; break; 
                  end if;
               end for;
                         
               if flg eq 0 then 
                  vprint Large: "Yes modulo",Cf[cf];
                  return [1]; 
               end if;
   
               vprint Large: "Trying",[D2[k],D1[j]];
               ZH:=ZeroMatrix(Fun,r,g);
               for l:=1 to r do
                  for m:=1 to g do
                     ZH[l,m]+:=Hmm(AP[l,m]);
                  end for;
               end for;

               flg:=0;
               the:=0;                   
               for l:=1 to g do                      
                  if D1[j]*I[l][2]+D2[k]*I[l][1] ne 0 then 
                     the:=l; break;
                  end if;
               end for;   
                           
               ZHC:=RemoveColumn(ZH,the);   
                
               for m:=1 to #RWS do
                  ZHCR:=ZHC;
                  RST:=Sort(SetToSequence(RWS[m]));
                  for l:=1 to def do
                     ZHCR:=RemoveRow(ZHCR,RST[def-l+1]);
                  end for;                          
                  NDR:=Numerator(Determinant(ZHCR));
                  if NDR ne 0 then 
                     flg+:=1; break; 
                  end if;
               end for;
                         
               if flg eq 0 then 
                  vprint Large: "Yes modulo",Cf[cf];
                  return [1]; 
               end if;
            end if;
         end for;
      end for;
   end for;
   return [0]; 
end function;
   
// This function is purely for the case where TFRank=2. 
// It is guaranteed (assuming no bugs, enough time and memory...)
// to find a successful homomorphism, if one or many exist, or to
// confirm that none exist.
// Input is the Alexander matrix, columns and rows, images of the
// generators under abelianisation and the number of a generator 
// with infinite image in the abelianisation.
// This is similar to the function input but does rank calculations directly 
// rather than evaluating many determinants. Can be slow if lots of generators,
// so this is only invoked in place of input if many minors need to be calculated. 
// In practice this will mainly be for tall thin matrices 
// (very few generators/columns but very many relators/rows).
   
function inputm(AP,g,r,I,th)
   Ring:=Integers();
   C:=0;
   
   def:=r-g+1;
   
   P:=PolynomialRing(Ring,2);
   
   MM:=[]; AV:=I[th];
   for h:=1 to 2 do
      if I[th][h] lt 0 then 
         Append(~MM,-I[th][h]); AV[h]:=0;
      else 
         Append(~MM,0);
      end if; 
   end for;
   AV:=ElementToSequence(AV);
   
   Mon:=Monomial(P,MM)-Monomial(P,AV);
   
   Ctlst:=[[],[]]; AXS:=[]; Ctend:=[0,0]; Std:=[]; 
   for h:=1 to 2 do
      Polyhere:=PolynomialRing(Ring);
      if h eq 1 then                           
         vprint Large: "Trying homomorphism [0,1]";
         homhere:=hom<P->Polyhere|1,Polyhere.1>;
         tht:=0;
         for j:=1 to g do
            if I[j][2] ne 0 then tht:=j; break; end if;
         end for;
      else
         vprint Large: "Trying homomorphism [1,0]";
         homhere:=hom<P->Polyhere|Polyhere.1,1>;
         tht:=0;
         for j:=1 to g do
            if I[j][1] ne 0 then tht:=j; break; end if;
         end for;
      end if;
                           
      DDH:=ZeroMatrix(Polyhere,r,g);
      for k:=1 to r do
         for l:=1 to g do
            DDH[k,l]+:=homhere(AP[k,l]);
         end for;
      end for;
   
      RmC:=RemoveColumn(DDH,tht);
      Plyh2:=PolynomialRing(Integers(2));
      RmC2:=ChangeRing(RmC,Plyh2);
      if Rank(RmC2) ne g-1 then 
         vprint Large: "Yes modulo 2 (and possibly more)";
         return [1]; 
      else
         FoF:=FieldOfFractions(Polyhere);
         RmCF:=ChangeRing(RmC,FoF);
         EF,TM:=EchelonForm(RmCF);
         Ctntp:=LCM([Content(Denominator(e)): e in Eltseq(TM)| e ne 0]);
         Ctntpd:=PrimeDivisors(Ctntp);
         vprint Large: "Also checking the primes",Ctntpd;
                                                       
         for cf:=1 to #Ctntpd do         
            vprint Large: "Prime now is",Ctntpd[cf];
            Ringy:=Integers(Ctntpd[cf]);
            PRingy:=PolynomialRing(Ringy); 
            EFP:=ChangeRing(RmC,PRingy);
            if Rank(EFP) ne g-1 then 
               vprint Large: "Yes modulo",Ctntpd[cf]; 
               return [1]; 
            end if;
         end for;
      end if;
                      
      vprint Large: "No, so finding a full determinant";
      Ctstff:=[0]; 
      Cc:=0; RwsD:=[[],[]];
      flg:=0;
      while Cc ne 1 do               
         Rn:=[];  RmCR:=RmC;
         for l:=1 to def do
            Rne:=Random([1..r+1-l]); 
            Append(~Rn,Rne);
            RmCR:=RemoveRow(RmCR,Rne); 
         end for;                              
         DDD:=Determinant(RmCR); 
         Ctddd:=Content(DDD); 
         Append(~Ctlst[h],Ctddd);
         Append(~RwsD,Rn);                    
         Cc:=GCD(Cc,Content(DDD));
         if Cc eq 1 then 
            Ctend[h]:=Content(DDD);
            Append(~Std,Rn);
            flg+:=1; break; 
         end if;
      end while;
      Ctstff:=[0];
   end for;

   for h:=1 to 2 do                  
      Rn:=Std[h];
      MMCR:=RemoveColumn(AP,th);
      for l:=1 to def do
         MMCR:=RemoveRow(MMCR,Std[h][l]);
      end for;
      vprint Large: "Calculating a full determinant number",h;
   
      FP:=Determinant(MMCR);
      FP:=P!FP div (Mon);
      Append(~AXS,FP);
   end for;
   
   vprint Large: "Looking for other possible homomorphisms";
   
   Co:=Coefficients(AXS[2],1); h1:=1;
   ip:=1; p:=2; q:=2;

   while p le #Co do
      while q le #Co do
         Cq:=[];
         for k:=1 to q do
            Append(~Cq,Co[k]);
         end for;
   
         for j:= q+1 to #Co do
            Cq[((j-1) mod q)+1]+:=Co[j];
         end for;
   
         tq:=0; ct:=0; 
         for j:=1 to q do
            ct:=GCD(ct,Evaluate(Cq[j],[1,1]));
            flgag:=0;
            if ct ne 0 then 
               for k:=1 to #PrimeDivisors(ct) do
                  if Ctend[2] mod PrimeDivisors(ct)[k] ne 0 then 
                     flgag+:=1; break;
                  end if;
               end for;
            else 
               flgag+:=1;
            end if;
           if flgag eq 0 then tq+:=1; break; end if;
         end for;
         if tq eq 0 then h1*:=p; end if;
         q*:=p;
      end while;
      ip+:=1; p:=NthPrime(ip); q:=p; 
   end while;
   
   Co:=Coefficients(AXS[1],2); h2:=1;
   
   ip:=1; p:=2; q:=2;
   
   while p le #Co do
      while q le #Co do
         Cq:=[];
         for k:=1 to q do
            Append(~Cq,Co[k]);
         end for;
   
         for j:= q+1 to #Co do
            Cq[((j-1) mod q)+1]+:=Co[j];
         end for;
         tq:=0; ct:=0;
         for j:=1 to q do
            ct:=GCD(ct,Evaluate(Cq[j],[1,1]));
            flgag:=0;
            if ct ne 0 then 
               for k:=1 to #PrimeDivisors(ct) do
                  if Ctend[1] mod PrimeDivisors(ct)[k] ne 0 then 
                     flgag+:=1; break;
                  end if;
               end for;
            else 
               flgag+:=1;
            end if;
            if flgag eq 0 then tq+:=1; break; end if;
         end for;
         if tq eq 0 then h2*:=p; end if;
         q*:=p;
      end while;
      ip+:=1; p:=NthPrime(ip); q:=p;
   end while;
   
   vprint Large: "Must be divisors of",[h2,h1];
   
   D1:=Divisors(h1); D2:=Divisors(h2);
   for j:=1 to #D1 do
      for k:=1 to #D2 do
         if GCD(D2[k],D1[j]) eq 1 then
            vprint Large: "Trying",[-D2[k],D1[j]];
            Hmhere:=hom<P->FoF|FoF.1^-D2[k],FoF.1^D1[j]>;
            ZH:=ZeroMatrix(FoF,r,g);
            for l:=1 to r do
               for m:=1 to g do
                   ZH[l,m]+:=Hmhere(AP[l,m]);
               end for;
            end for;
   
            the:=0;                   
            for l:=1 to g do                      
               if D1[j]*I[l][2]-D2[k]*I[l][1] ne 0 then the:=l; break; end if;
            end for;   
            ZHC:=RemoveColumn(ZH,the);
            if Rank(ZHC) ne g-1 then 
               vprint Large: "Yes modulo 0";
               return [1]; 
            else
               EF,TM:=EchelonForm(ZHC);
               Ctntp:=LCM([Content(
               Denominator(e)): e in Eltseq(TM)| e ne 0]);
               Ctntpd:=PrimeDivisors(Ctntp);
               vprint Large: "Also checking the primes",Ctntpd;
                                                       
               for cf:=1 to #Ctntpd do         
                  vprint Large: "Prime now is",Ctntpd[cf];
                  Ringy:=Integers(Ctntpd[cf]);
                  PRingy:=PolynomialRing(Ringy); 
                  FoFp:=FieldOfFractions(PRingy);
                  EFP:=EchelonForm(ChangeRing(ZHC,FoFp));
                  if Rank(EFP) ne g-1 then
                     vprint Large: "Yes modulo",Ctntpd[cf]; 
                     return [1]; 
                  end if;
               end for;
            end if;

            vprint Large: "Trying",[D2[k],D1[j]];
            Hmhere:=hom<P->FoF|FoF.1^D2[k],FoF.1^D1[j]>;
            ZH:=ZeroMatrix(FoF,r,g);
            for l:=1 to r do
               for m:=1 to g do
                  ZH[l,m]+:=Hmhere(AP[l,m]);
               end for;
            end for;
   
            the:=0;                   
            for l:=1 to g do                      
               if D1[j]*I[l][2]+D2[k]*I[l][1] ne 0 then 
                  the:=l; break;
               end if;
            end for;                        
   
            ZHC:=RemoveColumn(ZH,the);
   
            if Rank(ZHC) ne g-1 then 
               vprint Large: "Yes modulo 0";
               return [1]; 
            else
               EF,TM:=EchelonForm(ZHC);
               Ctntp:=LCM([Content(Denominator(e)): e in Eltseq(TM)| e ne 0]);
               Ctntpd:=PrimeDivisors(Ctntp);
               vprint Large: "Also checking the primes",Ctntpd;
                                                       
               for cf:=1 to #Ctntpd do         
                  vprint Large: "Prime now is",Ctntpd[cf];
                  Ringy:=Integers(Ctntpd[cf]);
                  PRingy:=PolynomialRing(Ringy); 
                  FoFp:=FieldOfFractions(PRingy);
                  EFP:=EchelonForm(ChangeRing(ZHC,FoFp));
                  if Rank(EFP) ne g-1 then
                     vprint Large: "Yes modulo",Ctntpd[cf]; 
                     return [1]; 
                  end if;
               end for;
            end if;
         end if;
      end for;
   end for;
   
   stdo:=GCD(Ctend[1],Ctend[2]);
   if stdo eq 1 then 
      if Ctstff[#Ctstff] eq 0 then 
         return [0]; 
      else 
         Append(~Pat,2); 
         return(Pat);
      end if; 
   end if;
   
   Cf:=PrimeDivisors(stdo);
   vprint Large: "Also need to try mod",[Cf];
   for cf:=1 to #Cf do
      vprint Large: "Looking mod",Cf[cf];      
      AXS:=[];      
   
      Ringyhere:=Integers(Cf[cf]);       
      Polyhere:=PolynomialRing(Ringyhere);
      Polyhere2:=PolynomialRing(Ringyhere,2);
      FoFp:=FieldOfFractions(Polyhere); 
      APC:=ChangeRing(RemoveColumn(AP,th),Polyhere2);
      for h:=1 to 2 do
         for k:=1 to #Ctlst[h] do
            if Ctlst[h][k] mod Cf[cf] ne 0 then
               APCR:=APC;
               for l:=1 to def do
                  APCR:=RemoveRow(APCR,RwsD[h][k][l]);
               end for;
               vprint Large: "Calculating full determinant number",h;  
               Append(~AXS,Determinant(APCR));
               break;
            end if;
         end for;
      end for;

      vprint Large: "Looking for possible homomorphisms";         
      Co:=Coefficients(AXS[2],1); h1:=1;
  
      ip:=1; p:=2; q:=2;
      while p le #Co do
         while q le #Co do
            Cq:=[];
            for k:=1 to q do
               Append(~Cq,Co[k]);
            end for;
            for j:= q+1 to #Co do
               Cq[((j-1) mod q)+1]+:=Co[j];
            end for;
   
            tq:=0; ct:=0; 
            for j:=1 to q do
               if Evaluate(Cq[j],[1,1]) ne 0 then
                  tq+:=1; break;
               end if;
            end for;
            if tq eq 0 then h1*:=p; end if;
            q*:=p;
         end while;
         ip+:=1; p:=NthPrime(ip); q:=p; 
      end while;
   
      Co:=Coefficients(AXS[1],2); h2:=1;
      ip:=1; p:=2; q:=2;
      while p le #Co do
         while q le #Co do
            Cq:=[];
            for k:=1 to q do
               Append(~Cq,Co[k]);
            end for;
            for j:= q+1 to #Co do
               Cq[((j-1) mod q)+1]+:=Co[j];
            end for;
            tq:=0; ct:=0;
            for j:=1 to q do
               if Evaluate(Cq[j],[1,1]) ne 0 then 
                  tq+:=1; break;
               end if;
            end for;
            if tq eq 0 then h2*:=p; end if;
            q*:=p;
         end while;
         ip+:=1; p:=NthPrime(ip); q:=p;
      end while;
   
      vprint Large: "Must be divisors of",[h2,h1];
   
      D1:=Divisors(h1); D2:=Divisors(h2);
      for j:=1 to #D1 do
         for k:=1 to #D2 do
            if GCD(D2[k],D1[j]) eq 1 then
               Hm:=hom<P->FoFp|FoFp.1^-D2[k],FoFp.1^D1[j]>;
               Hmm:=hom<P->FoFp|FoFp.1^D2[k],FoFp.1^D1[j]>;
               vprint Large: "Trying",[-D2[k],D1[j]];                   
               ZH:=ZeroMatrix(FoFp,r,g);
               for l:=1 to r do
                  for m:=1 to g do
                     ZH[l,m]+:=Hm(AP[l,m]);
                  end for;
               end for;
   
               the:=0;                   
               for l:=1 to g do                      
                  if D1[j]*I[l][2]-D2[k]*I[l][1] ne 0 then 
                     the:=l; break;
                  end if;
               end for;   
                          
               ZHC:=RemoveColumn(ZH,the);                   
   
               if Rank(ZHC) ne g-1 then 
                  vprint Large: "Yes modulo Cf[cf]";
                  return [1]; 
               end if;
   
               vprint Large: "Trying",[D2[k],D1[j]];
               ZH:=ZeroMatrix(FoFp,r,g);
               for l:=1 to r do
                  for m:=1 to g do
                     ZH[l,m]+:=Hmm(AP[l,m]);
                  end for;
               end for;
               the:=0;                   
               for l:=1 to g do                      
                  if D1[j]*I[l][2]+D2[k]*I[l][1] ne 0 then 
                     the:=l; break;
                  end if;
               end for;   
                           
               ZHC:=RemoveColumn(ZH,the);   
               if Rank(ZHC) ne g-1 then 
                  vprint Large: "Yes modulo",Cf[cf];
                  return [1]; 
               end if;
            end if;
         end for;
      end for;
   end for;
   return [0]; 
end function;
   
// General "management and evaluation" program for the largeness routines.
// Input is a group presentation 
// Aim is to find a "successful homomorphism" - a homomorphism from
// the input group to Z with an Alexander polynomial that is 0 over
// Z (we say 0 mod 0) or over some prime p (0 mod p). 
// First it checks for standard cases, then builds the Alexander
// matrix, as well as finding a generator with infinite image in 
// the abelianisation (because that column can then be deleted
// before evaluating a determinant). 

// If TFRank=2 then it calls the function input, or inputm if the number
// of choices of rows to delete is big.
// If TFRank=3 then it reduces to TFRank=2 and then calls input or inputm
// three times to check homomorphisms with a zero coefficient; 
// first ones of the form [x,y,0], then [x,0,y] and then [0,x,y]. 
// If the same determinant happens to have been used throughout 
// and was always unsuccessful (and there are not too many rows to delete) 
// then it calls function cray to look for other homomorphisms. 
   
// If TFRank=1 then the input integer C will be non-zero, meaning
// that the homomorphism onto Z (which is unique up to sign)
// can only be zero modulo primes p dividing C. Therefore we can
// work in (Z/pZ)[t] and do a rank calculation directly which should
// be fast. For all other TFRanks, the input C is currently 0 but
// has been left there in case of further information being available
// via pre-computation on the group presentation.
   
// If TFRank is 4 or more then it merely looks at the canonical
// homomorphisms [1,0,...,0] etc. This may seem lazy but computation
// with multivariates of high degree is expensive.
// For each of the t homomorphisms it first does a direct rank calculation 
// over (Z/2Z)[t] and then (if unsuccessful) tries out the homomorphism in 
// general using determinants (if there are not too many rows to delete). 
   
function fabno(G,C)
   Z:=Integers();
   if C eq 0 then Ring:=Z; else Ring:=Integers(C); end if;
   
   A,f:=AbelianQuotient(G);
   B:=AQInvariants(G);
   a:=#B;
   t:=TorsionFreeRank(G);
   
   if a in [0,1] or t eq 0 then return 0; end if;
   if C eq 0 and t eq 1 then C:=B[a-1]; end if;
   
   R:=[]; g:=#Generators(G);
   Rels:=Relations(G);
   Rels:=[LHS(r) * RHS(r)^-1: r in Rels]; 
   R:=[Eltseq(r): r in Rels];

   r:=#R; def:=r-g+1;
   
   if g-r ge 2 then 
      vprint Large: "Yes by Baumslag-Pride"; 
      return 1;
   end if;
   
   P:=PolynomialRing(Ring,t);
   I:=ZeroMatrix(Z,g,t);
   
   for i:=1 to g do
      J:=ElementToSequence(f(G.i));
      for j:=1 to a-t do
         J:=Remove(J,1);
      end for; 
      J:=Vector(J);
      I[i]:=J;
   end for;
   
   AP:=ZeroMatrix(P,#R,g); 
   z:=ZeroMatrix(Z,1,t); 
   u:=[1: h in [1..t]];
   
   for h:=1 to #R do
      v:=z[1]; M:=v; m:=v;
      AM:=[]; AN:=[];
      for i:=1 to g do
      Append(~AM,[]); Append(~AN,[]); 
      end for;
   
      for j:=1 to #R[h] do
         if R[h,j] gt 0 then   
            p:=Index(AM[R[h,j]],v);
            if p eq 0 then 
               Append(~AM[R[h,j]],v); 
               Append(~AN[R[h,j]],1);
            else 
               AN[R[h,j],p]+:=1;
            end if;
            v+:=I[R[h,j]]; 
            for k:=1 to t do
               if m[k] gt v[k] then m[k]:=v[k]; end if;
               if M[k] lt v[k] then M[k]:=v[k]; end if;
            end for;
         else  
            v-:=I[-R[h,j]];  
            for k:=1 to t do
               if m[k] gt v[k] then m[k]:=v[k]; end if;
               if M[k] lt v[k] then M[k]:=v[k]; end if;
            end for;
     
            p:=Index(AM[-R[h,j]],v);
            if p eq 0 then 
               Append(~AM[-R[h,j]],v); Append(~AN[-R[h,j]],-1);
            else 
               AN[-R[h,j],p]-:=1;
            end if;
         end if;
      end for;   
   
      for j:=1 to g do
         for k:=1 to #AM[j] do AM[j,k]-:=m; end for;                     
      end for;
   
      for j:=1 to g do
         for k:=1 to #AM[j] do
            AP[h,j]+:=AN[j,k]*Monomial(P,ElementToSequence(AM[j,k]));
         end for;
      end for;
   end for;
   
   th:=0;
   for h:=1 to g do
      if I[h] ne 0 then th:=h; break; end if;
   end for;
   
   Bi:=Binomial(r,def);
   
   if t eq 2 then
      vprint Large: "Testing for homomorphisms";
      if Bi le Limit then 
         Inp:=input(AP,g,r,I,th);
      else 
         Inp:=inputm(AP,g,r,I,th);    
      end if;
      return(Inp[#Inp]);
   end if;
   
   if t eq 3 then 
      Q:=PolynomialRing(Ring,2);
      vprint Large: "Trying homomorphisms of form [x,y,0]";
      I3:=RemoveColumn(I,3);
      th3:=0;
      for i:=1 to g do
         if I3[i] ne 0 then th3:=i; break; end if;
      end for;
      Hom:=hom<P->Q|Q.1,Q.2,1>;
      DDH:=ZeroMatrix(Q,r,g);
      for k:=1 to r do
         for l:=1 to g do
            DDH[k,l]+:=Hom(AP[k,l]);
         end for;
      end for;
   
      if Bi le Limit then 
         ret3:=input(DDH,g,r,I3,th3); 
      else 
         ret3:=inputm(DDH,g,r,I3,th3);
      end if;
   
      if ret3[#ret3] eq 1 then return 1; end if;
   
      vprint Large: "Trying homomorphisms of form [x,0,y]";
      I2:=RemoveColumn(I,2);
      th2:=0;
      for i:=1 to g do
         if I2[i] ne 0 then th2:=i; break; end if;
      end for;
   
      Hom:=hom<P->Q|Q.1,1,Q.2>;         
   
      DDH:=ZeroMatrix(Q,r,g);
      for k:=1 to r do
         for l:=1 to g do DDH[k,l]+:=Hom(AP[k,l]); end for;
      end for;
   
      if Bi le Limit then 
         ret2:=input(DDH,g,r,I2,th2); 
      else 
         ret2:=inputm(DDH,g,r,I2,th2);         
      end if;
   
      if ret2[#ret2] eq 1 then return 1; end if;
   
      vprint Large: "Trying homomorphisms of form [0,x,y]";
      I1:=RemoveColumn(I,1);
      th1:=0;
      for i:=1 to g do
         if I1[i] ne 0 then th1:=i; break; end if;
      end for;
   
      Hom:=hom<P->Q|1,Q.1,Q.2>;         
   
      DDH:=ZeroMatrix(Q,r,g);
      for k:=1 to r do
         for l:=1 to g do DDH[k,l]+:=Hom(AP[k,l]); end for;
      end for;
   
      if Bi le Limit then 
         ret1:=input(DDH,g,r,I1,th1); 
      else 
         ret1:=inputm(DDH,g,r,I1,th1);
      end if;
   
      if ret1[#ret1] eq 1 then return 1; end if;
   
      if Bi le Limit and ret3[#ret3] eq 2 and 
         ret3 eq ret2 and ret3 eq ret1 then 
         vprint Large: "Are there other homomorphisms worth trying?";          
         MM:=[]; AV:=I[th];
         for h:=1 to 3 do
            if I[th][h] lt 0 then 
               Append(~MM,-I[th][h]); AV[h]:=0;
            else 
               Append(~MM,0);
            end if; 
         end for;
         AV:=ElementToSequence(AV);
         Mon:=Monomial(P,MM)-Monomial(P,AV);
         MMCR:=RemoveColumn(AP,th);
         for l:=1 to def do
            MMCR:=RemoveRow(MMCR,ret3[def+1-l]);
         end for;
         FP:=Determinant(MMCR);
         FP:=P!FP div (Mon);
         Try:=cray(FP,t); 
         if #Try eq 1 then return 0; end if;
         RR:={x: x in [1..r]};
         RWS:=Subsets(RR,def);
         RWS:=SetToSequence(RWS);
         RST:=Sort(SetToSequence(RWS[1]));
         F:=FunctionField(Ring);
         HH:=[];
         for i:=1 to t do
            Append(~HH,F.1^Try[i]);
         end for;
         trr:=hom<P->F|HH>;      
         DDH:=ZeroMatrix(F,r,g);
         for k:=1 to r do
            for l:=1 to g do DDH[k,l]+:=trr(AP[k,l]); end for;
         end for;
   
         DmC:=RemoveColumn(DDH,th);
         if Rank(ChangeRing(DmC,PolynomialRing(Integers(2)))) ne g-1 then
            vprint Large: "Yes modulo 2 (and possibly more)";
            return 1;
         end if;

         ct:=0;
         for i:=1 to #RWS do
            DmCR:=DmC;
            RST:=Sort(SetToSequence(RWS[i]));          
            for h:=1 to def do
                DmCR:=RemoveRow(DmCR,RST[def-h+1]);
            end for;
            PP:=Determinant(DmCR);
            ct:=GCD(ct,Content(PP));
            if ct eq 1 then break; end if;
          end for;
   
          if ct ne 1 then 
             vprint Large: "Yes modulo",ct;
              return 1; 
          end if;
      end if;
   end if;
   
   if t eq 1 then 
      Cf:=PrimeDivisors(C); 
      vprint Large: "Testing that homomorphism";
      vprint Large: "Will try primes",Cf;
      for cf:=1 to #Cf do         
         vprint Large: "Prime now is",Cf[cf];
         Ringy:=Integers(Cf[cf]);
         PRingy:=PolynomialRing(Ringy); 
         RmC:=Matrix(PRingy,AP);
         RmC:=RemoveColumn(RmC,th);
         if Rank(RmC) lt g-1 then 
            vprint Large: "Yes, prime",Cf[cf],"worked";
            return 1; 
         end if;
      end for;
   end if;
   
   if t gt 3 then
      Bi:=Binomial(r,def);
      if Bi le Limit then
         RR:={x: x in [1..r]};
         RWS:=Subsets(RR,def);
         RWS:=SetToSequence(RWS);
         RST:=Sort(SetToSequence(RWS[1]));
      end if;
   
      Phere:=PolynomialRing(Ring);
      for s:=1 to t do
         Im:=[]; ct:=0; Hm:=[];   
         for j:=1 to t do
            if j eq s then 
               Append(~Im,Phere.1); Append(~Hm,1); 
            else 
               Append(~Im,Phere!1); Append(~Hm,0);
            end if;
         end for;
   
         vprint Large: "Trying homomorphism",Hm;                 
         homhere:=hom<P->Phere|Im>;
   
         DDH:=ZeroMatrix(Phere,r,g);
         for k:=1 to r do
            for l:=1 to g do
               DDH[k,l]+:=homhere(AP[k,l]);
            end for;
         end for;
    
         thh:= 0;
         for j:=1 to g do
            if I[j][s] ne 0 then thh:=j; break; end if;
         end for;             
         DmC:=RemoveColumn(DDH,thh);
   
         if Rank(ChangeRing(DmC,PolynomialRing(Integers(2)))) ne g-1 then
            vprint Large: "Yes modulo 2 (and possibly more)";
            return 1;
         end if;
   
         if Bi le Limit then  
            for i:=1 to #RWS do
               DmCR:=DmC;
               RST:=Sort(SetToSequence(RWS[i]));          
               for h:=1 to def do
                  DmCR:=RemoveRow(DmCR,RST[def-h+1]);
               end for;
               PP:=Determinant(DmCR);
               ct:=GCD(ct,Content(PP));
               if ct eq 1 then break; end if;
            end for;
            if ct ne 1 then 
              vprint Large: "Yes modulo",ct;
              return 1; 
            end if;
         end if; 
      end for;
   end if;
   
   return 0; 
end function;
   
// Search for promising subgroups of the input
// finitely-presented group G with index between MinIndex and MaxIndex 
// (or very small index sub-subgroup of such a subgroup).
// Promising means having a homomorphism onto the integers Z.
// Program first takes the input presentation and gets the
// list of subgroups of a specified index. It tests any having homomorphism(s) 
// onto the integers. This is equivalent to having torsion free rank (TFRank) > 0.
// If TFRank is 1 then there must be non-trivial torsion 
// too because in this case the Alexander polynomial of the 
// homomorphism to Z (unique up to sign) can only vanish modulo
// primes that divide the order of the torsion subgroup.
// For each index, a "best" subgroup B is chosen by (crudely) scoring
// its AbelianQuotientInvariants. One then gets, subindex by
// subindex, all subgroups of B of this subindex (referred to as
// sub-subgroups) and tests any suitable sub-subgroups.
// This goes on for subindices up to the current index of B
// We do not rewrite (and therefore do not test for homomorphisms) 
// any sub-subgroups whose abelianisation has a torsion subgroup 
// with large exponent as this can be slow. 
   
intrinsic IsLarge (G:: GrpFP, MinIndex :: RngIntElt, MaxIndex :: RngIntElt : 
Simplify := true, MaxExponent := 10^5, TimeLimit := 10) -> BoolElt, GrpFP 
{A finitely presented group G is large if it has a finite index
subgroup that has a surjective homomorphism to a nonabelian free group.
We attempt to decide if G is large by calculating the (multivariable) 
Alexander polynomial of those subgroups H of G having index h in 
[MinIndex..MaxIndex], and also subgroups of H having index up to 2*h in G.
If the abelian torsion for a subgroup H is larger than MaxExponent, 
then we do not rewrite to obtain a presentation for H. If we prove that 
G is large, then return true and a subgroup which is a witness to this 
property. Otherwise we return false, but this implies only that we could 
not decide this property for G. If Simplify, then use Simplify as flag 
for rewriting of presentations for subgroups.  If, in computing low index 
subgroups of a finite index subgroup H of G, the low-index subgroup 
calculation takes more than TimeLimit in seconds, then abort without trying 
to find more subgroups of H.
}
   m := MinIndex; 
   l := MaxIndex;
   rew := Simplify;
   
   if m eq 1 then 
      m+:=1;
      A:=AQInvariants(G);
      vprint Large: "Index",1;
      vprint Large: "AQInvariants",A;
      if #A ge 2 then 
         if A[#A] eq 0 then 
            fab:=fabno(G,A[#A-1]);
            if fab eq 1 then return true, G; end if;
         end if;
      end if;
   end if; 
   
   for i:=m to l do
      vprint Large: "Determine subgroups of G of index",i;
      L:=LowIndexSubgroups(G,<i,i>);
      vprint Large: "There are",#L,"subgroups of index",i;
      if #L eq 0 then continue; end if;
      bs:=0; bn:=0; fbu:=0; BQ:=[];

      for j:=1 to #L do
         if HasComputableAbelianQuotient(L[j]) eq true then 
            A:=AQInvariants(L[j]); a:=#A; 
         else 
            continue j; 
         end if;
         sc:=0;  
         for k:=1 to a do
            if A[k] eq 0 then sc+:=2; else sc+:=1; end if;
         end for;
         if a ge 2 and A[a] eq 0 then
            vprint Large: "Rewriting number",j,"with AQInvariants",A; 
            fbu+:=1; 
            W:=Rewrite(G,L[j]:Simplify:=rew);
            vprint Large: #Generators(W),"generators,",#Relations(W),"relators";
            if fabno(W,A[a-1]) eq 1 then return true, L[j]; end if;
         end if;
         if sc gt bs then 
            bs:=sc; bn:=j; BQ:=A;
            if a ge 2 and A[a] eq 0 then M:=W; end if;                
         elif sc eq bs then 
            if a ne 0 and A[a] eq 0 and #BQ ne 0 and BQ[#BQ] ne 0 then
               bn:=j; BQ:=A;
               if a ge 2 and A[a] eq 0 then M:=W; end if;
            end if;
         end if; 
      end for;

      if bn eq 0 then continue; end if;
      vprint Large: "Using subgroup number",bn,"with AQInvariants",BQ;    
      if fbu eq 0 then 
         vprint Large: "Rewriting number",bn;
         M:=Rewrite(G,L[bn]:Simplify:=rew); 
         vprint Large: #Generators(M),"generators,",#Relations(M),"relators";
      end if;

      // investigate subgroups of M having index at most i 
      for j:=2 to i do
         t:=Cputime();   
         LM:=LowIndexSubgroups(M,<j,j>);
         s:=Cputime(t);
         vprint Large: "There are",#LM,"sub-subgroups of subindex",j; 
         for k:=1 to #LM do 
            AQP:=AQPrimes(LM[k]);
            if AQP eq [0] and HasComputableAbelianQuotient(LM[k]) eq true then
               AQQ:=AQInvariants(LM[k]); 
               if #AQQ ge 2 then 
                  vprint Large: "Trying sub-subgroup #",k, "with AQI",AQQ;
                  // torsion-free rank 
                  tfr:=#[a:a in AQQ|a eq 0];
                  // exponent of torsion subgroup 
                  tr:=Maximum (AQQ);
                  if tr le MaxExponent then 
                     vprint Large: "Now rewriting ...";
                     R:=Rewrite(M,LM[k]:Simplify:=rew); 
                     vprint Large: #Generators(R),"generators,",#Relations(R),"relators";
                     if fabno(R,AQQ[#AQQ-1]) eq 1 then return true, LM[k]; end if;
                  else 
                     vprint Large: "Torsion too large so will not rewrite";
                  end if;
               end if;
            end if;
         end for;
         if s gt TimeLimit then 
            vprint Large: "Finding subgroups took too long so now breaking";
            break; 
         end if;
      end for;
   end for;
   return false, _;
end intrinsic;
