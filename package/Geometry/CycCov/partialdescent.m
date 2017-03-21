freeze;
/******************************************************************

partialdescent.m
Michael Mourao
November 2011


Intrinsics for performing a partial descent on a cyclic cover of P^1
of the form y^q = f(x)

******************************************************************/

/**** Changes:

+ Nov2011 Brendan
	changed verbosity
	added intrinsics


	
***/






/*-
k:=NumberField(x-1 : DoLinearExtension:=true);
Rk:=PolynomialRing(k);
K1:=NumberField(Rk!(x-1) : DoLinearExtension:=true);
RK1:=PolynomialRing(K1);
K2:=NumberField(Rk!(x^2-x+3));
RK2:=PolynomialRing(K2);
seq:=[*k!1,Factorisation(CyclotomicPolynomial(11),K2)[1,1],RK1!(x-1)*];
seq;
f:=Rk!(x^11-1);
load "partialdescentfastsydney.m";
descent_1(2,seq,f);
-*/

zp_soluble:= function(reps,pi,units,FFtounits,qt3,unitsmodq,FF,toFF,badprimes,K,q,coef,X,Y,p,k)

/*   if (((Integers()!Norm(p)-1) mod q) ne 0) and (p notin badprimes) then
      return true;
   else*/
      if (p notin badprimes) then
         for x in X do
            x0:=x;
            fx0:=&+[coef[i]@toFF*x0^(i-1)  : i in [1..#coef]];
        /*    if fx0 ne Codomain(toFF)!0 then
               fmodq:=(fx0)@@FFtounits@qt3;
            else
               fmodq:=Identity(unitsmodq);
            end if;*/
            if IsPower(fx0,q) then
               return true;
            else
               return false;
            end if;
         end for;
      else
	      Rf:=PolynomialRing(Integers(K));
	      f:=Rf!coef;	
	      g:=Derivative(f);
         for x in X do
	         x0:=K!x;

 /*           if (k eq 1) and (Valuation(Evaluate(g,x0),p) eq 0)  then
               if ((Integers()!Norm(p)-1) mod q) ne 0 then
                  return true;
               else
                  fx0:=&+[(coef[i]*x0^(i-1))@toFF  : i in [1..#coef]];
                  if fx0 ne Codomain(toFF)!0 then
                     fmodq:=(fx0)@@FFtounits@qt3;
                  else
                     fmodq:=Identity(unitsmodq);
                  end if;
                  if fmodq eq Identity(unitsmodq) then
                     return true;
                  else
                     return false;
                  end if;
               end if;              
            end if;*/
     //       for elt in FF do       
    //           y0:=y+elt@@toFF*pi^(k-1);
    //        for elt in CartesianPower(FF,k) do
    //           y0:=&+[(elt[i]@@toFF)*pi^(i-1) : i in [1..k]];
            for y in Y do
               y0:=K!y;
 //              printf "testing if (%o,%o) lifts.\n",x0,y0;   
               n:=Valuation((y0^q-Evaluate(f,x0)),p);
               m:=Min([Valuation(Evaluate(g,x0),p),Valuation((q*y0^(q-1)),p)]);
 //              printf "(n,m,k)=(%o,%o,%o).\n",n,m,k;
               if (k gt 0) and (n gt 2*m) and (k le (n-m)) then
 //                 printf "(%o,%o) lifted!\n",x0,y0;
                  return true; 
               else
                  if (k gt 0) and (n ge 500) then
	                  return true;
                  else 
	                  if  (k eq 0) or ((n le 2*m) and (n ge 2*k)) then
   //                     print "going in a loop";
			               if $$(reps,pi,units,FFtounits,qt3,unitsmodq,FF,toFF,badprimes,K,q,coef,[x0+a1*pi^k : a1 in reps],[y0+b1*pi^k : b1 in reps],p,k+1) then 
                           return true;
			               end if;
	                  end if;
                  end if;
               end if;
            end for;
         end for;
	      return false;
      end if;
//   end if;
					
end function;

selmer_3:=function(Map,K,q,p,f,fields,th,rings,polyrings,nf,poly)
   _,pi:=IsPrincipal(p);
 //  QNF:=NumberField(PolynomialRing(Rationals()).1-1: DoLinearExtension);
 //  F:=Polynomial(QNF,f);
 //  QQ:=BaseRing(Parent(F));
   OK:=Integers(K);

   R := PolynomialRing(K); x := R.1;
   ffactored:=f;
   lead :=LeadingCoefficient(poly);
   
   factors:=ffactored;
   f:=R!poly;
   coefs:=Coefficients(f);
   lead:=coefs[#coefs];
   O:=rings;
   RK:=polyrings;

   g1:=[* *];
   g2:=[* *];
   primes:=[* *];
   mapsKGP:=[* *];
   groupsGP:=[];
   localfields:=[* *];
   localmaps:=[**];
   selmermaps:=[* *];
   Gp:=[ ];
   inc:=[* *];
   pr:=[* *];
   N:=[* *];
   if (Degree(f) mod q) eq 0 then
      coef2:=[Coefficients(f)[#Coefficients(f)-i]: i in [0..#Coefficients(f)-1]];
   else
      coef2:=Eltseq(R!Evaluate(R!Reverse(Coefficients(f)),R.1^q));
   end if;
      
   f2:=R!coef2;
   for j in [1..nf] do

	   Fac:=Factorisation(RK[j]!f);
	   g1[j]:=RK[j]!(RK[j]!f/(RK[j]!factors[j]));
      if (Degree(f) mod q) eq 0 then
	      coef3:=[Coefficients(g1[j])[#Coefficients(g1[j])-i]: i in [0..#Coefficients(g1[j])-1]];
	      g2[j]:=RK[j]!coef3;
      else
         coef3:=Eltseq(RK[j]!Evaluate(RK[j]!Reverse(Coefficients(g1[j])),RK[j].1^q));
         g2[j]:=RK[j]!coef3;
      end if;

      localfields[j]:=[**];
      localmaps[j]:=[**];
      groupsGP[j]:=[];
      mapsKGP[j]:=[**];
      selmermaps[j]:=[**];
 
	   primes[j]:=[P: P in Support(pi*O[j])];
      for P in primes[j] do
         localfield,localmap:=Completion(fields[j],P);
         selmergroup,selmermap:=pSelmerGroup(q,localfield);
         localfields[j]:=localfields[j] cat [* localfield *];
         localmaps[j]:=localmaps[j] cat [* localmap *];
         groupsGP[j]:=groupsGP[j] cat [ selmergroup ];
         selmermaps[j]:=selmermaps[j] cat [* selmermap *];
	      mapsKGP[j]:=mapsKGP[j] cat [* localmap*selmermap *];
      end for;

	   Gp[j],inc[j],pr[j]:=DirectSum(groupsGP[j]);
	   N[j]:=#primes[j];
   end for;

   GP,INC,PR:=DirectSum(Gp);
   if (Degree(f) mod q) eq 0 then
      localfield,localmap:=Completion(K,p);
      GQp,mapQGQp1:=pSelmerGroup(q,localfield);
      mapQGQp:=localmap*mapQGQp1;

      mapGQpGP:=hom<GQp->GP| a:-> &+{(&+{((a @@ mapQGQp)^Degree(factors[j])) @ mapsKGP[j][i] @ inc[j][i] : i in [1..N[j]]})@INC[j] : j in [1..nf]}>; 

      G,qt2:=quo<GP|[mapGQpGP(GQp.l): l in [1..#OrderedGenerators(GQp)]]>;
      

      mapKG1:=map<fields->GP | a:-> &+{ &+{a[j] @ mapsKGP[j][i] @ inc[j][i]@ INC[j] : i in [1..N[j]]}: j in [1..nf]}>;
      mapKG:=mapKG1*qt2;
      image:={G| };
   else
      mapKG:=map<fields->GP | a:-> &+{ &+{a[j] @ mapsKGP[j][i] @ inc[j][i]@ INC[j] : i in [1..N[j]]}: j in [1..nf]}>; 
      image:={GP| };
      qt2:=hom<GP->GP | a :-> a>;   
   end if;
   return mapKG,qt2,primes,th,N,g1,g2,mapsKGP,inc,INC,coefs,coef2,GP,O;
end function;

local_search:=function(S,q,p,f,K,globalimage,qt2,O,fields,primes,th,nf,N,g1,g2,mapsKGP,inc,INC,coefs,coef2,GP,poly)
   _,pi:=IsPrincipal(p);
 //  QNF:=NumberField(PolynomialRing(Rationals()).1-1: DoLinearExtension);
 //  F:=Polynomial(QNF,f);
 //  QQ:=BaseRing(Parent(F));
   OK:=Integers(K);
   image:={@Universe(globalimage)|@};
   R := PolynomialRing(K); x := R.1;
   ffactored:=f;
   lead :=LeadingCoefficient(poly);
   
   factors:=ffactored;
   RK:=[* Parent(elt) : elt in factors*];
   f:=R!poly;

   FF,toFF:=ResidueClassField(p);
   reps:=[elt@@  toFF : elt in FF];
   _,pi:=IsPrincipal(p);
   units,FFtounits:=UnitGroup(Codomain(toFF));
   unitsmodq,qt3:=quo<units|[q*units.i : i in [1..Ngens(units)]]>;

   local_im:=function(reps,toFF,K,q,list,list2,image,k,p,aff)
      if p in S then
	      if aff eq 1 then
	         for x in list do
               x0:=x;
               solubilitytest:=false;
               solubley:=[];
               for y0 in list2 do
		            if zp_soluble(reps,pi,units,FFtounits,qt3,unitsmodq,FF,toFF,S,K,q,coefs,[x0],[y0],p,k) then
                     Include(~solubley,y0);
                     solubilitytest:=true;
                  end if;
               end for;
               if solubilitytest then
	               test:=true;
	               klist := [[[(2*Valuation(q*O[j],P)+Valuation(fields[j]!Evaluate(factors[j],fields[j]!x0)*O[j],P)+1)/Valuation(pi*O[j],P),(2*Valuation(q*O[j],P)+Valuation(Evaluate(g1[j],fields[j]!x0)*O[j],P)+1)/Valuation(pi*O[j],P)] : P in primes[j]] : j in [1..nf]];

	               for j in [1..nf] do
	                  for i in [1..N[j]] do
                        _,minval :=Min(klist[j][i]);
		                  if Min(klist[j][i]) gt k then 
			                  test:=false;
		                  end if;
	                  end for;
	               end for;
                  if test then
	                  im:=GP!0;
	                  for j in [1..nf] do
	                     for i in [1..N[j]] do
		                     if klist[j][i][1] le klist[j][i][2] then
			                     im:=im+(fields[j]!Evaluate(factors[j],fields[j]!x0))@mapsKGP[j][i]@inc[j][i]@INC[j];
		                     else
			                     im:=im+(Evaluate(g1[j],fields[j]!x0)^-1)@ mapsKGP[j][i] @ inc[j][i]@INC[j];
     //                         printf "using cofactor for x=%o.\n",x0;
		                     end if;
	                     end for;
	                  end for;
                     if (Degree(f) mod q) eq 0 then
   //                     printf "the image of %o is %o and the precision is %o.\n" ,x0,im@qt2,k;
	                     Include(~image,im @ qt2);
                     else
                        Include(~image,im);
                     end if;
                  else

                     newlist:=[x0+(t)*pi^k: t in reps];
                     newlist2:=&cat[[y0+(t)*pi^k: t in reps] : y0 in solubley];
     //                printf "The size of the image is %o\n",#image;
	                  image:=$$(reps,toFF,K,q,newlist,newlist2,image,k+1,p,1);
                  end if;			
		         end if;
	         end for;
	      else
	         for x in list do
               x0:=x;
               solubilitytest:=false;
               solubley:=[];
               for y0 in list2 do
		            if zp_soluble(reps,pi,units,FFtounits,qt3,unitsmodq,FF,toFF,S,K,q,coef2,[x0],[y0],p,k) then
                     Include(~solubley,y0);
                     solubilitytest:=true;
                  end if;
               end for;
               if solubilitytest then 
                  if (Degree(f) mod q) eq 0 then
			            klist := [[[(2*Valuation(q*O[j],P)+Valuation((Evaluate(RK[j]!Reverse(Eltseq(factors[j])),fields[j]!x0))*O[j],P)+1)/Valuation(pi*O[j],P),(2*Valuation(q*O[j],P)+Valuation(Evaluate(g2[j],fields[j]!x0)*O[j],P)+1)/Valuation(pi*O[j],P)] : P in primes[j]]: j in [1..nf]];
                  else
			            klist := [[[(2*Valuation(q*O[j],P)+Valuation((Evaluate(RK[j]!Reverse(Eltseq(factors[j])),fields[j]!x0^q))*O[j],P)+1)/Valuation(pi*O[j],P),(2*Valuation(q*O[j],P)+Valuation(Evaluate(g2[j],fields[j]!x0)*O[j],P)+1)/Valuation(pi*O[j],P)] : P in primes[j]]: j in [1..nf]];
                  end if;
			         test:=true;

		            for j in [1..nf] do
		               for i in [1..N[j]] do
			               if Min(klist[j][i]) gt k then test:=false;
			               end if;
		               end for;
		            end for;

			         if test then
				         im:=GP!0;
				         for j in [1..nf] do
				            for i in [1..N[j]] do
					            if klist[j][i][1] le klist[j][i][2] then
                              if (Degree(f) mod q) eq 0 then
						               im:=im+(Evaluate(RK[j]!Reverse(Eltseq(factors[j])),fields[j]!x0))@ mapsKGP[j][i] @ inc[j][i]@INC[j];
                              else
                                 im:=im+(Evaluate(RK[j]!Reverse(Eltseq(factors[j])),fields[j]!x0^q))@ mapsKGP[j][i] @ inc[j][i]@INC[j];
                              end if;
					            else
						            im:=im+(Evaluate(g2[j],fields[j]!x0)^-1) @ mapsKGP[j][i] @ inc[j][i]@INC[j];
					            end if;
				            end for;
				         end for;
                     if (Degree(f) mod q) eq 0 then
       //                 printf "the z coordinate %o mapped to %o.\n",x0,im@qt2;
				            Include(~image,im @ qt2);
                     else
                        Include(~image,im);
                     end if;
			         else
				         newlist:=[x0+(t)*pi^k : t in reps];
                     newlist2:=&cat[[y0+(t)*pi^k : t in reps] : y0 in solubley];
				         image:=$$(reps,toFF,K,q,newlist,newlist2,image,k+1,p,2);
			         end if;	
		         end if;
	         end for;
	      end if;
      else
 	      if aff eq 1 then
	         for x in list do
               x0:=x@@toFF;
		         if zp_soluble(reps,pi,units,FFtounits,qt3,unitsmodq,FF,toFF,S,K,q,coefs,[x],list2,p,k) then 
                  im:=GP!0;
                  for j in [1..nf] do
                     for i in [1..N[j]] do
                        if Valuation(Evaluate(factors[j],fields[j]!x0),primes[j][i]) le Valuation(Evaluate(g1[j],fields[j]!(x0)),primes[j][i]) then
		                     im:=im+(Evaluate(factors[j],fields[j]!x0))@mapsKGP[j][i]@inc[j][i]@INC[j];
	                     else
		                     im:=im+(Evaluate(g1[j],fields[j]!(x0))^-1)@ mapsKGP[j][i] @ inc[j][i]@INC[j];
	                     end if;
                     end for;
                  end for;
                  if (Degree(f) mod q) eq 0 then
                     Include(~image,im @ qt2);
                  else
                     Include(~image,im);
                  end if;                 			
		         end if;
	         end for;
	      else
	         for x in list do
               x0:=x@@toFF;
		         if zp_soluble(reps,pi,units,FFtounits,qt3,unitsmodq,FF,toFF,S,K,q,coef2,[x],list2,p,k) then 
                  im:=GP!0;
                  for j in [1..nf] do
                     for i in [1..N[j]] do
                        if (Degree(f) mod q) eq 0 then
                           if Valuation(Evaluate(RK[j]!Reverse(Eltseq(factors[j])),fields[j]!x0),primes[j][i]) le Valuation(Evaluate(g2[j],fields[j]!(x0)),primes[j][i]) then
		                        im:=im+(Evaluate(RK[j]!Reverse(Eltseq(factors[j])),fields[j]!x0))@mapsKGP[j][i]@inc[j][i]@INC[j];
	                        else
		                        im:=im+(Evaluate(g2[j],fields[j]!(x0))^-1)@ mapsKGP[j][i] @ inc[j][i]@INC[j];
	                        end if;
                        else
                           if Valuation(Evaluate(RK[j]!Reverse(Eltseq(factors[j])),fields[j]!x0^q),primes[j][i]) le Valuation(Evaluate(g2[j],fields[j]!(x0)),primes[j][i]) then
		                        im:=im+(Evaluate(RK[j]!Reverse(Eltseq(factors[j])),fields[j]!x0^q))@mapsKGP[j][i]@inc[j][i]@INC[j];
	                        else
		                        im:=im+(Evaluate(g2[j],fields[j]!(x0))^-1)@ mapsKGP[j][i] @ inc[j][i]@INC[j];
	                        end if;
                        end if;
                     end for;
                  end for;
                  if (Degree(f) mod q) eq 0 then
                     Include(~image,im @ qt2);
                  else
                     Include(~image,im);
                  end if;                 	                  
		         end if;
	         end for;
	      end if;     
      end if;
		
	   return image;
   end function;

   _,localmap:=Completion(K,p); 
   if (Degree(f) mod q ) eq 0 then
      if IsPower(LeadingCoefficient(f)@localmap,q) then
         Include(~image,(GP!0)@qt2);
      end if;
   else
      im:=GP!0;
      for j in [1..nf] do
         for i in [1..N[j]] do
            im:=im+(fields[j]!LeadingCoefficient(f)^Index([Degree(f)*j mod q : j in [1..q-1]],q-1))@mapsKGP[j][i]@inc[j][i]@INC[j];
         end for;
      end for;
      Include(~image,im);
   end if;

   if p in S then
      for x0 in FF do

         image:=local_im(reps,toFF,K,q,[x0@@toFF],reps,image,1,p,1);
         if image eq globalimage then 
            return {@i : i in [1..#globalimage]@};
         end if;
      end for;
 //     print "NOW WORKING WITH THE INFINITE PATCH";
      for x0 in FF do
         image:=local_im(reps,toFF,K,q,[x0@@toFF],reps,image,1,p,2);
         if image eq globalimage then 
            return {@i : i in [1..#globalimage]@};
         end if;
      end for;
   else
      for x0 in FF do
         image:=local_im(reps,toFF,K,q,[x0],FF,image,1,p,1);
         if image eq globalimage then 
            return {@i : i in [1..#globalimage]@};
         end if;
      end for;
      for x0 in FF do
         image:=local_im(reps,toFF,K,q,[x0],FF,image,1,p,2);
         if image eq globalimage then 
            return {@i : i in [1..#globalimage]@};
         end if;
      end for;
   end if;
   vprintf CycCov, 2: "The global image is %o and the local image is %o.\n",globalimage,image;
   return {@Index(globalimage,elt) : elt in (image meet globalimage)@};
end function;


descent_1:=function(q,f,poly,KnownPoints,PrimeBound,PrimeCutoff);

	for c in Coefficients(poly) do
		error if not IsIntegral(c), "f must have integral coefficients.";
	end for;

	vprintf CycCov, 1: "Doing partial descent on the C: y^q = %o\n", poly;
	vprintf CycCov, 1: " with respect to the factorization %o\n", f; 

	// y^q = poly
	// poly = c * &* Norm(f_i) : f_i in f

   Rx := PolynomialRing(Rationals()); x := Rx.1;
   if BaseRing(Parent(poly)) eq Rationals() then
      K:=NumberField(x-1 : DoLinearExtension:=true);
   else
      K:=BaseRing(Parent(poly));
   end if;
	 
	 vprintf CycCov, 1: " over %o.\n", K;
   
	 RK:=PolynomialRing(K);
   
   lead:=K!LeadingCoefficient(poly);
   for i in [1..#f] do
      if BaseRing(Parent(f[i])) ne BaseRing(Parent(poly)) then
         K1:=NumberField(RK!DefiningPolynomial(BaseRing(Parent(f[i]))) : DoLinearExtension:=true);
         RK1:=PolynomialRing(K1);
         f[i]:=RK1![K1!Eltseq(elt) : elt in Eltseq(f[i])];
      else
         f[i]:=Polynomial(NumberField(RK!(x-1) : DoLinearExtension:=true),f[i]);
      end if;
   end for;
         
   factors:=f;
   nfactors:=#f;
   K:=AbsoluteField(Parent(lead));
	RK := PolynomialRing(K); x := RK.1;
   ffactored:=f;

   f:=RK!poly;


   fieldsrel:=<>;
	fields:=<>;

	for i in [1..nfactors] do
      Append(~fieldsrel,BaseRing(Parent(factors[i])));
		Append(~fields,AbsoluteField(fieldsrel[i]));
	end for;
   fields:=CartesianProduct(fields);
   fieldsrel:=CartesianProduct(fieldsrel);
	
	vprintf CycCov, 1: "The algebra over K is %o.\n", fieldsrel;
   polyrings:=<>;
	for i in [1..nfactors] do
		Append(~polyrings,PolynomialRing(fields[i]));
	end for;	


	rings:=<>;
	for i in [1..nfactors] do
		Append(~rings,Integers(fields[i]));
	end for;

   S:=<>;

	for i in [1..nfactors] do
	/*	if Degree(Norm(factors[i])) eq 1 then
			g:=Evaluate(lead*&*[factor[1] : factor in Exclude(Factorisation(f,polyrings[i]),<factors[i],1>)],-Eltseq(factors[i])[1]);
			Si:=Support(q*(fields[i]!g)*rings[i]);
			if IsEmpty(Si) then
				Si:={Universe(Support(2*rings[i]))|};
			end if;	

			Append(~S,Si);
		else */
			g:=polyrings[i]!(polyrings[i]!f/(polyrings[i]!factors[i]));
			g:=Resultant(g,factors[i]);
			Si:=Support(q*(fields[i]!g)*rings[i]);
			
			if IsEmpty(Si) then
				Si:={Universe(Support(2*rings[i]))|};
			end if;	

			Append(~S,Si);
//		end if;
	end for;

	OK:=Integers(K);
	delta:=K!(Discriminant(f));
   Sbad:=Support(q*delta*OK);
   primes:=Sbad;
   Sp:=Set(primes);
   if IsEmpty(Sp) then
	   Sp:={Universe(Support(2*OK))|};
   end if;
   Kselmergroup,KtoKselmergroup:=pSelmerGroup(q,Sp);

	groups:=[];
   powerseqmaps:=[**];
   maps:=<>;
   mapsi:=<>;
   selmerbasis:=[**];
   normgens:=[**];
   normmaps:=<>;

	for i in [1..nfactors] do
		a,b,powerseqmaps[i],selmerbasis[i]:=pSelmerGroup(q,S[i]: Raw:=true);
		c:=Inverse(b);
		Include(~groups,a);
		Append(~maps,b);
		Append(~mapsi,c);
      normgens[i]:=[Norm(PowerProduct([fieldsrel[i]!elt: elt in Eltseq(selmerbasis[i])],Eltseq(powerseqmaps[i](a.j)))) : j in [1..Ngens(a)]];
      Append(~normmaps,hom<a->Kselmergroup | [elt @ KtoKselmergroup : elt in normgens[i]]>);
	end for;

	AqS,inc,pr:=DirectSum(groups);
   norm:=hom<AqS->Kselmergroup | [&+[elt@pr[i]@normmaps[i] : i in [1..nfactors]] :elt in OrderedGenerators(AqS)]>;

   n:=Degree(f);
   if (n mod q) eq 0 then
	   for p in primes do
		   test:=true;
		   for i in [1..nfactors] do
			   for P in Factorisation(ideal<rings[i]|p>) do
				   if P[1] notin S[i] then
					   if (P[2] mod q) ne 0 then
						   test:=false;
					   end if;
				   end if;
			   end for;
		   end for;
		   if not test then 
			  Exclude(~primes,p);
		   end if;
	   end for;
	   

	   Sp:=Set(primes);
	   if IsEmpty(Sp) then
		   Sp:={Universe(Support(2*OK))|};
	   end if;	
	   QqT,map:=pSelmerGroup(q,Sp);
	   mapi:=Inverse(map);
	//   printf "the degrees of the factors are %o.\n",[Degree(factor) : factor in factors];
	   iota:=hom<QqT->AqS | a :-> &+[(fields[i]!(a @ mapi)^Degree(factors[i])) @ maps[i] @ inc[i] : i in [1..nfactors]]>;
   /*	GG:=sub<AqS | Image(iota)>;*/
	   AQ,qt1:=quo<AqS |[iota(QqT.i) : i in [1..#OrderedGenerators(QqT)]]  >;
	   Map:=pmap<fields->AQ | a:-> (&+[a[i]@maps[i]@inc[i]: i in [1..nfactors]])@qt1,b:-> <b@@qt1@pr[i]@mapsi[i] : i in [1..nfactors]>>;
//	   norm:=hom<AQ->K| a :-> &*[Norm((a@@Map)[i]) : i in [1..#F]]>;
   else
 	   Map:=pmap<fields->AqS | a:-> (&+[a[i]@maps[i]@inc[i]: i in [1..nfactors]]),b:-> <b@pr[i]@mapsi[i] : i in [1..nfactors]>>;
	//   norm:=hom<AqS->K| a :-> &*[Norm((a@@Map)[i]) : i in [1..#F]]>;    
   end if;


   if (n mod q) eq 0 then
      try
         c_0:=(K!lead)@KtoKselmergroup@@norm;
      catch e
				 vprintf CycCov, 1 : "The image is empty due to norm and class group cosniderations.\n";
         return {},Map;
      end try;
      image:={(-c_0+elt)@qt1 : elt in Kernel(norm)};
      repsforaq:=[elt@@Map : elt in OrderedGenerators(AQ)];
      G:=q^(n-2)*(n*(q-1)/2-q)+1;
      knownpointimages:={AQ|};
      vprintf CycCov, 1 : "The Weil bound for the primes is %o.\n", 4*G^2;
			if PrimeBound eq 0 then
				PrimeBound := 4*G^2;
			end if;
			
      usefulprimes:={@ elt  : elt in Sbad@};
			if PrimeCutoff ne 0 then
				usefulprimes diff:= {@ v : v in usefulprimes | Norm(v) gt PrimeCutoff @};
			end if;
			BadRationalPrimes := { Factorization(Norm(v))[1][1] : v in Sbad };
			usefulprimes join:= &join{@ {@ pideal[1] : pideal in Factorisation(p*OK)@} : p in PrimesUpTo(Floor(PrimeBound)) | not p in BadRationalPrimes @};

      for point in { P : P in KnownPoints | P[3] ne 0} do 
         if point[2] ne 0 then
            Include(~knownpointimages,<&+[Eltseq(factors[i])[j]*Numerator(point[1])^(j-1)*Denominator(point[1])^(#Eltseq(factors[i])-j):j in [1..#Eltseq(factors[i])]]: i in [1..nfactors]>@Map);
         else
            preimage:=[**];
            for i in [1..nfactors] do
               if Evaluate(factors[i],point[1]) eq 0 then
                  coefs:=Eltseq(lead*&*[factor[1] : factor in Exclude(Factorisation(polyrings[i]!f),<factors[i],1>)]);
                  preimage:= preimage cat [*(&+[coefs[j]*Numerator(point[1])^(j-1)*Denominator(point[1])^(#coefs-j) : j in [1..#coefs] ])^-1*];
               else
                  coefs:=Eltseq(factors[i]);
                  preimage:= preimage cat [*&+[coefs[j]*Numerator(point[1])^(j-1)*Denominator(point[1])^(#coefs-j):j in [1..#coefs]]*];
               end if;
            end for;

            Include(~knownpointimages,<elt : elt in preimage>@Map);
         end if;
      end for;
   else
      c_0:=<fields[i]!lead^Index([n*j mod q : j in [1..q-1]],q-1) : i in [1..nfactors]>@Map;
      image:={c_0 + elt : elt in Kernel(norm)};
      repsforaq:=[elt@@Map : elt in OrderedGenerators(AqS)];
      G:=q^(n-1)*((n-1)*(q-1)/2)+1;
      knownpointimages:={AqS|};
      vprintf CycCov, 1 : "The Weil bound for the primes is %o.\n", 4*G^2;
			if PrimeBound eq 0 then
				PrimeBound := 4*G^2;
			end if;
      
						
      usefulprimes:={@ elt  : elt in Sbad@};
			if PrimeCutoff ne 0 then
				usefulprimes diff:= {@ v : v in usefulprimes | Norm(v) gt PrimeCutoff @};
			end if;
			BadRationalPrimes := { Factorization(Norm(v))[1][1] : v in Sbad };
			usefulprimes join:= &join{@ {@ pideal[1] : pideal in Factorisation(p*OK)@} : p in PrimesUpTo(Floor(PrimeBound)) | not p in BadRationalPrimes @};


      for point in { P : P in KnownPoints | P[3] ne 0} do 
         if point[2] ne 0 then
            Include(~knownpointimages,<&+[Eltseq(factors[i])[j]*Numerator(point[1])^(j-1)*Denominator(point[1])^(q*(#Eltseq(factors[i])-j)):j in [1..#Eltseq(factors[i])]]: i in [1..nfactors]>@Map);
         else
            preimage:=[**];
            for i in [1..nfactors] do
               if Evaluate(factors[i],point[1]) eq 0 then
                  coefs:=Eltseq(lead*&*[factor[1] : factor in Exclude(Factorisation(polyrings[i]!f),<factors[i],1>)]);
                  preimage:= preimage cat [*(&+[coefs[j]*Numerator(point[1])^(j-1)*Denominator(point[1])^(q*(#coefs-j)) : j in [1..#coefs] ])^-1*];
               else
                  coefs:=Eltseq(factors[i]);
                  preimage:= preimage cat [*&+[coefs[j]*Numerator(point[1])^(j-1)*Denominator(point[1])^(q*(#coefs-j)):j in [1..#coefs]]*];
               end if;
            end for;

            Include(~knownpointimages,<elt : elt in preimage>@Map);
         end if;
      end for;      


   end if;


	 if exists{ P : P in KnownPoints | P[3] eq 0 } then
		 if ((n mod q) eq 0) and (IsPower(lead,q)) then
				Include(~knownpointimages,Identity(AQ));
		 else
				if (n mod q) ne 0 then
					 Include(~knownpointimages,c_0);
				end if;
		 end if;
	 end if;

		// check that the known points map to the correct subset of the algebra
   assert knownpointimages subset image;

	vprintf CycCov, 3: "The known rational points map to %o.\n",knownpointimages;

	counter:=1;

	while (image ne knownpointimages) and (counter le #usefulprimes) do
		vprintf CycCov, 3: "The image is contained in %o\nand contains %o.\n",image,knownpointimages;
		vprintf CycCov, 1: "Computing local image at %o.\n",usefulprimes[counter];
		mapKG,qt2,primes,th,N,g1,g2,mapsKGP,inc,INC,coefs,coef2,GP,O:=selmer_3(Map,K,q,usefulprimes[counter],ffactored,fields,[* fields[i]!fieldsrel[i].1 : i in [1..nfactors] *],rings,polyrings,nfactors,f);
		G:=Codomain(mapKG);
      if (n mod q) eq 0 then
         AQtoG:=hom<AQ->G|[elt@mapKG : elt in repsforaq]>;
         globalimage:={@a @ AQtoG : a in image@};
         newimagelocal:=local_search(Sbad,q,usefulprimes[counter],ffactored,K,globalimage,qt2,O,fields,primes,th,nfactors,N,g1,g2,mapsKGP,inc,INC,coefs,coef2,GP,f);
         image:={elt : elt in image | Index(globalimage,elt@AQtoG) in newimagelocal};
      else
         AqStoG:=hom<AqS->G|[elt@mapKG : elt in repsforaq]>;
         globalimage:={@a @ AqStoG : a in image@};
         newimagelocal:=local_search(Sbad,q,usefulprimes[counter],ffactored,K,globalimage,qt2,O,fields,primes,th,nfactors,N,g1,g2,mapsKGP,inc,INC,coefs,coef2,GP,f);

         image:={elt : elt in image | Index(globalimage,elt@AqStoG) in newimagelocal};
      end if;

		counter:=counter+1;
	end while;

	return {im @@ Map : im in image}, Map;

end function;

intrinsic qCoverPartialDescent(f :: RngUPolElt, factors :: List, q :: RngIntElt : KnownPoints := {}, PrimeBound := 0, PrimeCutoff := 0) -> Set, Map
{Performs a partial decent on the cyclic cover y^q = f(x) with respect to the map determined by factors.}

Sel,toalg := descent_1(q,factors,f,KnownPoints,PrimeBound,PrimeCutoff);

return Sel, toalg;

end intrinsic;




