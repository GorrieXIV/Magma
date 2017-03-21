freeze;
/******************************************************************

descent.m
Michael Mourao
November 2011


Intrinsics for performing a (full) descent on a cyclic cover of P^1
of the form y^q = f(x)

******************************************************************/

/**** Changes:

+ May2012 Michael
   added singular case over Q, for
   the case q|n

+ Nov2011 Brendan
	changed verbosity


	
***/




declare verbose CycCov, 3;

/*This function is used to compute elements in K^* /K^*q such that a^n=elt.*/

root_n:= function(elt,n)
   G:=Parent(elt);
   list:=[a : a in G | n*a eq elt];
   return list[1];
end function;

zp_soluble:= function(reps,pi,FF,toFF,badprimes,K,q,coef,X,Y,p,k)

   /*if (((Integers()!Norm(p)-1) mod q) ne 0) and (p notin badprimes) then
      return true;
   else*/
      if (p notin badprimes) then
         for x in X do
            x0:=x;
            fx0:=&+[coef[i]@toFF*x0^(i-1)  : i in [1..#coef]];
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
            for y in Y do
               y0:=K!y;
               n:=Valuation((y0^q-Evaluate(f,x0)),p);
               m:=Min([Valuation(Evaluate(g,x0),p),Valuation((q*y0^(q-1)),p)]);
               if (k gt 0) and (n gt 2*m) and (k le (n-m)) then
                  return true; 
               else
                  if (k gt 0) and (n ge 500) then
	                  return true;
                  else 
	                  if  (k eq 0) or ((n le 2*m) and (n ge 2*k)) then
			               if $$(reps,pi,FF,toFF,badprimes,K,q,coef,[x0+a1*pi^k : a1 in reps],[y0+b1*pi^k : b1 in reps],p,k+1) then 
                           return true;
			               end if;
	                  end if;
                  end if;
               end if;
            end for;
         end for;
	      return false;
      end if;
 //  end if;
					
end function;

selmer_3:=function(Map,K,q,p,f,fields,th,rings,polyrings,nf)

   bool,pi:=IsPrincipal(p);

   error if not bool, "Not implemented for the case of non-principal prime ideals";

   OK:=Integers(K);

   R := PolynomialRing(K); x := R.1;
   f:=R!f;
   n:=Degree(f);
   nn:=[elt[2] : elt in Factorisation(f)];//new
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
   if (n mod q) eq 0 then
      coef2:=[Coefficients(f)[#Coefficients(f)-i]: i in [0..#Coefficients(f)-1]];
   else
      coef2:=Eltseq(R!Evaluate(R!Reverse(Coefficients(f)),R.1^q));
   end if;
      
   f2:=R!coef2;
   for j in [1..nf] do

	   Fac:=Factorisation(RK[j]!f);
	   g1[j]:=RK[j]!(RK[j]!f/(RK[j].1-th[j])^nn[j]);//new
      if (n mod q) eq 0 then
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
   if (n mod q) eq 0 then
      localfield,localmap:=Completion(K,p);
      GQp,mapQGQp1:=pSelmerGroup(q,localfield);
      mapQGQp:=localmap*mapQGQp1;

      mapGQpGP:=hom<GQp->GP| a:-> &+{(&+{a @@ mapQGQp @ mapsKGP[j][i] @ inc[j][i] : i in [1..N[j]]})@INC[j] : j in [1..nf]}>; 

      G,qt2:=quo<GP|[mapGQpGP(GQp.l): l in [1..#OrderedGenerators(GQp)]]>;
      

      mapKG1:=map<fields->GP | a:-> &+{ &+{a[j] @ mapsKGP[j][i] @ inc[j][i]@ INC[j] : i in [1..N[j]]}: j in [1..nf]}>;
      mapKG:=mapKG1*qt2;
      image:={G| };
   else
      mapKG:=map<fields->GP | a:-> &+{ &+{a[j] @ mapsKGP[j][i] @ inc[j][i]@ INC[j] : i in [1..N[j]]}: j in [1..nf]}>; 
      image:={GP| };
      qt2:=hom<GP->GP |  OrderedGenerators(GP) >;   
   end if;

   return mapKG,qt2,primes,th,N,g1,g2,mapsKGP,inc,INC,coefs,coef2,GP,O,nn;
end function;

local_search:=function(knownpointlocalims,S,q,p,f,K,globalimage,qt2,O,fields,primes,th,nf,N,g1,g2,mapsKGP,inc,INC,coefs,coef2,GP,nn)

   image:={@Universe(globalimage)|@};
   FF,toFF:=ResidueClassField(p);

   reps:=[elt@@  toFF : elt in FF];
   _,pi:=IsPrincipal(p);


   local_im:=function(reps,toFF,K,q,list,list2,image,k,p,aff)
      if p in S then
	      if aff eq 1 then

	         for x in list do
               x0:=x;
               solubilitytest:=false;
               solubley:=[];
               for y0 in list2 do

		            if zp_soluble(reps,pi,FF,toFF,S,K,q,coefs,[x0],[y0],p,k) then
                     Include(~solubley,y0);
                     solubilitytest:=true;
                  end if;
               end for;
               if solubilitytest then
	               test:=true;
	               klist := [[[(2*Valuation(q*O[j],P)+Valuation((fields[j]!x0-th[j])*O[j],P)+1)/Valuation(pi*O[j],P),(2*Valuation(q*O[j],P)+Valuation(Evaluate(g1[j],fields[j]!x0)*O[j],P)+1)/Valuation(pi*O[j],P)] : P in primes[j]] : j in [1..nf]];

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
			                     im:=im+(fields[j]!x0-th[j])@mapsKGP[j][i]@inc[j][i]@INC[j];
		                     else
			                     im:=im+root_n((Evaluate(g1[j],fields[j]!x0)^-1)@ mapsKGP[j][i],nn[j]) @ inc[j][i]@INC[j]; //new
		                     end if;
	                     end for;
	                  end for;
                     if (Degree(f) mod q) eq 0 then
	                     Include(~image,im @ qt2);
                     else
                        Include(~image,im);
                     end if;
                  else

                     newlist:=[x0+(t)*pi^k: t in reps];
                     newlist2:=&cat[[y0+(t)*pi^k: t in reps] : y0 in solubley];
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
		            if zp_soluble(reps,pi,FF,toFF,S,K,q,coef2,[x0],[y0],p,k) then
                     Include(~solubley,y0);
                     solubilitytest:=true;
                  end if;
               end for;
               if solubilitytest then 
                  if (Degree(f) mod q) eq 0 then
			            klist := [[[(2*Valuation(q*O[j],P)+Valuation((1-th[j]*fields[j]!x0)*O[j],P)+1)/Valuation(pi*O[j],P),(2*Valuation(q*O[j],P)+Valuation(Evaluate(g2[j],fields[j]!x0)*O[j],P)+1)/Valuation(pi*O[j],P)] : P in primes[j]]: j in [1..nf]];
                  else
			            klist := [[[(2*Valuation(q*O[j],P)+Valuation((1-th[j]*fields[j]!x0^q)*O[j],P)+1)/Valuation(pi*O[j],P),(2*Valuation(q*O[j],P)+Valuation(Evaluate(g2[j],fields[j]!x0)*O[j],P)+1)/Valuation(pi*O[j],P)] : P in primes[j]]: j in [1..nf]];
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
						               im:=im+(1-th[j]*fields[j]!x0)@ mapsKGP[j][i] @ inc[j][i]@INC[j];
                              else
                                 im:=im+(1-th[j]*fields[j]!x0^q)@ mapsKGP[j][i] @ inc[j][i]@INC[j];
                              end if;
					            else
						            im:=im+root_n((Evaluate(g2[j],fields[j]!x0)^-1) @ mapsKGP[j][i],nn[j]) @ inc[j][i]@INC[j]; //new
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
		         if zp_soluble(reps,pi,FF,toFF,S,K,q,coefs,[x],list2,p,k) then 
                  im:=GP!0;
                  for j in [1..nf] do
                     for i in [1..N[j]] do
                        if Valuation(fields[j]!(x0)-th[j],primes[j][i]) le Valuation(Evaluate(g1[j],fields[j]!(x0)),primes[j][i]) then
		                     im:=im+(fields[j]!(x0)-th[j])@mapsKGP[j][i]@inc[j][i]@INC[j];
	                     else
		                     im:=im+root_n((Evaluate(g1[j],fields[j]!(x0))^-1)@ mapsKGP[j][i],nn[j]) @ inc[j][i]@INC[j]; //new
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
		         if zp_soluble(reps,pi,FF,toFF,S,K,q,coef2,[x],list2,p,k) then 
                  im:=GP!0;
                  for j in [1..nf] do
                     for i in [1..N[j]] do
                        if (Degree(f) mod q) eq 0 then
                           if Valuation(1-th[j]*fields[j]!(x0),primes[j][i]) le Valuation(Evaluate(g2[j],fields[j]!(x0)),primes[j][i]) then
		                        im:=im+(1-th[j]*fields[j]!(x0))@mapsKGP[j][i]@inc[j][i]@INC[j];
	                        else
		                        im:=im+root_n((Evaluate(g2[j],fields[j]!(x0))^-1)@ mapsKGP[j][i],nn[j]) @ inc[j][i]@INC[j]; //new
	                        end if;
                        else
                           if Valuation(1-th[j]*fields[j]!(x0^q),primes[j][i]) le Valuation(Evaluate(g2[j],fields[j]!(x0)),primes[j][i]) then
		                        im:=im+(1-th[j]*fields[j]!(x0^q))@mapsKGP[j][i]@inc[j][i]@INC[j];
	                        else
		                        im:=im+root_n((Evaluate(g2[j],fields[j]!(x0))^-1)@ mapsKGP[j][i],nn[j]) @ inc[j][i]@INC[j]; //new
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

/*Here we compute the size of the neighborhood around the singular points (over Q_p) 
that we know the descent map has constant image. Prime ideal P of of some number field 
component K_i is used to pinpoint which root over Q_p we are talking about, so this ideal 
satisfies RamificationIndex x Degree = 1, or equivalently K_P=Q_p. In the end this image 
is added to the existing set of images.*/ 

   SizeOfNbhd:=function(image,P,i)
      finish:=false;
      kh:=0;
      while not finish do
         kh+:=1;
         K_P,toK_P:=Completion(fields[i],P:Precision:=kh);
         X:=Integers()!Eltseq(toK_P(th[i]))[1];
         foundkh:=true;
         ValList:=[Rationals()|];
         if (2*Valuation(q*O[i],P)+Valuation(Evaluate(g1[i],X),P)+1 le kh) then
            ValList:=ValList cat [2*Valuation(q*O[i],P)+Valuation(Evaluate(g1[i],X),P)+1];
         else
            foundkh:=false;
         end if;
         for j in [1..nf] do
            for Pp in primes[j] do
               if (i ne j) or (P ne Pp) then
                  if  ((2*Valuation(q*O[j],Pp)+Valuation((fields[j]!X-th[j])*O[j],Pp)+1)/Valuation(pi*O[j],Pp) le kh) then
                     ValList:=ValList cat [(2*Valuation(q*O[j],Pp)+Valuation((fields[j]!X-th[j])*O[j],Pp)+1)/Valuation(pi*O[j],Pp)];
                  else
                     foundkh:=false;
                     break;
                  end if;
               end if;
            end for;
         end for;
         if foundkh then
            Include(~image,(&+[&+[Domain(qt2)|(fields[j]!X-th[j])@mapsKGP[j][l]@inc[j][l]@INC[j] : l in [1..#primes[j]]| (j ne i) or (primes[j][l] ne P)] : j in [1..nf]]+root_n((Evaluate(g1[i],fields[i]!X)^-1)@ mapsKGP[i][Index(primes[i],P)],nn[i]) @ inc[i][Index(primes[i],P)]@INC[i]) @ qt2 );
            finish:=true;
         end if;
      end while;
      return image,[*kh,X*];
   end function;

/*Here we call SizeOfNbhd function and we gather all information in a list UU*/

   UU:=[**];
   for j in [1..nf] do
      for P in primes[j] do
         if (((Degree(P)*RamificationIndex(P)) eq 1) and (nn[j] gt 1) ) then
            image,x0:=SizeOfNbhd(image,P,j);
            UU:=UU cat [*x0*];
         end if;
      end for;
   end for;

/*Here the list of representatives (or p-adic neighborhoods) is computed. 
The property is that startlist minus UU is safe to use Hensel's Lemma on. */

   ComputeInputList:=function(repss,k,list)
      for x in repss do
         recu:=false;
         for h in UU do
            if (h[1] gt k) and (Valuation(x-h[2],p) ge k) then
               recu:=true;
               list:=$$([x+t*pi^k : t in reps],k+1,list);
            end if;
         end for;
         if not recu then
            list:=list cat [*[*k,x*]*];
         end if;
      end for;
      return list;
   end function;

   startlist:=ComputeInputList(reps,1,[**]);
//   if Norm(p) eq 2 then printf "UU=%o and startlist=%o\n",UU,startlist;end if;
   if p in S then
      for x0 in startlist do
         remove:=false;
         for h in UU do
            if (x0[1] eq h[1]) and (Valuation(x0[2] - h[2],p) ge h[1]) then
 //              printf "removing %o at prime %o\n",x0,p;
               remove:=true;
            end if; 
         end for;
         if not remove then
            image:=local_im(reps,toFF,K,q,[x0[2]],reps,image,x0[1],p,1);
         end if;
         if image eq globalimage then 
            return {@i : i in [1..#globalimage]@};
         end if;
      end for;
 //     print "NOW WORKING WITH THE INFINITE PATCH";
      for x0 in FF do
         image:=local_im(reps,toFF,K,q,[(x0@@toFF)*pi],reps,image,2,p,2);
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
	 // check to make sure the known points map to things in the local image:
   assert knownpointlocalims subset image;
   vprintf CycCov, 3:  "#red_p(GlobalImage)= %o and #mu_p(C(k_p))= %o.\n",#globalimage,#image;
   return {@Index(globalimage,elt) : elt in (image meet globalimage)@};
end function;


descent_1:=function(q,f,KnownPoints,PrimeBound,PrimeCutoff);

	for c in Coefficients(f) do
		error if not IsIntegral(c), "f must have integral coefficients.";
	end for;

/*-K is the basefield, i.e. the field of definition of the polynomial f.-*/

   if BaseRing(Parent(f)) eq Rationals() then
      K:=NumberField(PolynomialRing(Rationals()).1-1: DoLinearExtension);
   else
      K:=AbsoluteField(BaseRing(Parent(f)));
   end if;
	 RK := PolynomialRing(K); x := RK.1;
	 f:=RK!f;
	 F:=Factorisation(f);
	 lead := LeadingCoefficient(f);
	 vprintf CycCov, 1: "Doing descent on the cyclic cover C: y^%o = %o over %o.\n",q,f,K;

/*-The "fields" tuple is used to store the absolute field components of the algebra while 
the "fieldsrel" tuple is used to store these as extensions relative to the basefield K.  -*/ 
   fields:=<>;
   fieldsrel:=<>;

   nn:=[elt[2] : elt in F];//new
	for i in [1..#F] do
		if Degree(F[i][1]) eq 1 then
         Append(~fieldsrel,NumberField(PolynomialRing(K).1+Eltseq(F[i][1])[1]: DoLinearExtension));
			Append(~fields,AbsoluteField(fieldsrel[i]));
		else
         Append(~fieldsrel,NumberField(F[i][1]));
			Append(~fields,AbsoluteField(fieldsrel[i]));
		end if;
	end for;

   fieldsrel:=CartesianProduct(fieldsrel);
   fields:=CartesianProduct(fields);
	
	vprintf CycCov, 3: "The etale algebra is %o.\n", fieldsrel;

/*-The polynomial rings are defined and mainly used to factorise f, 
one of it's irreducible factors, or the reverse polynomial of f.-*/

   polyrings:=<>;
	for i in [1..#F] do
		if Degree(F[i][1]) eq 1 then
			Append(~polyrings,Parent(Polynomial(fields[i],f)));
		else
			Append(~polyrings,PolynomialRing(fields[i]));
		end if;
	end for;

/*- The tuple "rings" contains the rings of integers of the number field components of the algebra. -*/

   rings:=<>;
	for i in [1..#F] do
		if Degree(F[i][1]) eq 1 then
			Append(~rings,Integers(BaseRing(polyrings[i])));
		else
			Append(~rings,Integers(fields[i]));
		end if;
	end for;

/*- "S" is a tuple containing sets of all the primes of a particular number field component 
such that the image of any rational point under the descent map in fields[i]^* /fields[i]^{*q} 
would be unramified at all primes outside S. These are evaluated in a slightly different way when 
the relative degree of fieldsrel[i] is 1. -*/

   S:=<>;
	for i in [1..#F] do
		if Degree(F[i][1]) eq 1 then
			g:=Evaluate(LeadingCoefficient(f)*&*[F[l][1]^F[l][2] : l in Exclude([1..#F],i)],-Eltseq(F[i][1])[1]);
			Si:=Support(q*(fields[i]!g)*rings[i]);
			if IsEmpty(Si) then
				Si:={Universe(Support(2*rings[i]))|};
			end if;	

			Append(~S,Si);
		else
			g:=polyrings[i]!(f/(polyrings[i].1-fieldsrel[i].1)^nn[i]);//new
			g:=Evaluate(g,fieldsrel[i].1);
			Si:=Support(lead*q*(fields[i]!g)*rings[i]);
			
			if IsEmpty(Si) then
				Si:={Universe(Support(2*rings[i]))|};
			end if;	

			Append(~S,Si);
		end if;
	end for;

   gg:=&*[F[i][1] : i in [1..#F]];//new
   deg:=Degree(gg);
   OK:=Integers(K);
   delta:=K!(lead*Discriminant(gg));//new
   Sbad:=Support(q*delta*OK);
   primes:=Sbad;
   Sp:=Set(primes);
   if IsEmpty(Sp) then
	   Sp:={Universe(Support(2*OK))|};
   end if;

/*- "Kselmergroup" is the selmer group K(2,Support(q*delta*OK)) and will be 
used as the codomain of the norm homomorphism defined later. -*/ 
   Kselmergroup,KtoKselmergroup:=pSelmerGroup(q,Sp);


/*- The selmer group of each component of the algebra is computed and then 
they are all added together via the DirectSum command. At the same time the 
norm homomorphism from each of the summands to the Kselmergroup defined above is also stored. -*/
   vprintf CycCov, 2: "The set of bad primes S is equal to %o.\n",S;
	 groups:=[];
   powerseqmaps:=[**];
   maps:=<>;
   mapsi:=<>;
   selmerbasis:=[**];
   normgens:=[**];
   normmaps:=<>;

  vprintf CycCov, 1: "Computing q-Selmer group of the algebra.\n";
	for i in [1..#F] do
		a,b,powerseqmaps[i],selmerbasis[i]:=pSelmerGroup(q,S[i]: Raw:=true);
		c:=Inverse(b);
		Include(~groups,a);
		Append(~maps,b);
		Append(~mapsi,c);
      normgens[i]:=[Norm(PowerProduct([fieldsrel[i]!elt: elt in Eltseq(selmerbasis[i])],Eltseq(powerseqmaps[i](a.j)))) : j in [1..Ngens(a)]];
      Append(~normmaps,hom<a->Kselmergroup | [elt @ KtoKselmergroup : elt in normgens[i]]>);
	end for;

/*- "AqS" stands for the unramified outside S part of A^* /A^{*q}. -*/ 

	AqS,inc,pr:=DirectSum(groups);

   norm:=hom<AqS->Kselmergroup | [&+[nn[i]*(elt@pr[i]@normmaps[i]) : i in [1..#F]] :elt in OrderedGenerators(AqS)]>;//new


   n:=Degree(f);


   if (n mod q) eq 0 then
		 //we need to mod out by K^*
		 /*- Here the set of K-primes T="primes" is computed. -*/
	   for p in primes do
		   test:=true;
		   for i in [1..#F] do
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
	   
		 vprintf CycCov, 2: "The set of bad primes T is equal to %o.\n",primes;

	   Sp:=Set(primes);
	   if IsEmpty(Sp) then
		   Sp:={Universe(Support(2*OK))|};
	   end if;	
	   QqT,map:=pSelmerGroup(q,Sp);
	   mapi:=Inverse(map);
	   iota:=hom<QqT->AqS |  [ &+[(fields[i]!(a @ mapi)) @ maps[i] @ inc[i] : i in [1..#F]] : a in OrderedGenerators(QqT) ]>;

	   AQ,qt1:=quo<AqS |[iota(QqT.i) : i in [1..#OrderedGenerators(QqT)]]  >;
	   Map:=pmap<fields->AQ | a:-> (&+[a[i]@maps[i]@inc[i]: i in [1..#F]])@qt1,b:-> <b@@qt1@pr[i]@mapsi[i] : i in [1..#F]>>;

   else
 	   
		 Map:=pmap<fields->AqS | a:-> (&+[a[i]@maps[i]@inc[i]: i in [1..#F]]),b:-> <b@pr[i]@mapsi[i] : i in [1..#F]>>;
   
	 end if; // (n mod q) eq 0

   if (n mod q) eq 0 then
      try
         c_0 := (K!lead)@KtoKselmergroup@@norm;
      catch e
				 vprintf CycCov,1: "The image is empty due to norm + class group considerations.\n";
         return {},Map,"";
      end try;
      image:={(-c_0 +elt)@qt1 : elt in Kernel(norm)};
      repsforaq:=[elt@@Map : elt in OrderedGenerators(AQ)];
			G:=q^(deg-2)*(deg*(q-1)/2-q)+1;
      knownpointimages:={AQ|};
      vprintf CycCov, 2: "Weil bound for for the primes is %o.\n", 4*G^2;
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
         if point[2] ne 0 and point[3] ne 0 then 
            Include(~knownpointimages,<Denominator(point[1])*(point[1]-fieldsrel[i].1): i in [1..#F]>@Map);
         else 
            preimage:=[**];
            for i in [1..#F] do
               if (fieldsrel[i]!point[1]) eq fieldsrel[i].1 then
                  coefs:=Eltseq(polyrings[i]!(f/(polyrings[i].1-fieldsrel[i].1)^nn[i]));//new
                  preimage:= preimage cat [*(&+[coefs[j]*Numerator(point[1])^(j-1)*Denominator(point[1])^(#coefs-j) : j in [1..#coefs] ])^-1*];
               else
                  preimage:= preimage cat [*Denominator(point[1])*(point[1]-fieldsrel[i].1)*];
               end if;
            end for;

            Include(~knownpointimages,<elt : elt in preimage>@Map);
         end if;
      end for;

   else
      c_0:=<fields[i]!lead^Index([n*j mod q : j in [1..q-1]],q-1) : i in [1..#F]>@Map;
			//printf "c_0=%o\n",c_0;
      image:={c_0 +elt : elt in Kernel(norm)};
			// better to represent this as a coset...?
			
      repsforaq:=[elt@@Map : elt in OrderedGenerators(AqS)];
			G:=q^(n-1)*((n-1)*(q-1)/2)+1;
      knownpointimages:={AqS|};
      vprintf CycCov, 2: "Weil bound for primes is %o.\n", 4*G^2;
			if PrimeBound eq 0 then
				PrimeBound := 4*G^2;
			end if;
			
      usefulprimes:={@ elt  : elt in Sbad@};
			if PrimeCutoff ne 0 then
				usefulprimes diff:= {@ v : v in usefulprimes | Norm(v) gt PrimeCutoff @};
			end if;
			BadRationalPrimes := { Factorization(Norm(v))[1][1] : v in Sbad };
			usefulprimes join:= &join{@ {@ pideal[1] : pideal in Factorisation(p*OK)@} : p in PrimesUpTo(Floor(PrimeBound)) | not p in BadRationalPrimes @};


			for point in { P : P in KnownPoints | P[3] ne 0 } do 
         if point[2] ne 0 then 
            Include(~knownpointimages,<(Numerator(point[1])-Denominator(point[1])^q*fieldsrel[i].1): i in [1..#F]>@Map);
         else
            preimage:=[**];
            for i in [1..#F] do
               if (fieldsrel[i]!point[1]) eq fieldsrel[i].1 then
                  coefs:=Eltseq(polyrings[i]!(f/(polyrings[i].1-fieldsrel[i].1)));
                  preimage:= preimage cat [*(&+[coefs[j]*Numerator(point[1])^(j-1)*Denominator(point[1])^(q*(#coefs-j)) : j in [1..#coefs] ])^-1*];
               else
                  preimage:= preimage cat [*(Numerator(point[1])-Denominator(point[1])^q*fieldsrel[i].1)*];
               end if;
            end for;

            Include(~knownpointimages,<elt : elt in preimage>@Map);
         end if;
      end for;


   end if;
	
	 if exists{ P : P in KnownPoints | P[3] eq 0 } then
		 if ((n mod q) eq 0) and IsPower(lead,q) then
				Include(~knownpointimages,Identity(AQ));
		 else
				if (n mod q) ne 0 then
					 Include(~knownpointimages,c_0);
				end if;
		 end if;
	 end if;
	 //are the known point images are a subset of AqS?:
   
	 assert knownpointimages subset image;

   vprintf CycCov, 2: "Images of known rational points: %o.\n",knownpointimages;

	 vprintf CycCov, 2: "Size of potential Selmer set before local compuations: %o.\n", #image;
	counter:=1;

	while (image ne knownpointimages) and (counter le #usefulprimes) do
		vprintf CycCov, 3: "The image is contained in %o\nand contains %o.\n",image,knownpointimages;
		vprintf CycCov, 1: "Now testing prime %o.\n",usefulprimes[counter];
		mapKG,qt2,primes,th,N,g1,g2,mapsKGP,inc,INC,coefs,coef2,GP,O:=selmer_3(Map,K,q,usefulprimes[counter],f,fields,[* fields[i]!fieldsrel[i].1 : i in [1..#F] *],rings,polyrings,#F);
		G:=Codomain(mapKG);
      if (n mod q) eq 0 then
         AQtoG:=hom<AQ->G|[elt@mapKG : elt in repsforaq]>;
         globalimage:={@a @ AQtoG : a in image@};
         knownpointlocalims:={@a @ AQtoG : a in knownpointimages@};
         newimagelocal:=local_search(knownpointlocalims,Sbad,q,usefulprimes[counter],f,K,globalimage,qt2,O,fields,primes,th,#F,N,g1,g2,mapsKGP,inc,INC,coefs,coef2,GP,nn);
         image:={elt : elt in image | Index(globalimage,elt@AQtoG) in newimagelocal};
      else
         AqStoG:=hom<AqS->G|[elt@mapKG : elt in repsforaq]>;
         globalimage:={@a @ AqStoG : a in image@};
         knownpointlocalims:={@a @ AqStoG : a in knownpointimages@};
         newimagelocal:=local_search(knownpointlocalims,Sbad,q,usefulprimes[counter],f,K,globalimage,qt2,O,fields,primes,th,#F,N,g1,g2,mapsKGP,inc,INC,coefs,coef2,GP,nn);
         image:={elt : elt in image | Index(globalimage,elt@AqStoG) in newimagelocal};
      end if;
		counter:=counter+1;
	end while;

	return {im @@ Map : im in image},Map;

end function;


intrinsic qCoverDescent(f :: RngUPolElt, q :: RngIntElt : KnownPoints := {}, PrimeBound := 0, PrimeCutoff := 0) -> Set, Map
{Performs a q-cover decent on the cyclic cover y^q = f(x).}

Sel,toalg := descent_1(q,f,KnownPoints,PrimeBound,PrimeCutoff);
return Sel,toalg;

end intrinsic;

 
