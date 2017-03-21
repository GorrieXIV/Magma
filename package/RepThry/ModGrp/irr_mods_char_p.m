freeze;

// import "cond.m" : PermCond, TensorCond; 

   import "min_field.m" : WriteOverSmallerField;

forward Absolutise, AddModules, AddModulesSub, pCharacter, GenerateModules;
forward HasNewExteriorConstituent, HasNewSymmetricConstituent; 
forward HasNewTensorConstituent, HasNewPermutationConstituent; 
forward IsKnown, IsTFGroup, MarkMaxDone, MarkPrdDone, MarkSqrDone, pRegularClasses;
forward NextProduct, NextModule, NonIsomorphicModules;
forward TFModules, SQModules;
forward InitBrauerCharacterInfo, BrauerChtr, ModulesSortCmp;
forward AddModuleConjugates;
forward ComplexChtrToBC, BCToComplexChtr;


/////////////////////////////////////////////////////////////////////////////

Z := IntegerRing();
Q := RationalField();
MB := func<| GetMaximumMemoryUsage()/2^20.0>;

AddAttribute(Grp, "pMod");
AddAttribute(Grp, "Lixsubs");


/////////////////////////////////////////////////////////////////////////////

intrinsic AbsolutelyIrreducibleModulesBurnside(G::Grp, K::FldFin : 
                  Mods := [], ModLim := -1, DimLim := 500000, 
                  LixStep := -1, LixBnd := -1, LixLim := 50000) -> []
{Given a permutation group G and a finite field K, construct the absolutely 
irreducible K[G]-modules for G by splitting modules. The function returns
a sequence containing the irreducible modules and also a parallel sequence
containing the corresponding Brauer characters} 

   requirege DimLim, 1;

      // Deal with trivial case
      pClasses := pRegularClasses(G, Characteristic(K));
      if #pClasses eq 1 then
          return [TrivialModule(G, K)], 
                 [CharacterRing(G)|[1] cat [0:i in [1..#Classes(G)-1]]];
      end if;

      LixBnd  := (LixBnd eq -1) select DimLim else LixBnd;
      LixStep  := (LixStep eq -1) select LixBnd div 2 else LixStep;
      Irrs := GenerateModules(G, K, Mods, ModLim, DimLim, LixStep, LixBnd, LixLim);

      // "*** After GenerateModules:", Cputime();
      // Irrs := AbsoluteModulesOverMinimalField(Irrs, K);
      // "*** After AbsoluteModulesOverMinimalField:", Cputime();

      Sort(~Irrs, ModulesSortCmp, ~perm);
      perm := Eltseq(perm);
      if Type(G) eq GrpMat then
	  chars := [BrauerCharacter(m): m in Irrs];
      else
	  chars := [ BCToComplexChtr(G, (G`pMod`Table)[perm[i]]) :
	      i in [1..#Irrs] ];
      end if;

   return Irrs, chars;

end intrinsic;


/////////////////////////////////////////////////////////////////////////////

intrinsic IrreducibleModulesBurnside(G::Grp, K::FldFin :
                  Mods := [], ModLim := -1, DimLim := 500000, 
                  LixStep := -1, LixBnd := -1, LixLim := 500000) -> []
{Given a permutation group G and a finite field K, construct the irreducible 
K[G]-modules for G by splitting modules} 

   // vprint IrrMods, 3: G:Magma;
   requirege DimLim, 1;

   require Type(G) in { GrpPerm, GrpMat }: 
       "This intrinsic only applies to a permutation or matrix group.";

      // Deal with trivial case
      pClasses := pRegularClasses(G, Characteristic(K));
      if #pClasses eq 1 then
         M := TrivialModule(G, K);
         return [ M ], [ M ], [ [ 1 ] ];
      end if;

      LixBnd  := (LixBnd eq -1) select DimLim else LixBnd;
      LixStep  := (LixStep eq -1) select LixBnd div 2 else LixStep;
      AbsIrrs := GenerateModules(G, K, Mods, ModLim, DimLim, LixStep, LixBnd, LixLim);
      Sort(~AbsIrrs, ModulesSortCmp, ~perm);
      vprint IrrMods: "Absolutely irreducible modules", AbsIrrs;

      ModuleIndex := function(Mods, T)
        K := Field(T);
        for i := 1 to #Mods do
            M := Mods[i];
            if #K eq #Field(M) and IsIsomorphic(M, T) then
                return i;
            end if;
        end for;
        return 0;
      end function;


      Irrs := [];
      Cons := [];
      for i := 1 to #AbsIrrs do
         M := AbsIrrs[i];
         N := AbsoluteModuleOverMinimalField(M, K);
         if #Field(N) ne #K then
             T := WriteOverSmallerField(N, K);
             n := ModuleIndex(Irrs, T);
             if n eq 0 then
                 Append(~Irrs, T);
                 Append(~Cons, [i]);
             else
                 cons := Cons[n];
                 Append(~cons, i);
                 Cons[n] := cons;
             end if;
         else
             Append(~Irrs, N);
             Append(~Cons, [i]);
         end if;
      end for;

      Sort(~Irrs, ModulesSortCmp, ~pi);
      vprint IrrMods: "Irreducible modules over given field", Irrs;
      perm := Eltseq(pi);
      Cons := [ Cons[perm[i]] : i in [1..#Cons]];
 
   return Irrs, AbsIrrs, Cons;

end intrinsic;

/////////////////////////////////////////////////////////////////////////////

procedure InitialiseModules(G, K, DimLim, LixStep, LixBnd, LixLim)

   lixstep := LixStep;
   lixbnd := LixBnd;
   lixlim := LixLim;

   // Determine the p-regular classes

   Z := Integers();
   p := Characteristic(K);
   Cls := Classes(G);
   pClasses := pRegularClasses(G, p);
   vprintf IrrMods, 1: "\n +++ Irreducible modules of group of order %o over GF(%o). +++ \n", #G, p;
   // vprint IrrMods, 3: "The p-classes are:-";
   // vprint IrrMods, 3: PcLASSES;
   NumIrrs := #pClasses;

   // Contruct the squares map sigma for character calculations
   phi := ClassMap(G);
   sigma := map< {1..NumIrrs} -> {1..NumIrrs} | 
                 k :-> Position(pClasses, phi(Cls[pClasses[k]][3]^2))  >; 

   // X := CharacterTable(G);
   // maxdeg := Z!Degree(X[#X]);
   // vprint IrrMods: "maxdeg =", maxdeg;

   V := VectorSpace(K, NumIrrs);
   prdflgs := Matrix( Z, NumIrrs, NumIrrs, [ 0 : i in [1..NumIrrs^2] ]);
   vprint IrrMods: "\nThere are", NumIrrs, "p-modular irreducibles.\n";

   // Initialise low index subgroups
   lixsubflg := (lixstep ne 0) and (Type(G) ne GrpMat) and (IsTFGroup(G));
   if true then
   // if lixsubflg then
      // lixsubs := LowIndexSubgroups(G, lixstep);
    Comp := func< A, B | #A - #B >;
    lixsubs := Sort( [ R`subgroup : R in Subgroups(G : IndexLimit :=1000000) ], Comp );
      lixind := lixstep;
   else
      lixsubs := [ G ];
      lixind := 1;
   end if;
   if #lixsubs gt LixLim then
       lixsubs := lixsubs[1..lixlim];
   end if;
   G`Lixsubs := lixsubs;
   lixflgs := [ Z | 0 : i in [1..lixlim] ];
   vprintf IrrMods, 3: "Found %o subgroups having index bounded by %o:-\n", #lixsubs, 1000000; 
    // [ Index(G, lixsubs[i]) : i in [1..#lixsubs] ];

   /* Lix by-pass code */
/*
   lixsubs := [ G ];
   lixlim := 1;
   G`Lixsubs := lixsubs;
   lixflgs := [ Z | 0 : i in [1..LixLim] ];
*/

  /* 
   *  If no constituent of Irr[i] is processed sqrflgs := 0
   *  If SymmetricSquare of Irr[i] is processed sqrflgs := 1
 */
   sqrflgs  := [ Z | 0 : i in [1..NumIrrs] ];

   MXF := recformat< pCls, NumCls, Sqrs, BaseField, Table, TableEchelon,
	    p, PrdFlags, LixSubFlg, LixInd, LixStep, LixBnd, LixLim, LixFlags, SqrFlags, 
            BrauerField, BrauerInfo, FrobClassAction, DualClassAction >; 
   BCF := recformat< pCls, lift_polys, lift_vals, lift_where, field, zeta, primitive, lift_ords, lift_mats, int_classes >;
   G`pMod := rec< MXF |
                      pCls 		:= pClasses,
                      NumCls 		:= NumIrrs,
                      Sqrs		:= sigma,
                      BaseField    	:= K,
		      Table		:= [ ],
		      p 		:= p,
                      PrdFlags		:= prdflgs,
                      LixSubFlg         := lixsubflg,
                      LixInd            := lixind,
                      LixStep           := lixstep,
                      LixBnd            := lixbnd,
                      LixLim            := lixlim,
                      LixFlags          := lixflgs,
                      SqrFlags          := sqrflgs,
		      BrauerInfo        := rec<BCF|pCls := pClasses>
                    >;
   InitBrauerCharacterInfo(~G, p, Max([DimLim, LixLim, LixBnd]));
   G`pMod`BrauerField := G`pMod`BrauerInfo`field;
   sigma := map< {1..NumIrrs} -> {1..NumIrrs} | 
                 k :-> Position(pClasses, phi(Cls[pClasses[k]][3]^2))  >; 
   G`pMod`FrobClassAction := [Position(pClasses, phi(Cls[pClasses[k]][3]^p)):
	    k in [1..NumIrrs]];
   G`pMod`DualClassAction := [Position(pClasses, phi(Cls[pClasses[k]][3]^-1)):
	    k in [1..NumIrrs]];

end procedure;

/////////////////////////////////////////////////////////////////////////////

function IsTFGroup(G)

   return IsTrivial(Radical(G));

end function;

/////////////////////////////////////////////////////////////////////////////

function SQModules (G, K)

   if IsPerfect(G) then return []; end if;

   SQ, phi := SolubleQuotient(G);
   SQReps := AbsolutelyIrreducibleRepresentationsSchur(SQ, K);
   return [ GModule(G, [ G.i @ phi @ SQReps[j] : i in [1..Ngens(G)]]: Check := false ) 
                                                 : j in [1..#SQReps] ];

end function;

/////////////////////////////////////////////////////////////////////////////

function TFModules(G, K)

   if IsSoluble(G) or #Radical(G) lt 8 then return []; end if;

   RQ, phi := RadicalQuotient(G);
   RRQ, tau := DegreeReduction(RQ);
   RQReps := [ Representation (M) : M in AbsolutelyIrreducibleModulesBurnside(RRQ, K) ];
   return [
       GModule(G, [ G.i @ phi @ tau @ RQReps[j] : i in [1..Ngens(G)]]: Check := false
       ) : j in [1..#RQReps]
   ];

end function;

/////////////////////////////////////////////////////////////////////////////

GenerateModules := function(G1, K1, Mods, ModLim, DimLim, LixStep, LixBnd, LixLim)
/*
Given a permutation group G, construct the irreducible modules for G 
by forming tensor products and consequent irreducibles provided that 
the degree of a tensor product does not exceed DimLim
*/

   G := G1;
   K := K1;
   TIME := Cputime();

   // If G is a matrix group try to find a faithful perm representation

   if Type(G) eq GrpMat then
      if #G le 10^9 then
          zeit := Cputime();
          M := G1;
          gbp := GoodBasePoints(M);
          i := 1;
          repeat
             I := OrbitImage(M, gbp[i]);
             RandomSchreier(I);
             i +:= 1;
          until #I eq #M;
          G := DegreeReduction(I);
          printf "Time to find permutation representation is %o seconds.\n", Cputime(zeit);
          vprint IrrMods, 3: "The following permutation representation was constructed:-";
          G:Minimal; printf "\n";
       elif Characteristic(BaseRing(G)) ne Characteristic(K) then 
          error "Unable to compute the irreducibles for this matrix group.";
       end if;
    end if;
   
   InitialiseModules(G, K, DimLim, LixStep, LixBnd, LixLim);

   NumIrrs := G`pMod`NumCls;

   IrrLim := NumIrrs;
   if ModLim gt 0 then
     IrrLim := Minimum([NumIrrs, ModLim]);
   end if;
   // printf "IrrLim = %o.\n", IrrLim;
   
   Duals := [0 : i in [1..NumIrrs]];
   Duals[1] := 1;
   Frobs := [0 : i in [1..NumIrrs]];
   Frobs[1] := 1;
   M := TrivialModule(G, PrimeField(K));
   X := [G`pMod`BrauerField|1:i in [1..NumIrrs]];
   Irrs:=[M];
   G`pMod`Table := [X];
   G`pMod`TableEchelon := Matrix([X]);
   char2 := G`pMod`p eq 2;

   /*
   SQMods := SQModules(G, K);
   for i := 1 to #SQMods  do
      M := SQMods[i];
      assert IsIrreducible(M);
      assert IsAbsolutelyIrreducible(M);
      X := BrauerChtr(G, M);
      AddModulesSub(G, K, [<M, 1>], X, ~Irrs, ~Duals, ~Frobs);
   end for;
   vprint IrrMods: "At end of SQMods we have:-", Irrs;
   */
      
   /* 
   TFMods := TFModules(G, K);
   for i := 1 to #TFMods do
      M := TFMods[i];
      assert IsIrreducible(M);
      assert IsAbsolutelyIrreducible(M);
      X := BrauerChtr(G, M);
      AddModulesSub(G, K, [<M, 1>], X, ~Irrs, ~Duals, ~Frobs);
   end for;
   vprint IrrMods: "At end of TFMods we have:-", Irrs;
   */

      
   /* Create the natural module */

   // G is a permutation group

   if Type(G) eq GrpPerm then
	if Degree(G) le 500000 then
	// if Degree(G) le DimLim then
	   BF := G`pMod`BrauerField;
	   pCl := G`pMod`pCls;
	   Cls := Classes(G);
	   X := [BF|#Fix(Cls[pCl[i]][3]) : i in [1..#pCl] ];
	   vprint IrrMods: "Starting splitting of the given perm module:";
           zeit := Cputime();
           if Degree(G) lt 1000 then
           // if Degree(G) lt 500 or not IsTransitive(G) then
	      M := PermutationModule(G, K);
              Q := ConstituentsWithMultiplicities(M);
           else
              // H := Stabilizer(G, 1);
              Q := PermCond(G, 0, K);
           end if;
           vprint IrrMods, 3: "Splits into", [<Dimension(t[1]),t[2]>:t in Q];
           vprint IrrMods, 3: "Splitting takes", Cputime(zeit), "seconds";
	   AddModulesSub(G, K, Q, X, ~Irrs, ~Duals, ~Frobs);
	   vprint IrrMods: "Given modules yield", #Irrs, "irreducibles";
	end if;
   end if;

   // G is a matrix group

   if Type(G) eq GrpMat then

     // If G is a matrix group having the same characteristic as K we can proceed.

	   if Characteristic(BaseRing(G)) eq Characteristic(K) 
		and Degree(G) le DimLim 
	   then
	       M := GModule(G);
	       X := BrauerChtr(G, M);
	       vprint IrrMods: "Splitting initial module";
               Q := ConstituentsWithMultiplicities(M);
               vprint IrrMods, 3: "Splits into", [<Dimension(t[1]),t[2]>:t in Q];
	       AddModulesSub(G, K, Q, X, ~Irrs, ~Duals, ~Frobs);
	       vprint IrrMods: "Initial modules give", #Irrs, "irreducibles";
	   end if;

   end if; 

   vprint IrrMods: "Adding known modules";
   OldIrrs := #Irrs;
   for i := 1 to #Mods do
       M := Mods[i];
       H := Group(M);
       if H ne G then 
	error "Group of module is not equal to G";
	end if;
	if Ngens(G) eq Ngens(H) and 
	    forall{i:i in [1..Ngens(G)]|G.i eq H.i} then
	    M := GModule(G, ActionGenerators(M): Check := false);
	else
	    rho := Representation(M);
	    ag := [(G.i)@rho:i in [1..Ngens(G)]];
	    M := GModule(G, ag: Check := false);
	end if;

       X := BrauerChtr(G, M);
       if IsConsistent(G`pMod`TableEchelon, Matrix([X])) then 
	continue i;
       end if;
       Q := ConstituentsWithMultiplicities(M);
       AddModulesSub(G, K, Q, X, ~Irrs, ~Duals, ~Frobs);
       delete Q;
   end for;
   vprint IrrMods: "Initial modules give", #Irrs - OldIrrs, "irreducibles";

   vprint IrrMods, 1: "Now have", #Irrs, "of", NumIrrs, "modules";
   vprint IrrMods, 1: "Current elapsed time:", Cputime(TIME);
   vprint IrrMods, 2: Irrs;
   done := true;
   while  #Irrs lt IrrLim do
       
      new, Next := NextProduct(G, Irrs, Duals, DimLim);
      vprint IrrMods, 3: new, Next; /* debug */
      if not new then
         done := false;
         break;
      end if;

      t := Next[1];
      i := Next[2];
      j := Next[3];

      // print t, i, j;
      // print G`pMod`PrdFlags;
      // print G`pMod`SqrFlags;

      case t:
        when 1:

          // Tensor product

          d_i := Dimension(Irrs[i]);
          d_j := Dimension(Irrs[j]);
          dimprd := d_i*d_j;
          halfdp := (dimprd div 2) + 1;
	  flag, X := HasNewTensorConstituent(G, Irrs, i, j);
          if flag then
             vprint IrrMods:  
                "Product of", i, "of dim", d_i, "with",  j, "of dim", d_j, 
                   "giving dim", dimprd;
             Q := [];
             Irri, Irrj := ModulesOverCommonField(Irrs[i], Irrs[j]);
             if dimprd gt 1000 then
             // if dimprd gt 1000 and (d_i le halfdp) and (d_j le halfdp) then
                Q := TensorCond(Irri, Irrj);
                vprint IrrMods, 2: "Modules produced by TensorCond:-", Q;

             elif dimprd le 1000 then
                Q := ConstituentsWithMultiplicities(TensorProduct(Irri, Irrj));
                vprint IrrMods, 2:"Modules produced by TensorProduct:-", Q;

             end if;
	     if not IsEmpty(Q) then
		 dimfnd := &+[Dimension(t[1])*t[2]:t in Q];
		 assert dimfnd le dimprd;
	     end if;
	      AddModules(G, K, Q, X, Next, ~Irrs, ~Duals, ~Frobs, NumIrrs, TIME);
	      vprint IrrMods, 2:Irrs;
          end if;

          // Set flags showing processed
          MarkPrdDone(G, i, j, ~Duals, ~Frobs);

       when 2:

          // Exterior square

          d_i := Dimension(Irrs[i]);
          if d_i ne 1 then 
             dimprd := d_i*(d_i-1) div 2;
	     flag, X := HasNewExteriorConstituent(G, Irrs, i);
             //  BAD STRATEGY if flag and (dimprd le 2000) then
             if flag then
                vprint IrrMods: 
                   "Exterior square of", i, "of dim", d_i, "giving dim", dimprd;
                N := ExteriorSquare(Irrs[i]);
                Q := ConstituentsWithMultiplicities(N);
		delete N;
                vprint IrrMods, 2:"Modules produced by ExteriorSquare:", Q;
                AddModules(
		    G, K, Q, X, Next, ~Irrs, ~Duals, ~Frobs, NumIrrs, TIME
		);
                vprint IrrMods, 2:Irrs;
             end if;
          end if;

          // Set flags showing processed
          MarkSqrDone(G, i, ~Duals, ~Frobs);
	  if char2 then
	        /* 
		 In characteristic 2, the exterior square contains 
		 all we can find in the full square.
		*/
		MarkPrdDone(G, i, i, ~Duals, ~Frobs);
	  end if;

       when 3:

          // Symmetric square

          d_i := Dimension(Irrs[i]);
          dimprd := d_i*(d_i+1) div 2;
	  flag, X := HasNewSymmetricConstituent(G, Irrs, i);
          if flag and (dimprd le 2000) then
             vprint IrrMods: 
                "Symmetric square of", i, "of dim", d_i, "giving dim", dimprd;
             N := SymmetricSquare(Irrs[i]);
             Q := ConstituentsWithMultiplicities(N);
	     delete N;
             vprint IrrMods, 2:"Modules produced by SymmetricSquare:", Q;
             AddModules(G, K, Q, X, Next, ~Irrs, ~Duals, ~Frobs, NumIrrs, TIME);
             vprint IrrMods, 2:Irrs;
          end if;

          // Set flags showing processed
          MarkPrdDone(G, i, i, ~Duals, ~Frobs);

      when 4:

         // subgps := G`Lixsubs;
         H := G`Lixsubs[Next[2]];
	 flag, X := HasNewPermutationConstituent(G, H, i);
         if flag then
             vprint IrrMods: "Permutation module from subgroup number", 
                 i, "giving dim", Next[4];
             //if Degree(G) lt 500 then
             if Next[4] lt 300 then
                M := PermutationModule(G, H, K);
                Q := ConstituentsWithMultiplicities(M);
		vprint IrrMods, 2: "Modules produced by direct perm chop:", Q;
             else
                Q := PermCond(G, H, K);
		 vprint IrrMods, 2: "Modules produced by PermCond:", Q;
             end if;
	     complete := &+[Dimension(u[1])*u[2]:u in Q] eq Next[4];
             AddModules(G, K, Q, X, Next, ~Irrs, ~Duals, ~Frobs, NumIrrs, TIME);
	     if not complete then
		Q := PermCond(G, H, K:pPrime := true);
		vprint IrrMods, 2: "Modules produced by PermCond:", Q;
		AddModules(G, K, Q, X, Next, ~Irrs, ~Duals, ~Frobs, NumIrrs, TIME);
	     end if;
             vprint IrrMods, 2:Irrs;
          end if;

          // Set flags showing processed
          MarkMaxDone(G, i);

   end case;

   Q := 0; // force deletion of Q if set.

   end while;
   
   if not done then 

       //time subs := Subgroups(G : IndexLimit := 10000);
       //nsubs := #subs;
       //for i := nsubs to 1 by -1 do
       //   H := subs[i]`subgroup;
       //   // H;
       //   if HasNewPermutationConstituent(G, H, 0) then
       //        printf "\n Perm module defined by subgroup H has new irreducible.\n";  
       //        H;
       //   end if;
       //end for;
          
       " *** ERROR -- not all irreducible modules found."; 
   end if;

   return Irrs;

end function;

/////////////////////////////////////////////////////////////////////////////

pRegularClasses := function(G, p)

/* Determine the p-regular classes for the group G */

   Cls := Classes(G);
   pCls := {@ @};
   for i := 1 to #Cls do
      if (Cls[i][1] mod p ne 0) then 
          Include(~pCls, i);
      end if;
   end for;
  
   return pCls;

end function;


///////////////////////////////////////////////////////////////////////////////

AddModules := procedure(G, M, K, X, Next, ~Irrs, ~Duals, ~Frobs, NumIrrs, TIME)


   t := Next[1];
   i := Next[2]; 
   j := Next[3];
   OldTally := #Irrs;

   AddModulesSub(G, M, K, X, ~Irrs, ~Duals, ~Frobs);

   // Verbose output
   Tally := #Irrs;
   if Tally gt OldTally then 
      vprint IrrMods:  "*** New modules found: ", 
      [<i, Dimension(Irrs[i]), #Field(Irrs[i])> : i in [OldTally+1 .. Tally] ]; 
      // PrintFileMagma("O73_F2_mods_part", Irrs : Overwrite := true);
      vprintf IrrMods: "Now have %o modules of %o (time %o, MB: %.1o)\n",
	  #Irrs, NumIrrs, Cputime(TIME), MB();
      //MemProfile();

      // vprint IrrMods: G`pMod`Table;
      // print [Irrs[i] : i in [OldTally + 1 .. Tally] ]; 
      // print "Product", Next, "extended the list of irreducibles to: ";
      // Irrs;
      // print [<i, Dimension(Irrs[i]), #Field(Irrs[i])> : i in [1 .. Tally] ]; 
   else
        // print "Product", Next, "did not produce any new irreducibles.";
   end if;

end procedure;

///////////////////////////////////////////////////////////////////////////////

IsKnown := function(Irrs, M);

      if #Irrs eq 0 then return false, _; end if;

      d := Dimension(M);
      for i := 1 to #Irrs do
         U := Irrs[i];
         if Dimension(U) ne d then continue; end if;
         if Field(U) eq Field(M) then
               if IsIsomorphic(M, U) then 
                    return true, i; 
               else
                    continue;
               end if;
         else
               M1, U1 := ModulesOverCommonField(M, U);
               if IsIsomorphic(M1, U1) then 
                    return true, i; 
               else
                    continue;
               end if;
         end if;
      end for;
      return false, _;

end function;


/////////////////////////////////////////////////////////////////////////////

MarkPrdDone := procedure(G, i, j, ~Duals, ~Frobs)

    next_i := i;
    next_j := j;
    repeat
	G`pMod`PrdFlags[next_i, next_j] := 1;
	G`pMod`PrdFlags[Duals[next_i], Duals[next_j]] := 1;
	next_i := Frobs[next_i];
	next_j := Frobs[next_j];
    until i eq next_i and j eq next_j;

end procedure;

/////////////////////////////////////////////////////////////////////////////

MarkSqrDone := procedure(G, i, ~Duals, ~Frobs)

    next_i := i;
    repeat
	G`pMod`SqrFlags[next_i] := 1;
	G`pMod`SqrFlags[Duals[next_i]] := 1;
	next_i := Frobs[next_i];
    until i eq next_i;

end procedure;


/////////////////////////////////////////////////////////////////////////////

MarkMaxDone := procedure(G, i)

    G`pMod`LixFlags[i] := 1;

end procedure;


/////////////////////////////////////////////////////////////////////////////

NonIsomorphicModules := function(Mods)

      NIMods := [];
      for i := 1 to #Mods do
         N := Mods[i];
         if not IsKnown(NIMods, N) then
             Append(~NIMods, N);
         end if;
      end for;
    
      return NIMods;

end function;

///////////////////////////////////////////////////////////////////////////////

NextProduct := function(G, Irrs, Duals, DimLim)

   /* Given a list Irrs of irreducible modules together with a list of
      dual pointers, Duals, determine the tensor product of least degree
      that has not yet been formed and return a triple containing the
      numbers of the corresponding irreducibles together with the degree of
      the product module */

   sqrflgs := G`pMod`SqrFlags;
   prdflgs := G`pMod`PrdFlags;
   lixflgs := G`pMod`LixFlags;
   lixsubflg := G`pMod`LixSubFlg;
   lixind  := G`pMod`LixInd;
   lixstep := G`pMod`LixStep;
   lixbnd  := G`pMod`LixBnd;
   lixlim  := G`pMod`LixLim;
   lixsubs := G`Lixsubs;

   best := 1000000;
   Next := <0, 0, 0, 0>;
   for i := 2 to #Irrs do
      Dimi := Dimension(Irrs[i]);
      for j := i to #Irrs do
         if prdflgs[i, j] eq 0 then

            // Tensor product (i ne j)
 
            if i ne j then
               t := 1;
               m := Dimi*Dimension(Irrs[j]);
            else

            //Tensor square -- take exterior and symmetric parts

               if sqrflgs[i] eq 0 then 
                  t := 2; 
                  m := (Dimi*(Dimi-1)) div 2; 
               else
                  t := 3; 
                  m := (Dimi*(Dimi+1)) div 2; 
               end if; 

            end if; // prdflgs[i, j] eq 0

	    if m lt best then 
	       best := m;
	       Next :=  <t, i, j, m>; 
	    end if;

         end if;

      end for;
   end for;

   // if best gt 1000 then best := 1000000; end if;
   if true then
   // if lixsubflg then
      subgps := true;
      while subgps do

         for i := 1 to #lixsubs do
            indx := Index(G, lixsubs[i]);
            if lixflgs[i] eq 0 and indx lt best then
               best := indx;
               t := 4;
               Next := <t,i,0,indx>;       
            end if;
         end for;

         if best gt lixind + 500 then

             if (lixind le DimLim) and (lixind + lixstep le lixbnd) then
                lixind := lixind + lixstep; 
                G`pMod`LixInd := lixind;
                lixsubs := LowIndexSubgroups(G, lixind);
                vprint IrrMods: [ Index(G, lixsubs[i]) : i in [1..#lixsubs] ];
                if #lixsubs gt lixlim then
                     lixsubs := lixsubs[1..lixlim];
                end if;
                G`Lixsubs := lixsubs;
              else
                Next[1] := 0;
                subgps := false;
              end if;

          else
              subgps := false;
         end if;

      end while;

   end if;

   if Next[1] ne 0 and Next[4] lt DimLim then
       // "Next returns", Next;
       return true, Next;
   else
      return false, <0,0,0,0>;
   end if;

end function;


/////////////////////////////////////////////////////////////////////////////

HasNewSymmetricConstituent := function(G, Irrs, i)

   /* 
      Given integers i and j, determine whether the symmetric
      square of Irr(i)  contains a new irreducible module.
   */


   Chars := G`pMod`Table;
   K := G`pMod`BrauerField;
   N := G`pMod`NumCls;
   Xi := Chars[i];

   // Symmetric square

      sigma := G`pMod`Sqrs;
      a := (K!2)^-1;
      X := [ a*(Xi[k]^2 + Xi[sigma(k)]) : k in [1..N] ];
      yes := IsConsistent( G`pMod`TableEchelon, Vector(K, N, X) );

   return not yes, X;

end function;


/////////////////////////////////////////////////////////////////////////////

HasNewExteriorConstituent := function(G, Irrs, i)

   /* 
      Given integers i and j, determine whether the exterior
      square of Irr(i)  contains a new irreducible module.
   */

   Chars := G`pMod`Table;
   K := G`pMod`BrauerField;
   N := G`pMod`NumCls;
   Xi := Chars[i];

      sigma := G`pMod`Sqrs;
      a := (K!2)^-1;
      X := [ a*(Xi[k]^2 - Xi[sigma(k)]) : k in [1..N] ];
      yes := IsConsistent( G`pMod`TableEchelon, Vector(K, N, X) );

   return not yes, X;

end function;


/////////////////////////////////////////////////////////////////////////////

HasNewTensorConstituent := function(G, Irrs, i, j)

   /* 
      Given integers i and j, determine whether the tensor
      product Irr(i) x Irr(j)  contains a new irreducible module.
   */

   Chars := G`pMod`Table;
   K := G`pMod`BrauerField;
   N := G`pMod`NumCls;
   Xi := Chars[i]; assert Xi[1] eq K!Dimension(Irrs[i]);
   Xj := Chars[j]; assert Xj[1] eq K!Dimension(Irrs[j]);
    
   X := [ Xi[k] * Xj[k] : k in [1..N] ];
   yes := IsConsistent( G`pMod`TableEchelon, Vector(K, N, X) );

   // "In HasNewConstituent with", i, j, yes;

   return not yes, X;

end function;


/////////////////////////////////////////////////////////////////////////////

HasNewPermutationConstituent := function(G, H, i)

   /* 
      Given a subgroup H of G determine whether the permutation module 
      afforded by the action of G on the cosets of H contains a new 
      irreducible module.
   */


   Cls := Classes(G);
   K := G`pMod`BrauerField;
   N := G`pMod`NumCls;
   pCl := G`pMod`pCls;
   phi, Im, Ker := CosetAction(G, H);
   X := [ K!#Fix(phi(Cls[pCl[i]][3])) : i in [1..#pCl] ];

   yes := IsConsistent( G`pMod`TableEchelon, Vector(K, N, X) );

   return not yes, X;

end function;

/////////////////////////////////////////////////////////////////////////////

ModulesSortCmp := function(M, N)

    /* Comparison routine for sorting final output */

    r := Dimension(M) - Dimension(N);
    if r ne 0 then 
	return r; 
    else
	return Degree(BaseRing(M)) - Degree(BaseRing(N));
    end if;
end function;

///////////////////////////////////////////////////////////////////////////////

field_degree_poly := function(f)
    coeffs := Coefficients(f);
    K := sub<Universe(coeffs)|1>;
    deg := 1;
    coeffs := [a:a in coeffs|not IsZero(a)];
    for a in coeffs do
        deg := Lcm(deg, Degree(MinimalPolynomial(a, K)));
    end for;
    return deg;
end function;

reduce_field_poly_seq := function(Q)
    deg := 1;
    for f in Q do
        deg := Lcm(deg, field_degree_poly(f));
    end for;
    bigK := BaseRing(Universe(Q));
    if deg eq Degree(bigK) then
        return Q;
    end if;
    K := sub<bigK|deg>;
    P := PolynomialRing(K);
    return [P|f:f in Q];
end function;

function EltWithOrder(K, e)
    q1 := #K - 1;
    k := q1;
    P := PrimeBasis(e);
    M := [];
    for p in P do
	m := 0;
	while IsDivisibleBy(k, p) do
	    k div:= p;
	    m +:= 1;
	end while;
	assert m gt 0;
	Append(~M, m);
    end for;
    o := q1 div k;

    EM := [Valuation(e, p): p in P];

// "P:", P;
// "M:", M;
// "EM:", EM;
// "o:", o;

    repeat
	h := 1;
	repeat 
	    r := Random(K);
	until not IsZero(r);
	r := r^k;
	fail := false;
// "new";
	for i := 1 to #P do
	    p := P[i];
	    kk := o div p^M[i];
	    s := r^kk;
	    m := 0;
	    while not IsOne(s) do
		m +:= 1;
		if m eq M[i] then
		    break;
		end if;
		s := s^p;
	    end while;
// printf "p: %o, m: %o, em: %o\n", p, m, EM[i];

	    if m lt EM[i] then
		fail := true;
		break;
	    end if;

	    h *:= p^(m - EM[i]);
	end for;
    until not fail;
// "h:", h;
// Factorization(h);

    r := r^h;
    return r;
end function;

roots_of_unity := function(p, Q)

    assert forall{o:o in Q|Gcd(p,o) eq 1};
    assert #Factorization(p) eq 1;

    if #Q eq 0 then Q := [1]; end if;
    e := Lcm(Q);
    fe := Factorization(e);
    ppows := {@ t[1]^t[2]: t in fe @};
    primes := {@ t[1]: t in fe @};
    pp_elts := [**];

    /* get elts with prime power orders */
    for q in ppows do
        ord := Modorder(p, q);
        K := GF(p, ord);
        Append(~pp_elts, EltWithOrder(K, q));
    end for;

    /* build final answers */
    res := [* *];
    for o in Q do

	/* build o-th root of unity mod p */
        if o eq 1 then
	    /* really easy case */
            Append(~res, GF(p)!1);
            continue o;
        end if;

	/* the field it will live in */
	degK := Modorder(p, o);
	K := GF(p, degK);

	/* build prime power order bits of root of unity */
        fo := Factorization(o);
        temp := [* *]; /* storage for prime power order bits */
        for t in fo do
            po := t[1];
            eo := t[2];
            ind := Index(primes, po);
            assert fe[ind, 1] eq po;
            ee := fe[ind,2];
            zeta := pp_elts[ind];
	    z := zeta^(po^(ee-eo));
	    degzeta := Degree(Parent(pp_elts[ind]));
	    if degK mod Degree(Parent(pp_elts[ind])) ne 0 then
		z := GF(p, Modorder(p,po^eo)) ! z;
	    end if;
            Append(~temp, K!z);
        end for;

	/* is o a prime power? */
        if #temp eq 1 then 
            Append(~res, temp[1]);
            continue o;
        end if;

	/* build this one */
        r := K!1;
        for i := 1 to #fo do
            rt := temp[i];
            ppo := fo[i,1]^fo[i,2];
	    /* assert Order(rt) eq ppo; */
            r *:= rt ^ Modinv(o div ppo, ppo);
        end for;
        Append(~res, r);
    end for;

// conditions satisfied by elts of res 
// comment out checks as they take a bit of time!
// assert forall{i:i in [1..#Q]|Order(res[i]) eq Q[i]}; /* orders as required */
// assert forall{0:i,j in [1..#Q]|res[i]^(Q[i] div d) eq res[j]^(Q[j] div d)
//  where d is Gcd(Q[i], Q[j])}; /* compatibility of powers */

    return res;
end function;


InitBrauerCharacterInfo := procedure(~G, p, DimLim)
    zeit := Cputime();
    // vprint IrrMods, 2: "Precomputing the Brauer character information";
    cl := Classes(G);
    /* Get p-regular classes, skipping the identity */
    reg := {@i:i in [2..#cl]|not IsDivisibleBy(cl[i,1], p)@};
    pm := PowerMap(G);
    // vprint IrrMods, 3: "Power map found computed", Cputime(zeit), "seconds";
    info := G`pMod`BrauerInfo;
    polys := [**];
    vals := [**];
    lift_where := [];
    reg_ords := {@ cl[i,1]: i in reg @};
    roots := roots_of_unity(p, reg_ords);
    // vprint IrrMods, 3:"Found roots of unity mod", p, "in", Cputime(zeit), "seconds";
    bcp := DimLim + 1;
    e := Lcm([cl[i,1]: i in reg]);
    d := bcp mod e;
    if d eq 0 then
	bcp +:= 1;
    elif d ne 1 then
	bcp +:= e - d + 1;
    end if;
    assert bcp mod e eq 1;
    while not (#G mod bcp ne 0 and IsPrime(bcp)) do
	bcp +:= e;
    end while;
    field := GF(bcp);
    // vprint IrrMods, 2: "Brauer characters will be computed in the", field, "after", Cputime(zeit), "secs";
    big_zeta := EltWithOrder(field, e);
    /* big_zeta is an e-th root of unity in field */
    done := {@ @};
    for i in reg do
        n := cl[i, 1];
        assert e mod n eq 0;
	/* subgroup of unit grp mod n that fixes this class */
        grp := {j:j in [1..n-1]|pm(i, j) eq i};
        ind := Index(done, <n, grp>);
        if ind gt 0 then
            lift_where[i] := ind;
            continue i;
        else
            Include(~done,  <n, grp>);
            lift_where[i] := #done;
        end if;
        z := roots[Index(reg_ords, n)]; /* n-th root of unity over GF(p) */
        zeta := big_zeta ^ (e div n); /* n-th root of unity in field */
	K := Parent(z);
        P := PolynomialRing(K); X := P.1;
        n_polys := [P|];
        n_vals := [];
        to_do := {0..n-1};
        while to_do ne {} do
            r := Rep(to_do);
	    /* the following powers of z will occur together as eigenvalues */
            powers := {(r*j) mod n : j in grp};
            to_do diff:= powers;
	    /* precompute corresp. polynomial factor */
            Append(~n_polys, &*[ X-z^j : j in powers]);
	    /* precompute corresp. brauer chtr values in all powers */
            Append(~n_vals, [&+[ zeta^(k*j) : j in powers]:k in [1..n-1]]);
        end while;
        Append(~polys, reduce_field_poly_seq(n_polys));
        Append(~vals, n_vals);
    end for;
    info`lift_polys := polys;
    info`lift_vals := vals;
    info`lift_where := lift_where;
    info`pCls := reg;
    info`field := field;
    info`zeta := big_zeta;
    info`primitive := PrimitiveElement(field);
    info`lift_ords := {@Integers()| @};
    info`lift_mats := [* *];
    int_classes := {1} join {i:i in [1..#cl]|cl[i,1] mod p eq 0 or
	forall{j:j in [1..cl[i,1]]|GCD(j,cl[i,1]) ne 1 or pm(i,j) eq i}};
    info`int_classes := int_classes;
    G`pMod`BrauerInfo := info;
    // vprint IrrMods, 2: "Precomputation of Brauer Character data took", Cputime(zeit), "seconds";
end procedure;

BrauerChtr := function(G, M)
    zeit := Cputime();
    // rep_time := 0.0;
    // cp_time := 0.0;
    info := G`pMod`BrauerInfo;
    K := info`field;
    chtr := [K|Dimension(M)];
    reg := info`pCls;
    polys := info`lift_polys;
    vals := info`lift_vals;
    lift_where := info`lift_where;
    len := #reg;
    cl := Classes(G);
    pm := PowerMap(G);
    rho := Representation(M);
    p := Characteristic(BaseRing(M));
    for i := len to 1 by -1 do
	if IsDefined(chtr, i+1) then
	    continue i;
	end if;
        c := reg[i];
        w := lift_where[c];
        i_polys := polys[w];
	d_i_polys := Degree(BaseRing(Universe(i_polys)));
        i_vals := vals[w];
        i_len := #i_polys;
	n := cl[c,1];
        val := [K| 0 : k in [1..n-1]];
	// t1 := Cputime();
	rep_im := cl[c, 3]@rho;
	// rep_time +:= Cputime(t1);
	// vprint IrrMods, 3:"Class rep image:", Cputime(t1), "seconds";
	// t1 := Cputime();
        cp := CharacteristicPolynomial(rep_im);
	// cp_time +:= Cputime(t1);
	// vprint IrrMods, 3:"Char poly:", Cputime(t1), "seconds";
	d_cp := Degree(BaseRing(Parent(cp)));
	d := Gcd(d_cp, d_i_polys);
	if d lt d_cp then
	    cp := PolynomialRing(GF(p, d))!cp;
	end if;
	if d lt d_i_polys then
	    cp := Universe(i_polys)!cp;
	end if;
        for j := 1 to i_len do
            f := i_polys[j];
	    i_vals_j := i_vals[j];
            repeat
                flag, quot := IsDivisibleBy(cp, f);
                if flag then
                    cp := quot;
		    for k := 1 to n-1 do
			val[k] +:= i_vals_j[k];
		    end for;
                else
                    continue j;
                end if;
            until false;
        end for;
	for k := 1 to n-1 do
	    ck := pm(c, k);
	    ind := Index(reg, ck)+1;
	    if IsDefined(chtr, ind) then 
		continue k;
	    end if;
	    chtr[ind] := val[k];
	end for;
    end for;
    // vprint IrrMods, 3: "BrauerChtr: reps time:", rep_time, "seconds";
    // vprint IrrMods, 3: "BrauerChtr: char poly time:", cp_time, "seconds";
    vprint IrrMods, 3: "BrauerChtr:", Cputime(zeit), "seconds";
    return chtr;
end function;

///////////////////////////////////////////////////////////////////////////

FrobeniusConjugate := function(G, M)
    act := ActionGenerators(M);
    p := Characteristic(BaseRing(M));
    d := Dimension(M);
    act := [ Matrix(d, d, [x^p : x in Eltseq(m)]) : m in act ];
    res := GModule(G, act: Check := false);
    /* this doesn't work well - problem with module code reported to Allan 
    a,b := HasAttribute(M, "IsIrreducible");
    if a then
	AssertAttribute(res, "IsIrreducible", b);
    end if;
    */
    return res;
end function;

AddModuleConjugates := procedure(M, X, ~Irrs, ~Duals, ~Frobs)

    zeit := Cputime();
    G := Group(M);
    // assert BrauerChtr(G, M) eq X;
    frob_perm := G`pMod`FrobClassAction;
    inv_perm := G`pMod`DualClassAction;
    chtrs := [X];
    Q := [M];
    done := 0;
    XTable := G`pMod`Table;
    repeat
	done +:= 1;
	M := Q[done];
	X := chtrs[done];
	ind := Index(XTable, X);
	if ind eq 0 then
	    Append(~Irrs, M);
	    Append(~XTable, X);
	    Append(~Frobs, 0);
	    Append(~Duals, 0);
	    ind := #XTable;
	end if;

	if Frobs[ind] eq 0 then
	    NX := [ X[i]: i in frob_perm ];
	    indN := Index(XTable, NX);
	    if indN eq 0 then
		vprint IrrMods, 3:"Storing frobenius conjugate";
		N := FrobeniusConjugate(G, M);
	    // assert(NX eq BrauerChtr(Group(M), N));
		Append(~Irrs, N);
		Append(~XTable, NX);
		Append(~Q, N);
		Append(~chtrs, NX);
		Append(~Frobs, 0);
		Append(~Duals, 0);
		indN := #XTable;
	    end if;
	    Frobs[ind] := indN;
	end if;

	if Duals[ind] eq 0 then
	    NX := [ X[i]: i in inv_perm ];
	    indN := Index(XTable, NX);
	    if indN eq 0 then
		vprint IrrMods, 3:"Storing dual";
		N := Dual(M);
		Append(~Irrs, N);
		Append(~Q, N);
		Append(~chtrs, NX);
		Append(~XTable, NX);
		Append(~Frobs, 0);
		Append(~Duals, 0);
		indN := #XTable;
	    end if;
	    Duals[ind] := indN;
	end if;
	    
    until done eq #Q;

    G`pMod`Table := XTable;
    if assigned G`pMod`TableEchelon then
	XTable := G`pMod`TableEchelon;
	XTable := VerticalJoin(XTable, Matrix(chtrs));
    else
	XTable :=  Matrix(chtrs);
    end if;
    G`pMod`TableEchelon := EchelonForm(XTable);
    vprint IrrMods, 2: "Stored module and conjugates", Cputime(zeit), "seconds";

end procedure;

BCcmp := function(t1, t2)
    M := t1[1];
    res := Dimension(M)^2 * Degree(BaseRing(M));
    M := t2[1];
    res -:= Dimension(M)^2 * Degree(BaseRing(M));
    if res eq 0 then return t2[3] - t1[3]; end if;
    return res;
end function;

function GetAbsModule(M)
    while true do
	A, B := Meataxe(M);
	if IsIrreducible(M) then
	    return M;
	end if;
	M := Dimension(A) le Dimension(B) select A else B;
    end while;
end function;

//-----------------------------------------------------------------------------
Absolutise := function( Q )

    absQ := [];
    for t in Q do
       N := t[1];
       vprint IrrMods, 3: "Testing for absolute irreducibility", N;
       // "Processing new module:", N;
       // "Doing IsAbsolutelyIrreducible";
       is_a_i, _, deg := IsAbsolutelyIrreducible(N);
       if is_a_i then
          Append(~absQ, <t[1], t[2], 1>);
       else
	  vprint IrrMods, 3: "Doing AbsoluteRepresentation on", N;
	  if false then
	      L := ext<BaseRing(N) | deg>;
	      NL := ChangeRing(N, L);
	      IndentPush();
	      /*
	      vtime IrrMods, 3: CF := CompositionFactors(NL);
	      N_sub := CF[1];
	      */
	      vtime IrrMods, 3: N_sub := GetAbsModule(NL);
	      IndentPop();
//"WAS:", AbsoluteRepresentation(N);
	  else
	      vtime IrrMods, 3: N_sub := AbsoluteRepresentation(N);
	  end if;
          vprint IrrMods, 3: "Submodule", N_sub;
          assert Dimension(N) mod Dimension(N_sub) eq 0;
          Append(~absQ,<N_sub,t[2],Dimension(N) div Dimension(N_sub)>);
       end if;
    end for;
    return absQ;

end function;

//-----------------------------------------------------------------------------
AddModulesSub := procedure(G, K, Q, X, ~Irrs, ~Duals, ~Frobs)

    zeit := Cputime();
    absQ := Absolutise(Q);

    /* 
       At this stage the reps in absQ are the absolutely irreducible
       constituents of M. I believe that each abs. irred. is in only
       one tuple with the right multiplicity connected to it.
    */

    /* scan the elts in absQ to find out which ones we know */

    QX := [];
    unkQ := [];
    XTable := G`pMod`Table;
    for t in absQ do
	known, i := IsKnown(Irrs, t[1]);
	if known then
	    ii := i;
	    conj_list := [];
	    repeat
		Append(~conj_list, ii);
		ii := Frobs[ii];
		assert ii gt 0 and ii le #Irrs;
	    until ii eq i;
	    c := t[3];
	    assert #conj_list mod c eq 0;
	    step := #conj_list div c;
	    m := t[2];
	    for ii := 1 to #conj_list by step do
		NX := XTable[conj_list[ii]];
		X := [X[j] - m*NX[j] : j in [1..#X]];
	    end for;
	else
	    Append(~unkQ, t);
	end if;
    end for;
    if #unkQ eq 0 then
	vprint IrrMods, 1: "Split module",Cputime(zeit),"secs, nothing new";
	vprint IrrMods, 3: "X:", X;
	return;
    end if;
    vprint IrrMods, 3: "Found", #unkQ, "new absolute irreducibles";

    Sort(~unkQ, BCcmp);
    
/*
    G`pMod`NumCls;
    #Irrs;
    unkQ;
    if G`pMod`NumCls eq (#Irrs + &+[t[3] : t in unkQ]) then
    "*** Early termination ***";
       for i := 1 to #unkQ do
	   N := unkQ[i][1];
	   old_deg := Degree(K);
	   N := AbsoluteModuleOverMinimalField (N);
           new_deg := Degree(BaseRing(N));
	   if old_deg gt new_deg then
	      vprint IrrMods, 3: "Field degree", new_deg, "reduced from", old_deg;
	   end if;
	   AddModuleConjugates(N, NX, ~Irrs, ~Duals, ~Frobs);
        end for;
        return;
    end if;
*/

    for i := 1 to #unkQ do
	t := unkQ[i];
	N := t[1];
	m := t[2];
	if i gt 1 then
	    known, ind := IsKnown(Irrs, N);
	    if known then
		vprint IrrMods, 3: "Known module", N;
		ii := ind;
		conj_list := [];
		repeat
		    Append(~conj_list, ii);
		    ii := Frobs[ii];
		    assert ii gt 0 and ii le #Irrs;
		until ii eq ind;
		c := t[3];
		assert #conj_list mod c eq 0;
		step := #conj_list div c;
		for ii := 1 to #conj_list by step do
		    NX := XTable[conj_list[ii]];
		    X := [X[j] - m*NX[j] : j in [1..#X]];
		end for;
		continue i;
	    end if;
	end if;
	// old_deg := Degree(BaseRing(M));
	old_deg := Degree(K);
        // "Doing AbsoluteModuleOverMinimalField";
	N := AbsoluteModuleOverMinimalField (N);
	new_deg := Degree(BaseRing(N));
	if old_deg gt new_deg then
	    vprint IrrMods, 3: "Field degree", new_deg, "reduced from", old_deg;
	end if;
	n_Irrs := #Irrs;
           
	if i eq #unkQ and t[3] eq 1 then
	    m_inv := 1/(Universe(X)!m);
	    NX := [m_inv*X[j]: j in [1..#X]];
	    if Universe(X)!Dimension(N) eq m_inv*X[1] then
		NX := [m_inv*X[j]: j in [1..#X]];
	    else
		NX := BrauerChtr(G, N);
	    end if;
	else
	    NX := BrauerChtr(G, N);
	end if;
	AddModuleConjugates(N, NX, ~Irrs, ~Duals, ~Frobs);
	XTable := G`pMod`Table; /* should have changed */
	assert Nrows(G`pMod`TableEchelon) eq #Irrs;
	ii := n_Irrs + 1;
	conj_list := [];
	repeat
	    Append(~conj_list, ii);
	    ii := Frobs[ii];
	    assert ii gt 0 and ii le #Irrs;
	until ii eq n_Irrs+1;
	c := t[3];
	assert #conj_list mod c eq 0;
	step := #conj_list div c;
	for ii := 1 to #conj_list by step do
	    NX := XTable[conj_list[ii]];
	    X := [X[j] - m*NX[j] : j in [1..#X]];
	end for;
	if IsConsistent(G`pMod`TableEchelon, Matrix([X])) then
	    vprint IrrMods, 1: "Split module", Cputime(zeit), "seconds";
	    return;
	end if;
    end for;

    vprint IrrMods, 2: "WARNING: missed a new irreducible";
    vprint IrrMods, 3: "X:", X;

    vprint IrrMods, 1: "Split module", Cputime(zeit), "seconds";

end procedure;

ComplexChtrToBC := function(c)
// Assumes G`pMod`BrauerInfo is defined with appropriate data
    G := Group(Parent(c));
    cl := ClassesData(G);
    info := G`pMod`BrauerInfo;
    v := CharacterToModular(c, info`primitive);
    reg := info`pCls;
    K := info`field;
    res := [K|Degree(c)];
    for i in reg do Append(~res, v[i]); end for;
    return res;
end function;

BCToComplexChtr := function(G, b)
// Assumes G`pMod`BrauerInfo is defined with appropriate data
    info := G`pMod`BrauerInfo;
    cl := ClassesData(G);
    K := info`field;
    v := [K|0:i in [1..#cl]];
    v[1] := b[1];
    reg := info`pCls;
    for i := 1 to #reg do
	v[reg[i]] := b[i+1];
    end for;
    res := ChtrLiftInternal(CharacterRing(G), Vector(v), info`int_classes,
	    info`lift_ords, info`lift_mats, info`primitive);
    return res;
end function;

BCToComplexChtrSeq := function(G, b)
// Assumes G`pMod`BrauerInfo is defined with appropriate data
    chi := BCToComplexChtr(G,b);
    info := G`pMod`BrauerInfo;
    reg := info`pCls;
    res := [Degree(chi)];
    for i := 1 to #reg do
	Append(~res, chi[reg[i]]);
    end for;
    return res;
end function;

BCToComplexChtrVec := function(G, b)
// Assumes G`pMod`BrauerInfo is defined with appropriate data
    chi := BCToComplexChtrSeq(G,b);
    res := Vector(chi);;
    return res;
end function;

