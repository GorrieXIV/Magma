freeze;

/* 
  This file contains the functions that compute generators
  for the subgroups of the classical group G that are used in the 
  rewriting process.
  
  PSubgroup returns the p-core of the stabilizer of 
  <e_2,...,e_m,f_m,...,f_1>.
  
*/
  
import "bbclassical.m":B, BBType, BBField, BBStandardGenerators, 
  BBDimension;
import "elements.m":X_, Tf1aw, RootElements;

/* The following return a list of SLPs that contains slps to Siegel
   transformations corresoponding to gamma^i in the [e1,b] position and 
   0-s elsewhere.  */
                        
forward SLPToSiegelTrans;
                        
SLPToSiegelTrans := function( G : EvaluateSLPs := false, Transpose := false )
    
  gens := BBStandardGenerators( G );  
  
  // once calculated, the output of this function is stored.
    
  if Transpose and assigned G`SiegTransTranspose then
      // if we need the values and they are not yet computed we compute them   
      if EvaluateSLPs and #G`SiegTransTranspose eq 1  then
            G`SiegTransTranspose := <G`SiegTransTranspose[1],
                                    Evaluate( G`SiegTransTranspose[1], gens )>;
      return G`SiegTransTranspose[1], G`SiegTransTranspose[2],
             G`SiegTransTranspose[3];
      elif EvaluateSLPs then
          return G`SiegTransTranspose[1], G`SiegTransTranspose[2],
                 G`SiegTransTranspose[3];
      else 
          return G`SiegTransTranspose[1];
      end if;
  end if;         
      
  if not Transpose and assigned G`SiegTrans then
      // if we need the values and they are not yet computed we compute them   
      if EvaluateSLPs and #G`SiegTrans eq 1  then
            pgens := Evaluate( G`SiegTrans[1], gens );
          G`SiegTrans := <G`SiegTrans[1], pgens, 
                         sub< Universe( pgens ) | pgens >>;
          return G`SiegTrans[1], G`SiegTrans[2], G`SiegTrans[3];
      elif EvaluateSLPs then
          return G`SiegTrans[1], G`SiegTrans[2], G`SiegTrans[3];
      else 
          return G`SiegTrans[1];
      end if;
  end if; 
  
  F := BBField( G );
  d := BBDimension( G );
  q := #F;  
  type := BBType( G );
  p := Characteristic( F );
  e := Round( Log( p, q ));
  wittindex := case< type | "SL": d, "Omega-": d/2-1, default: Floor( d/2 )>;
  wittdefect := d-2*wittindex;
  
  // SU(3,2) needs to be handled differently
  
  if <type,d,q> eq <"SU",3,4> and EvaluateSLPs then
      slps := [B.8,B.10,B.3];
      pgens := EvaluateSLPs( slps, gens );
      G`SiegTrans := <slps,pgens,sub< Universe( pgens ) | pgens >>;
      return G`SiegTrans[1], G`SiegTrans[2], G`SiegTrans[3];
  elif <type,d,q> eq <"SU",3,4> then
      slps := [B.8,B.10,B.3];
      G`SiegTrans := <slps>;
      return G`SiegTrans[1];
  end if;
        
  // set up the beginning of the SLP
    
  /* this variable detects if G has regular Seigel element of the form
     T_{f_1,e_2} and T_{f_1,f_n}. */                            
  hasregularsiegelelement := (type eq "SL" and d gt 1) or
                             (type eq "Sp" and d gt 2) or 
                             (type eq "SU" and d gt 3) or
                             (type eq "Omega+" and d gt 2) or
                             (type eq "Omega" and d gt 3) or  
                             (type eq "Omega-" and d gt 4);

  // V is a permutation element that fixes 1, D is a diagonal element.
  V := B.2*B.5;
  
  if <type,Transpose> ne <"SL",true> then 
      D := B.4^-1; 
  else 
      D := B.4;
  end if;
              
  /* In some cases this diagonal has additional non-trivial
     entries that cause confusion, and hence we add another diagonal 
     element.*/
              
  if type eq "SL" or ( type in [ "SU", "Omega+" ] and d ge 4 ) then 
      D1 := D^V;
  end if;
  
  // slps will hold the slps
    
  slps := [];
  
  if hasregularsiegelelement and Transpose then 
      siegslp := (B.6^-1)^B.5;
      Append( ~slps, siegslp ); // add the first Siegel element
  elif hasregularsiegelelement and not Transpose then
      siegslp := B.6;
      Append( ~slps, siegslp ); // add the first Siegel element
  end if;
     
  up := (d-wittdefect)/2; 
  for i in [2..up] do
      
      /* we usually conjugate with the 3rd entry of slp. 
         sometimes with the 4th. */
        
      if <type,d> eq <"Omega+",4> then
          conjel := B.10;
      elif type in ["SL","SU","Omega+"] and i eq 2 then
          conjel := D1;
      else
          conjel := D;
      end if;
          
      // we conjugate the last Siegel element with the diagonal matrix
      for j in [1..e-1] do
          Append( ~slps, slps[#slps]^conjel );
       end for;
              
      if i ne up then
          /* we calculate the Siegel element with 1 in the 
          [e1,b] position where b is the next basis element */            
          siegslp := siegslp^V;
          if type in ["SL","Omega+","Omega","Omega-"] then
              // in SL and Omega(+-) we change the -1 entry to 1
              siegslp := siegslp^-1;
          end if;
          slp := siegslp;
          Append( ~slps, slp );
      end if;
  end for;
  
  // in SL we are done
  if type eq "SL" and Transpose then 
      if EvaluateSLPs then
          pgens := Evaluate( slps, gens );
          G`SiegTransTranspose := <slps,pgens,sub< Universe( pgens ) | pgens >>;
          return G`SiegTransTranspose[1], G`SiegTransTranspose[2],
                 G`SiegTransTranspose[3];
      else
          G`SiegTransTranspose := <slps>; 
          return G`SiegTransTranspose[1];
      end if;
  elif type eq "SL" then 
      if EvaluateSLPs then
          pgens := Evaluate( slps, gens );
          G`SiegTrans := <slps,pgens,sub< Universe( pgens ) | pgens >>;
          return G`SiegTrans[1], G`SiegTrans[2], G`SiegTrans[3];
      else
          G`SiegTrans := <slps>; 
          return G`SiegTrans[1];
      end if;
  end if;
  
  if hasregularsiegelelement then
      // we need now the inverse of the permutation matrix in the 2nd pos
      V := V^-1;  
      // the next Siegel element is gens[7]^v    
      siegslp := B.7^V;  
      
      // in Omega this element needs inverted
      if <type,d mod 4> eq <"Omega",3> or <type,d mod 4> eq <"Omega-",2> 
         or <type,d mod 4> eq <"Omega+",0> then  
         siegslp := siegslp^-1;
      end if;
      Append( ~slps, siegslp );
  end if;
        
  // essentially repeating the loop above
          
  for i in [2..up] do
      
      if type eq "SU" and d eq 4 then
      /* in this case we use (gens[4]^(gens[1]^gens[2]))^-1;
            to conjugate   */
         conjel := (B.4^(B.1^B.2))^-1;       
      elif <type,d> eq <"Omega+",4> then
          conjel := B.10;
      elif type in [ "SU","Omega+"] and i eq up then
          conjel := D1;
      else
          conjel := D;    
      end if;

      for j in [1..e-1] do
          Append( ~slps, slps[#slps]^conjel );
      end for;
            
      if i ne up then
          siegslp := siegslp^V;
          if type in ["Omega+","Omega","Omega-"] then
              siegslp := siegslp^-1;
          end if;
          slp := siegslp;
          Append( ~slps, slp );
      end if;    
   end for;

   /* orthogonal groups contain no transvections.
      if the type os Omega+ then we are done. */
       
   if type eq "Omega+" then
          if EvaluateSLPs then
              pgens := Evaluate( slps, gens );
              G`SiegTrans := <slps,pgens,sub< Universe( pgens ) | pgens >>;
              return G`SiegTrans[1], G`SiegTrans[2], G`SiegTrans[3];
          else
              G`SiegTrans := <slps>; 
              return G`SiegTrans[1];
          end if;
  end if;
   
   // if type is Omega- then we add T_{f_1,alpha w_1 + beta w_2} 
   if type eq "Omega-" then
       Append( ~slps, B.8 );    
       for i in [1..e-1] do
	   Append( ~slps, slps[#slps]^(B.10^-1));
       end for;
    
       Append( ~slps, B.9 );
       for i in [1..e-1] do
	   Append( ~slps, slps[#slps]^(B.10^-1));
       end for;    
    
       if EvaluateSLPs then
           pgens := Evaluate( slps, gens );
           G`SiegTrans:= < slps,  pgens, sub< Universe( pgens ) | pgens >>;
           return G`SiegTrans[1], G`SiegTrans[2], G`SiegTrans[3];
       else
           G`SiegTrans:= < slps >;
           return G`SiegTrans[1];
       end if;
   end if; 
         
  /* in case of SU( odd, q ) and Omega( odd, q ) we need to add 
     Siegel transforms of the form T_{f_1,alpha w}
     where alpha runs through some F_p-basis of F_q */
      
  if IsOdd( d ) then
      Append( ~slps, B.8 );
      for i in [1..e-1] do
          if type eq "SU" and q eq 4 then
              conjel := B.4^B.2;
          elif type eq "SU" then
              conjel := B.4;
          else
              conjel := B.4^-1;
          end if;
          Append( ~slps, slps[#slps]^conjel );
      end for;
  end if; 
  
  // if the type is Omega then we are done
  if type eq "Omega" then
      if EvaluateSLPs then
          pgens := Evaluate( slps, gens );
          G`SiegTrans := <slps,pgens, sub<Universe( pgens ) | pgens >>;
          return G`SiegTrans[1], G`SiegTrans[2], G`SiegTrans[3];
       else
           G`SiegTrans := <slps>; 
           return G`SiegTrans[1];
       end if;
   end if;
  
  // In the cases of Sp and SU we need to add the transvections
  Append( ~slps, B.3 );
   
  e0 := case< type | "SU":e/2, default: e >;
            
  for i in [1..e0-1] do
      conj := case< type | "Sp": B.4^-1, "SU":B.10, default: B.4^-1 >;
      Append( ~slps, slps[#slps]^conj );
  end for;
          
  if EvaluateSLPs then 
      pgens := Evaluate( slps, gens );
      G`SiegTrans := <slps,pgens,sub< Universe( pgens ) | pgens >>;
      return G`SiegTrans[1], G`SiegTrans[2], G`SiegTrans[3];
  else
      G`SiegTrans := <slps>; 
      return G`SiegTrans[1];
  end if;
  
end function;

/* 
  The following constructs stabilizer of E1 in G. Transpose is needed
  in the SL case. When "on" then the transpose of the stabilizer
  is returned.
*/
    
StabilizerOfE1 := function( G : Transpose := false )
      
      if not Transpose and assigned G`StabilizerOfE1 then
          return G`StabilizerOfE1;
      elif Transpose and assigned G`StabilizerOfE1Transpose then
          return G`StabilizerOfE1Transpose;
      end if; 
            
     gens := BBStandardGenerators( G );
      type := BBType( G );
      dim := BBDimension( G );
      q :=    #BBField( G );
        
        // low dim groups have no gens[5].
        // the following boolean will show which ones do.

      hasgens5 := not < type, dim > in { <"SU",4>, 
                          <"Sp",4>, 
                          <"SU",5>, 
                          <"Omega-",4>,
                          <"Omega-",6>,
                          <"Omega",5>,
                          <"Omega",3> };

      if type eq "SL" and dim eq 2 and not Transpose then
          
          stabgens := [ gens[3]^gens[1], gens[4] ];
          
      elif type eq "SL" and dim eq 2 and Transpose then
          
          stabgens := [ gens[3], gens[4] ];
          
      elif type eq "SU" and dim eq 3 then
          
          stabgens := [ gens[4],gens[10],gens[3]^gens[1], gens[8]^gens[1]]; 
          
      elif type eq "Omega+" and dim eq 4 then
                    
          stabgens := [ gens[4], gens[6]^gens[5], gens[7]^gens[1], gens[10]];
          
      elif type eq "Omega-" and dim eq 4 and IsOdd( q ) then
          
          stabgens := [ gens[4], gens[11], gens[8]^gens[1]];

      elif  type eq "Omega-" and dim eq 4 and IsEven( q ) then
          
          stabgens := [ gens[4], gens[11], 
                        gens[8]^gens[2]*gens[1]^(gens[2]^-1)];
          
      elif type eq "Omega" and dim eq 3 then
          
          stabgens := [ gens[4], gens[8]^gens[1]];
          
      elif type eq "Omega-" and IsEven( q ) then
          
          stabgens := [ 
                        gens[1]^gens[2]^-1,
                        gens[2]*gens[5],
                        gens[3]^gens[2],
                        gens[4],
                        gens[4]^gens[2],
                        case< hasgens5 | true:  gens[5]^gens[2],
                        default: One( G )>,
                        gens[6]^gens[2],
                        //gens[7]^gens[2],
                        //gens[8]^gens[2],
                        //gens[9]^gens[2],
                        gens[10],
                        gens[3]^gens[5],
                        gens[6]^gens[2]^-1];
          
    elif not Transpose then
        

        stabgens := [ 
	          // the expression for gens[1] is different in Omega+
                      case< type | "Omega+": gens[1]^gens[2], 
                      default: gens[1]^gens[2]^-1 >,
                      gens[2]*gens[5],
                      gens[3]^gens[2],
                      gens[4],
                      gens[4]^gens[2],
		  // low dim groups have no gens[5] 
                      case< hasgens5 | true: gens[5]^gens[2],
                      default: One( G )>,
                      gens[6]^gens[2],
		      case< <type,dim> | <"Omega+",4>: gens[7]^gens[2],
                                         default: One( G )>,
                      case< <type,dim> | <"Omega+",6>: gens[7]^gens[2],
                                         default: One( G )>,	  
                      gens[8]^gens[2],
                      gens[9]^gens[2],
                      gens[10],
                      gens[3]^gens[5],
                      gens[7]^gens[1],
                      gens[8]^gens[1],
                      gens[9]^gens[1] ];

    elif Transpose then
    
        stabgens := [ gens[3]^gens[2]^2,
                      gens[2]*gens[5],
                      gens[1]*gens[2],
                      gens[4]^gens[2],
                      gens[3] ];
        
    end if;
    
    stab := sub< GL( Degree( G ), BaseRing( G )) | stabgens >;
    
    if not Transpose then
        G`StabilizerOfE1 := stab;
    else
        G`StabilizerOfE1Transpose := stab;
    end if;
    
    return stab;
end function;
    
    
/* 
  the following is a function that returns part of the generating
  set of PSubgroup, namely elements of the form T_{f1,b}. needed
  in SmallerMatrix.
*/
    
// the following returns the $i$-th long root subgroup in PSubgroup( G )
// tested only for Omega
  
LongRootGroup := function( G, pos : Transpose := false )
    
    q := #BBField( G );
    _, _, d := IsPrimePower( q );  
    dim := BBDimension( G );
    gens := BBStandardGenerators( G );
    type := BBType( G );
    
    if type eq "Omega+" then
        S := gens[1]*gens[5];
    elif type eq "Omega-" and IsEven( q ) then
        S := gens[1]^2;
    else
        S := gens[1];
    end if;
    
    D := gens[4];
    
    if type eq "Omega+" and pos eq 1 then
        D := D^gens[2];
    end if;
    
    R := RootElements( G : Transpose := Transpose )[pos];

    gens := { R^(D^i) : i in [0..d-1] };
    
    return sub< Universe( gens ) | gens >;
end function;
    
    
    
        
