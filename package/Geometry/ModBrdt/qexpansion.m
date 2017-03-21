freeze;
////////////////////////////////////////////////////////////////////
//                                                                //
//                        David Kohel                             //
//              q-Expansion Bases for Brandt Modules              //
//                                                                //
////////////////////////////////////////////////////////////////////

forward EchelonSeries, ValuationOrder;

intrinsic qExpansionBasis(M::ModBrdt,prec::RngIntElt) -> SeqEnum
    {}
    PS := LaurentSeriesRing(RationalField());
    q := PS.1;
    B := Basis(M);
    F := EchelonSeries(&cat[ Parent([ PS | ]) | 
         [ PS ! ThetaSeries(B[i], B[j], prec) 
                   : i in [1..j] ] : j in [1..#B] ]);
    return F;
end intrinsic;

intrinsic qExpansionBasis(B::[ModBrdtElt],prec::RngIntElt) -> SeqEnum
    {}
    PS := LaurentSeriesRing(RationalField());
    q := PS.1;
    F := EchelonSeries(&cat[ Parent([ PS | ]) | 
         [ PS ! ThetaSeries(B[i], B[j], prec) 
                  : i in [1..j] ] : j in [1..#B] ]);
    return F;
end intrinsic;

function EchelonSeries(B)
   // Returns the echelonized sequence of power series spanning
   // the same space.

   error if not IsField(CoefficientRing(Universe(B))),
      "Series base ring must be a field";
   if #B eq 0 then return B; end if;
   for i in [1..#B] do
      Sort(~B,ValuationOrder);
      n1 := Valuation(B[i]);
      if n1 lt AbsolutePrecision(B[i]) then 
         B[i] := B[i]/Coefficient(B[i],n1);
         for j in [1..#B] do
            if j lt i then
               B[j] := B[j] - Coefficient(B[j],n1)*B[i]; 
            elif j gt i and (n1 eq Valuation(B[j])) then 
               B[j] := B[j] - Coefficient(B[j],n1)*B[i]; 
               n2 := Valuation(B[j]);
               if n2 lt AbsolutePrecision(B[i]) then 
                  B[j] := B[j]/Coefficient(B[j],n2);
               end if;
            end if;
         end for;
      end if;
   end for;         
   while #B gt 0 and RelativePrecision(B[#B]) eq 0 do
      Remove(~B,#B); 
      if #B eq 0 then break; end if; 
   end while; 
   return B;
end function;

function ValuationOrder(f,g)
   // Partial ordering of series based on valuation.
   n := Valuation(f);
   m := Valuation(g);
   if n gt m then return 1;
   elif n lt m then return -1;
   end if;
   return 0;
end function;

