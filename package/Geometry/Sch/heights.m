freeze;

/********************************************************************

                   BASIC HEIGHT FUNCTIONS 
                    
                  Steve Donnelly, Oct 2014

*********************************************************************


   So far we have C-level functions 
     Height(FldRatElt), and 
     AbsoluteLogarithmicHeight(FldAlgElt)

   Below are defined:
     Height(RngIntElt)   
     Height(Pt : Absolute:=false ) 
       for Pt on any affine or projective variety (including weighted)
       over Q, number fields, function fields ...
       (exponential height, not logarithmic)

   TO DO: function field case?

*********************************************************************/


intrinsic Height(n::RngIntElt) -> RngIntElt
{The absolute height of the integer n}
  if n eq 0 then return 1; end if;
  return Abs(n); 
end intrinsic;


intrinsic HeightOnAmbient(P::Pt : Absolute:=false, Prec:=30 ) -> RngElt
{The relative, exponential height of a point on a scheme over the rationals
or a number field. The scheme may be affine or projective.}

  K := NumberField(Ring(Parent(P)));

  require t eq FldRat or ISA(t, FldAlg) where t is Type(K) :
    "The base ring must be contained in Q or a number fields";

  // get nonzero coords
  Amb := Ambient(Scheme(P));
  if Type(Amb) eq Aff then 
    coords := Eltseq(P) cat [1];
  elif Type(Amb) eq Prj then
    g := Gradings(Amb);
    require #g eq 1 : "There is more than one grading on the ambient projective space";
    coords := Eltseq(P);
    coords := [ coords[i]^g[1,i] : i in [1..#coords] ];
  else 
    require false : "The ambient space must be affine or projective.";
  end if;
  coords := [a : a in coords | not IsZero(a)];

  if #coords le 1 then
    return 1;
  end if;
  
  if Type(K) eq FldRat then
    den := LCM([Denominator(c) : c in coords]);
    coords := [Integers() | c*den : c in coords];
    return Max([Abs(c) : c in coords]) div GCD(coords);
  end if;

  assert ISA(Type(K), FldNum);

  d := AbsoluteDegree(K);

  if IsAbsoluteField(K) then
    C := [Conjugates(c : Precision:=Prec) : c in coords];
    H := &* [Max([Abs(C[i,j]) : i in [1..#C]]) : j in [1..d]];
  else
    H := 1;
    for v in InfinitePlaces(K) do
      Hv := Max([Abs(Evaluate(c, v)) : c in coords]);
      H := H * (IsReal(v) select Hv else Hv^2);
    end for;
  end if;

  H := H / AbsoluteNorm(ideal< Integers(K) | coords >);
  
  if Absolute then H := H^(1/d); end if;

  return H;

end intrinsic;

