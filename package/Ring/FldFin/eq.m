freeze;

intrinsic 'eq'( m1::Map[FldFin,FldFin], m2::Map[FldFin,FldFin] ) -> BoolElt
{Equality for homomorphisms of finie fields}
    k := Domain(m1);
    if      k       cmpne Domain(m2) 
    or Codomain(m1) cmpne Codomain(m2) then  
        return false;
    end if;
    
    require assigned m1`IsHomomorphism and m1`IsHomomorphism
        and assigned m2`IsHomomorphism and m2`IsHomomorphism : "Cannot decide equality: maps are not homomorphisms";
    
    x := PrimitiveElement(k);
    
    return m1(x) eq m2(x);
end intrinsic;
