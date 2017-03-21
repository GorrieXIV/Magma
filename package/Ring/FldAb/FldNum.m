freeze;

intrinsic DecompositionType(K::FldNum, p::RngIntElt) -> SeqEnum
{}
  require IsPrime(p) : "p must be a prime number";
  require IsAbsoluteField(K) : "K must be defined over Q";

  if assigned K`MaximalOrder then
    return DecompositionType(K`MaximalOrder, p);
  end if;

  if Gcd(Discriminant(K), p) eq 1 then
    return DecompositionType(EquationOrder(K), p);
  else  
    return DecompositionType(MaximalOrder(K), p);
  end if;
end intrinsic;

intrinsic DecompositionType(K::FldOrd, p::RngIntElt) -> SeqEnum
{}
  require IsPrime(p) : "p must be a prime number";
  require IsAbsoluteField(K) : "K must be defined over Q";

  return DecompositionType(Order(K), p);
end intrinsic;

intrinsic DecompositionType(K::FldNum, p::RngOrdIdl) -> SeqEnum
{}
  require IsPrime(p) : "p must be a prime ideal";
  require EquationOrder(BaseField(K)) cmpeq Order(p) :
       "p must be a prime ideal of the base field of K";

  if assigned K`MaximalOrder then
    M := K`MaximalOrder;
    return DecompositionType(M, BaseRing(M)!!p);
  end if;

  if Discriminant(K) + p eq 1*Order(p) then
    return DecompositionType(EquationOrder(K), p);
  else  
    M := MaximalOrder(K);
    return DecompositionType(M, BaseRing(M)!!p);
  end if;
end intrinsic;

intrinsic DecompositionType(K::FldOrd, p::RngOrdIdl) -> SeqEnum
{The decomposition type of the factorisation of p as a sequence of pairs <f, e>}
  require IsPrime(p) : "p must be a prime ideal";
  require EquationOrder(BaseField(K)) cmpeq Order(p) :
       "p must be a prime ideal of the base field of K";

  return DecompositionType(Order(K), p);
end intrinsic;

  

