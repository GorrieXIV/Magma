174,1
S,IsCentral,"If g central in G, return true, else false",0,2,0,0,0,0,0,0,0,180,,0,0,178,,36,-38,-38,-38,-38,-38
S,IsCentral,"If g central in G, return true, else false",0,2,0,0,0,0,0,0,0,222,,0,0,224,,36,-38,-38,-38,-38,-38
S,IsCentral,"If g central in G, return true, else false",0,2,0,0,0,0,0,0,0,108,,0,0,107,,36,-38,-38,-38,-38,-38
S,IsCentral,"If g central in G, return true, else false",0,2,0,0,0,0,0,0,0,130,,0,0,129,,36,-38,-38,-38,-38,-38
S,CentralOrder,"return smallest n such that g^n is central in its parent, which can be supplied as the optional argument ParentGroup. If Proof is false then accept a multiple of this value; the second value returned is true if the answer is exact",0,1,0,0,0,0,0,0,0,180,,148,36,-38,-38,-38,-38
S,CentralOrder,"return smallest n such that g^n is central in its parent, which can be supplied as the optional argument ParentGroup. If Proof is false then accept a multiple of this value; the second value returned is true if the answer is exact",0,1,0,0,0,0,0,0,0,222,,148,36,-38,-38,-38,-38
S,RandomElementOfPrimeOrder,"Search for a random element of specified prime order. If such is found, then return true, the element, and its SLP. MaxTries is the maximum number of random elements that are chosen. Randomiser is the random process used to construct these, and the SLP for the returned element is in the word group of this process",0,2,0,0,0,0,0,0,0,148,,0,0,178,,36,180,137,-38,-38,-38
S,RandomElementOfPrimeOrder,"Search for a random element of specified prime order. If such is found, then return true, the element, and its SLP. MaxTries is the maximum number of random elements that are chosen. Randomiser is the random process used to construct these, and the SLP for the returned element is in the word group of this process",0,2,0,0,0,0,0,0,0,148,,0,0,224,,36,222,137,-38,-38,-38
S,RandomElementOfOrder,"Search for a random element of specified order. If such is found, then return true, the element, and its SLP. If Proof is false, then accept an element whose order may be a multiple of the desired order. The final value returned indicates whether the element is known to have the precise order. If Central then search for an element which has this order modulo the centre of G. MaxTries is the maximum number of random elements that are chosen. Randomiser is the random process used to construct these, and the SLP for the returned element is in the word group of this process",0,2,0,0,0,0,0,0,0,148,,0,0,178,,36,180,137,36,-38,-38
S,RandomElementOfOrder,"Search for a random element of specified order. If such is found, then return true, the element, and its SLP. If Central then search for an element which has this order modulo the centre of G. MaxTries is the maximum number of random elements that are chosen. Randomiser is the random process used to construct these, and the SLP for the returned element is in the word group of this process",0,2,0,0,0,0,0,0,0,148,,0,0,224,,36,222,137,-38,-38,-38
S,ElementOfOrder,"Fct can be Order or ProjectiveOrder; search at most Limit times for element of (projective) order RequiredOrder; if found return element and possibly word, else return false",0,3,0,0,0,0,0,0,0,148,,0,0,-1,,0,0,-27,,180,-38,-38,-38,-38,-38
S,PrimePowerOrderElement,"p is a prime. Determine if p divides the order of g and if so return true, an element h of order a power of p, a multiplicative upper bound for order of h, the power of g equal to h, and a flag indicating if the upper bound is the true order",0,2,0,0,0,0,0,0,0,148,,0,0,-28,,36,-28,148,148,36,-38
S,PrimeOrderElement,"p is a prime. Determine if p divides the order of g and if so return true and the power of g which gives an element of order p. The algorithm is Las Vegas polynomial time, in particular it avoids integer factorisation",0,2,0,0,0,0,0,0,0,148,,0,0,-28,,36,148,-38,-38,-38,-38