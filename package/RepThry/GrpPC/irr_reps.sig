174,1
S,GModule,Return the G module M corresponding to the representation D,0,1,0,0,0,0,0,0,0,175,,103,-38,-38,-38,-38,-38
S,MakeCyclotomic,"Given algebraic numbers known to lie in a cyclotomic field, change the universe of the sequence to be cyclotomic",1,0,1,82,0,-10,1,0,0,0,0,0,0,0,82,,82,-38,-38,-38,-38,-38
S,CharacterFromTraces,Create the character in RG corresponding to the given traces in CC. (Note: CC must describe a group character; no checking is done.),1,1,1,82,0,-45,2,0,0,0,0,0,0,0,82,,0,0,40,,39,-38,-38,-38,-38,-38
S,Character,Create the character corresponding to the given representation D,0,1,0,0,0,0,0,0,0,175,,39,-38,-38,-38,-38,-38
S,Character,Create the character corresponding to the current representation specified by the process P,0,1,0,0,0,0,0,0,0,148,,39,-38,-38,-38,-38,-38
S,Character,Create the character corresponding to the given G-module M,0,1,0,0,0,0,0,0,0,103,,39,-38,-38,-38,-38,-38
T,SolRepProc,-,0
A,SolRepProc,5,StartArgs,AbelLinReps,LoopPts,RepStack,Conditions
S,AbsolutelyIrreducibleRepresentationsInit,Initialize a Process for calculating all linear representations of a soluble group G for the rational field F,0,2,0,0,0,0,0,0,0,262,,0,0,129,,SolRepProc,-38,-38,-38,-38,-38
S,AbsolutelyIrreducibleRepresentationsInit,Initialize a Process for calculating all linear representations of a soluble group G for the rational field F,0,2,0,0,0,0,0,0,0,84,,0,0,129,,SolRepProc,-38,-38,-38,-38,-38
S,AbsolutelyIrreducibleModulesInit,Initialize a Process for calculating all linear representations of a soluble group G for the finite field F,0,2,0,0,0,0,0,0,0,262,,0,0,129,,SolRepProc,-38,-38,-38,-38,-38
S,AbsolutelyIrreducibleModulesInit,Initialize a Process for calculating all linear representations of a soluble group G for the finite field F,0,2,0,0,0,0,0,0,0,84,,0,0,129,,SolRepProc,-38,-38,-38,-38,-38
S,IrreducibleRepresentationsInit,Initialize a Process for calculating all linear representations of a soluble group G for the rational field F,0,2,0,0,0,0,0,0,0,262,,0,0,129,,SolRepProc,-38,-38,-38,-38,-38
S,IrreducibleRepresentationsInit,Initialize a Process for calculating all linear representations of a soluble group G for the rational field F,0,2,0,0,0,0,0,0,0,84,,0,0,129,,SolRepProc,-38,-38,-38,-38,-38
S,IrreducibleModulesInit,Initialize a Process for calculating all linear representations of a soluble group G for the finite field F,0,2,0,0,0,0,0,0,0,262,,0,0,129,,SolRepProc,-38,-38,-38,-38,-38
S,IrreducibleModulesInit,Initialize a Process for calculating all linear representations of a soluble group G for the finite field F,0,2,0,0,0,0,0,0,0,84,,0,0,129,,SolRepProc,-38,-38,-38,-38,-38
S,NextRepresentation,Return the next representation or false if no further exist,0,1,0,0,0,0,0,0,0,SolRepProc,,36,175,-38,-38,-38,-38
S,NextModule,Return the next representation or false if no further exist,0,1,0,0,0,0,0,0,0,SolRepProc,,36,175,-38,-38,-38,-38
S,AbsolutelyIrreducibleRepresentationProcessDelete,Free all data of the representation Process type,0,1,0,0,1,0,0,1,1,SolRepProc,,-38,-38,-38,-38,-38,-38
S,Representations,"Return a list of absolutely irreducible representations which corresponds to the constituents of the character cc. Each list element is a tuple <D, m>, with D the representation and m the multiplicity of D as constituent of cc. The second argument is a control flag, it is true iff cc equals the sum over D. The group of the character cc must be solvable",0,1,0,0,0,0,0,0,0,39,,168,36,-38,-38,-38,-38
S,Characters,Calculate a list of all irreducible Characters of a soluble Group G (with respect to conditions defined by the optional parameters,0,1,0,0,0,0,0,0,0,129,,168,-38,-38,-38,-38,-38
