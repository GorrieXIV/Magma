174,1
T,SQProc,-,0
A,SQProc,11,Root,SQ,Series,Data,Modi,Limits,ModulCandidates,SplitExt,NonsplitExt,Relat,Collect
S,Initialize,Initialize a SQProc for a finitely presented group F without any information about the relevant primes,0,1,0,0,0,0,0,0,0,121,,SQProc,-38,-38,-38,-38,-38
S,Initialize,Initialize a SQProc for a given quotient epi:F -> G without any information about the relevant primes,0,1,0,0,0,0,0,0,0,175,,SQProc,-38,-38,-38,-38,-38
S,Initialize,Initialize a SQProc for a finitely presented group F with expected order n,0,2,0,0,0,0,0,0,0,148,,0,0,121,,SQProc,-38,-38,-38,-38,-38
S,Initialize,Initialize a SQProc for a given quotient epi:F -> G with expected order n,0,2,0,0,0,0,0,0,0,148,,0,0,175,,SQProc,-38,-38,-38,-38,-38
S,Primes,Calculate the set of relevant primes for SQP,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,AddPrimes,Add the given prime to the set of relevant primes,0,2,0,0,1,0,0,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,AddPrimes,mp is a set of primes which are added to the relevant primes for SQP,0,2,0,0,1,0,0,0,0,83,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,ReplacePrimes,Replace the set of relevant primes in SQP by the given set,0,2,0,0,1,0,0,0,0,83,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,SQ_check,Check the correctness of the soluble quotient,0,1,0,0,0,0,0,0,0,SQProc,,36,-38,-38,-38,-38,-38
S,EquivalentQuotients,"Checks whether two soluble quotients have the same kernel. If not and Construct is true, then a bigger quotient will be constructed, where the kernel is the intersection of both kernels",0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,IntersectKernels,Construct a bigger soluble quotient by intersecting the kernels of the given quotient. The return values are a new soluble quotient process and maps from the new to the given soluble groups,0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,SQProc,175,175,-38,-38,-38
S,ComposeQuotients,"Compose the lifts SQ1 and SQ2 of SQP to a new bigger quotient. If the optional parameter Check is set to true, it will be tested whether the intersection of the kernels has maximal index",0,3,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,SolubleQuotientProcess,Start the soluble quotient algorithm for a finitely presented group F without any information about the relevant primes,0,1,0,0,0,0,0,0,0,121,,SQProc,148,-38,-38,-38,-38
S,SolubleQuotientProcess,Start the soluble quotient algorithm for a finitely presented group F with expected order of the quotient being n,0,2,0,0,0,0,0,0,0,148,,0,0,121,,SQProc,148,-38,-38,-38,-38
S,SolubleQuotientProcess,Start the soluble quotient algorithm for a finitely presented group F with expected order of the quotient being the factorized integer f,0,2,0,0,0,0,0,0,0,149,,0,0,121,,SQProc,148,-38,-38,-38,-38
S,SolubleQuotientProcess,Start the soluble quotient algorithm for a finitely presented group F with relevant primes restricted by the set s,0,2,0,0,0,0,0,0,0,83,,0,0,121,,SQProc,148,-38,-38,-38,-38
S,NonsplitCollector,"Set up the collector for a nonsplit extension of SQP with algebra RG, R the prime ring in characteristic p",0,2,0,0,1,0,0,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,NonsplitCollector,"Set up the collector for a nonsplit extension of SQP with algebra RG, R the prime ring in characteristic p. The pairs in tr indicates trivial tails",0,3,0,0,1,0,0,0,0,82,,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,NonsplitCollector,"Set up the collector for a nonsplit extension of SQP with algebra RG, R the prime ring in characteristic p. The pairs in tr indicates trivial tails. ws defines the weights of a series",0,4,0,0,1,0,0,0,0,82,,0,0,82,,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,NonsplitCollector,"Set up the collector for a nonsplit extension of SQP with algebra RG, R the prime ring in characteristic p. The pairs in tr indicates trivial tails. ws defines the weights of a series. epi is an epimorphism onto another soluble group",0,5,0,0,1,0,0,0,0,175,,0,0,82,,0,0,82,,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,SplitCollector,Set up the collector for a standard split extension of SQP with algebra RG R the prime ring in characteristic p,0,2,0,0,1,0,0,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,SplitCollector,Setup the collector for a standard ssplit extension of SQP with algebra RG R the prime ring in characteristic p. ws defines the weights of a series,0,3,0,0,1,0,0,0,0,82,,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,SplitCollector,"Set up the collector for a nonsplit extension of SQP with algebra RG, R the prime ring in characteristic p. ws defines the weights of a series. epi is an epimorphism onto another soluble group",0,4,0,0,1,0,0,0,0,175,,0,0,82,,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,Modules,"Calculates the G-modules in characteristic p with respect to the given options. The return value is 0 iff no such module exists, otherwise it is the index of the list of modules in SQP",0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,148,-38,-38,-38,-38,-38
S,Modules,Calculates the modules for all (known) relevant primes,0,1,0,0,0,0,0,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,AppendModule,Append/Find the module M in the list of modules in SQP. The first return value is the index of the module in the char p list in SQP. The second return value is false iff the index belongs to an isomophic module. (It might happen that the isomorphism is the identity; relevant is the internal data structure.),0,2,0,0,0,0,0,0,0,303,,0,0,SQProc,,148,36,-38,-38,-38,-38
S,SolutionSpace,internal,0,5,0,0,0,0,0,0,0,36,,0,0,36,,0,0,148,,0,0,148,,0,0,SQProc,,36,148,-38,-38,-38,-38
S,SplitExtensionSpace,"Calculates the split extension lift for the module M. The return is -1 iff the solution space does not exist in general,otherwise it is the Fq-dimension of the space (could be 0)",0,2,0,0,0,0,0,0,0,303,,0,0,SQProc,,148,-38,-38,-38,-38,-38
S,SplitExtensionSpace,"Calculates the split extension lift for the modules in the list. Returned is a sequence of: -1 iff the solution space does not exist in general, otherwise it is the Fq-dimension of the space (could be 0)",0,2,0,0,0,0,0,0,0,168,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,SplitExtensionSpace,"Calculates the split extension lift for the modules in the l-th list in SQP. The return is a sequence of: -1 iff the solution space does not exist in general,otherwise it is the Fq-dimension of the space (could be 0)",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,SplitExtensionSpace,"Calculates the split extension lift for the p-modules stored in SQP. The return is a sequence of: -1 iff the solution space does not exist in general, otherwise it is the Fq-dimension of the space (could be 0)",0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,SplitExtensionSpace,"Calculates the split extension lift for all modules stored in SQP. The return are sequences for each prime of: -1 iff the solution space does not exist in general, otherwise it is the Fq-dimension of the space (could be 0)",0,1,0,0,0,0,0,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,NonsplitExtensionSpace,"Calculates the nonsplit extension lift for the module M. The return is -1 iff the solution space does not exist in general, otherwise it is the Fq-dimension of the space (could be 0)",0,2,0,0,0,0,0,0,0,303,,0,0,SQProc,,148,-38,-38,-38,-38,-38
S,NonsplitExtensionSpace,"Calculates the nonsplit extension lift for the modules in the list. The return is a sequence of: -1 iff the solution space does not exist in general, otherwise it is the Fq-dimension of the space (could be 0)",0,2,0,0,0,0,0,0,0,168,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,NonsplitExtensionSpace,"Calculates the nonsplit extension lift for the modules in the l-th list in SQP. The return is a sequence of: -1 iff the solution space does not exist in general, otherwise it is the Fq-dimension of the space (could be 0)",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,NonsplitExtensionSpace,"Calculates the split extension lift for the p-modules stored in SQP. The return is a sequence of: -1 iff the solution space does not exist in general, otherwise it is the Fq-dimension of the space (could be 0)",0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,NonsplitExtensionSpace,"Calculates the nonsplit extension lift for all modules stored in SQP. The return are sequences for each prime of: -1 iff the solution space does not exist in general, otherwise it is the Fq-dimension of the space (could be 0)",0,1,0,0,0,0,0,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,DeleteSplitSolutionspace,Delete the k-th split solution space of the i-th p-module as the actual solution space,0,4,0,0,1,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,DeleteNonsplitSolutionspace,Delete the k-th split solution space of the i-th p-module as the actual solution space,0,4,0,0,1,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,LiftSplitExtension,Build the split extension of the i-th p-module for the k-th solution space. A set of linear combinations can be specified,0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,SQProc,,SQProc,-38,-38,-38,-38,-38
S,LiftSplitExtension,Build the split extension of the l-th list of p-modules for their actual solution space,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftSplitExtension,Build the split extension of the list of p-modules for their actual solution space,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftSplitExtension,Build the split extension of the list of modules for their actual solution space,0,1,0,0,0,0,0,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftSplitExtensionRow,Build the split extensions of SQP for the p-modules in the l-th list for their actual solution space,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftSplitExtensionRow,Build the split extensions of SQP for the list of p-modules for their actual solution space,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftSplitExtensionRow,Build the split extension of the list of modules for their actual solution space,0,1,0,0,0,0,0,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftNonsplitExtension,Build the non-split extension of the i-th p-module for the k-th solution space. A set of linear combinations can be specified,0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,SQProc,,SQProc,-38,-38,-38,-38,-38
S,LiftNonsplitExtension,Build the non-split extension of the l-th list of p-modules for their actual solution space,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftNonsplitExtension,Build the non-split extension of the list of p-modules for their actual solution space,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftNonsplitExtension,Build the non-split extension of the list of modules for their actual solution space,0,1,0,0,0,0,0,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftNonsplitExtensionRow,Build the non-split extensions of SQP for the p-modules in the l-th list for their actual solution space,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftNonsplitExtensionRow,Build the non-split extensions of SQP for the list of p-modules for their actual solution space,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,LiftNonsplitExtensionRow,Build the non-split extension of the list of modules for their actual solution space,0,1,0,0,0,0,0,0,0,SQProc,,148,SQProc,-38,-38,-38,-38
S,PrintProcess,Print function for SQProc. Print prime specific information,0,2,0,0,1,0,0,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintProcess,General print function for SQProc,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintQuotient,Print function,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintSeries,Print function,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintPrimes,Print function,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintCollector,Print function,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintCollector,Print function,0,2,0,0,1,0,0,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintRelat,Print function,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintModules,Print function,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintModules,Print function,0,2,0,0,1,0,0,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintExtensions,Print function,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,PrintExtensions,Print function,0,2,0,0,1,0,0,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,GetQuotient,Returns the soluble group and the epimorphism from SQP,0,1,0,0,0,0,0,0,0,SQProc,,129,175,-38,-38,-38,-38
S,GetPrimes,Return the relevant primes stored in SQP and a flag indicating the completeness,0,1,0,0,0,0,0,0,0,SQProc,,83,36,-38,-38,-38,-38
S,GetParent,"Returns the parent of SQP, i.e. the soluble Quotient which lifts to SQP",0,1,0,0,0,0,0,0,0,SQProc,,SQProc,-38,-38,-38,-38,-38
S,GetChildren,Returns a list of soluble quotients which are lifts of SQP,0,1,0,0,0,0,0,0,0,SQProc,,168,-38,-38,-38,-38,-38
S,GetChild,Returns the i-th soluble quotient which is a lift of SQP,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,168,-38,-38,-38,-38,-38
S,GetModule,Return the i-th p-module stored in SQP,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SQProc,,103,-38,-38,-38,-38,-38
S,GetModules,Return the list of all p-modules stored in SQP,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,168,-38,-38,-38,-38,-38
S,GetModules,Return the l-th list of p-modules stored in SQP,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SQProc,,168,-38,-38,-38,-38,-38
S,DeleteSplitCollector,Delete the collector for split extensions in characteristic p,0,2,0,0,1,0,0,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,DeleteSplitCollector,Delete all collectors for split extensions,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,DeleteNonsplitCollector,Delete the collector for non-split extensions in characteristic p,0,2,0,0,1,0,0,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,DeleteNonsplitCollector,Delete all collectors for non-split extensions,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,DeleteCollector,Delete the collectors in characteristic p,0,2,0,0,1,0,0,0,0,148,,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,DeleteCollector,Delete all the collectors of SQP,0,1,0,0,1,0,0,0,0,SQProc,,-38,-38,-38,-38,-38,-38
S,DeleteProcess,Delete the soluble quotient process variable,0,1,0,0,1,0,0,1,1,SQProc,,-38,-38,-38,-38,-38,-38
S,DeleteProcessDown,Delete the Process and all its child processes,0,1,0,0,1,0,0,1,1,SQProc,,-38,-38,-38,-38,-38,-38
S,DeleteProcessComplete,Delete all soluble quotient processes which are related to SQP,0,1,0,0,1,0,0,1,1,SQProc,,-38,-38,-38,-38,-38,-38
S,KeepGeneratorOrder,Return the sequence useful for the Collector setup. It determines that the order of the pc generators in SQP is kept unchanged,0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,KeepGeneratorAction,Return the sequence useful for the Collector setup. It determines that the conjugation action of the pc generators in SQP is kept unchanged,0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,KeepElementary,Return the sequence useful for the Collector setup. It determines that the order of the pc generators in SQRSQP is kept unchanged,0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,KeepAbelian,Return the sequence useful for the Collector setup. It determines that the conjugation action of the pc generators in SQR SQP is kept unchanged,0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,KeepGroupAction,Return the sequence useful for the Collector setup. It determines that the conjugation action of the pc generators of SQP on those of SQR SQP is kept unchanged,0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,KeepSplit,Return the sequence useful for the Collector setup. It determines that the presentation of SQP is kept unchanged,0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,KeepElementaryAbelian,Return the sequence useful for the Collector setup. It determines that the order and the conjugation action of the pc generators in SQR SQP is kept unchanged,0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,KeepSplitAbelian,Return the sequence useful for the Collector setup. It determines that the presentation of SQP and the conjugation action in SQR SQP are kept unchanged,0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,KeepSplitElementaryAbelian,Return the sequence useful for the Collector setup. It determines that the presentation of SQP and of SQR SQP are kept unchanged,0,2,0,0,0,0,0,0,0,SQProc,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,KeepPrimePower,"Return a sequence of pairs [j,i] s.t. the order of both G.j and G.i is not p",0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,82,-38,-38,-38,-38,-38
S,KeepPGroupWeights,"Return a sequence of pairs [j,i] correspnding to the weight condition for the p-group. The weights are defined by the sequence of quotients",0,1,0,0,0,0,0,0,0,82,,82,-38,-38,-38,-38,-38
S,IsPureOrder,Check the PC presentation of G for the Hall property,0,1,0,0,0,0,0,0,0,129,,36,148,148,-38,-38,-38
S,AbelianSection,Determine the maximal p-abelian module which lifts to a bigger quotient,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,AbelianSection,"Determine the maximal abelian module which lifts to a bigger quotient. If PrimeCalc equals true, the relevant primes will be calculated first. If ModuleList is 0, only the known modules will be taken into account",0,1,0,0,0,0,0,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,ElementaryAbelianSection,Determine the maxinmal p-elementary abelian module which lifts to a bigger quotient,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,ElementaryAbelianSection,"Determine the maximal elementary abelian module which lifts to a bigger quotient. If PrimeCalc equals true, the relevant primes will be calculated first. If ModuleList is 0, only the known modules will be taken into account",0,1,0,0,0,0,0,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,SplitSection,Determine the maximal p-group with a splitting lift to a bigger quotient,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,SplitSection,"Determine the maximal nilpotent group with a splitting lift to a bigger quotient. If PrimeCalc equals true, the relevant primes will be calculated first. If ModuleList is 0, only the known modules will be taken into account",0,1,0,0,0,0,0,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,SplitAbelianSection,Determine the maximal p-abelian module with a splitting lift to a bigger quotient,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,SplitAbelianSection,"Determine the maximal abelian group with a splitting lift to a bigger quotient. If PrimeCalc equals true, the relevant primes will be calculated first. If ModuleList is 0, only the known modules will be taken into account",0,1,0,0,0,0,0,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,SplitElementaryAbelianSection,Determine the maxinmal p-elementary abelian module with a splitting lift to a bigger quotient,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,SplitElementaryAbelianSection,"Determine the maximal elementary abelian group with a splitting lift to a bigger quotient. If PrimeCalc equals true, the relevant primes will be calculated first. If ModuleList is 0, only the known modules will be taken into account",0,1,0,0,0,0,0,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,NonsplitSection,Determine the maximal p-group with a non splitting lift to a bigger quotient,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,NonsplitSection,"Determine the maximal elementary abelian group with a splitting lift to a bigger quotient. If PrimeCalc equals true, the relevant primes will be calculated first. If ModuleList is 0, only the known modules will be taken into account",0,1,0,0,0,0,0,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,NonsplitAbelianSection,Determine the maximal p-abelian module with a non splitting lift to a bigger quotient,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,NonsplitAbelianSection,"Determine the maximal elementary abelian group with a splitting lift to a bigger quotient. If PrimeCalc equals true, the relevant primes will be calculated first. If ModuleList is 0, only the known modules will be taken into account",0,1,0,0,0,0,0,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,NonsplitElementaryAbelianSection,Determine the maximal p-elementary abelian module with a splitting lift to a bigger quotient,0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,NonsplitElementaryAbelianSection,"Determine the maximal elementary abelian group with a nonsplitting lift to a bigger quotient. If PrimeCalc equals true, the relevant primes will be calculated first. If ModuleList is 0, only the known modules will be taken into account",0,1,0,0,0,0,0,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,PGroupSection,"Determine a lift with a p-group, given by its lower central series",0,2,0,0,0,0,0,0,0,148,,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,NilpotentSection,"Determine the maximal nilpotent group with a lift to a bigger quotient. If PrimeCalc equals true, the relevant primes will be calculated first. If ModuleList is 0, only the known modules will be taken into account. Steps puts a limit on the weights of the p-groups of the nilpotent group",0,1,0,0,0,0,0,0,0,SQProc,,36,SQProc,-38,-38,-38,-38
S,SolubleQuotient,"Compute a soluble quotient of F. S is a sequence of tuples <p, e>, with p a prime or 0 and e a non-negative integer. The order of the quotient will be a divisor of &* [ p^e : <p, e> in S] if all p's and e's are positive. See handbook for further details",0,1,0,0,0,0,0,0,0,121,,129,175,82,298,-38,-38
S,SolubleQuotient,"Compute a soluble quotient of F. S is a sequence of tuples <p, e>, with p a prime or 0 and e a non-negative integer. The order of the quotient will be a divisor of &* [ p^e : <p, e> in S] if all p's and e's are positive. See handbook for further details",0,2,0,0,0,0,0,0,0,148,,0,0,121,,129,175,82,298,-38,-38
S,SolubleQuotient,"Compute a soluble quotient of F. S is a sequence of tuples <p, e>, with p a prime or 0 and e a non-negative integer. The order of the quotient will be a divisor of &* [ p^e : <p, e> in S] if all p's and e's are positive. See handbook for further details",0,2,0,0,0,0,0,0,0,83,,0,0,121,,129,175,82,298,-38,-38
