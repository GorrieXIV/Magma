freeze;

/* This file contains functions for manipulating deterministic finite state
 * automata.
 * Unfortunately there is more than one definition of this:
 * In the complete model, all state/alphabet transitions must be defined,
 * and in the partial model they are allowed to be undefined.
 * The partial model is more convenient for computation and agrees with
 * existing concepts such as coset tables, so we use that.
 * One slightly unfortunate consequence is that the minimal automaton with
 * empty language has no states, so we need to allow 0 or 1 initial states.
 *
 * Most of the information is in the "transitions" component of the record.
 * This is a list of lists, with each sublist of length the alphabet size,
 * and transitions[i][j] is the target of the transition from alphabet
 * number j on state number i. A value of 0 means that this is undefined.
 *
 * The "states" and "alphabet" components need not be used. They are there
 * to identify what the  states and alphabet correspond to - for example,
 * members of the alphabet might be generators of a group.
 *
 * There should probably be other components to record things like whether
 * the fsa is known to minimal.
 *
 * Many of the functions here, such as minimization, would ideally be
 * put into C.
 */

declare verbose DFA, 1;

declare type DFA;

declare attributes DFA:
      initial,  //must have size 0 or 1 - usually 1.
      final,
      transitions,
      alphabetsize, //we need that only for case of no states
      alphabet,
      states,
      growthfunction,
      standard,
      minimal;

intrinsic Print(M::DFA, level::MonStgElt)
{}
    if level eq "Magma" then
	printf "BuildDFA(%m, %m, %m, %m",
	    M`initial, M`final, M`transitions, AlphabetSize(M);
	noptional := 0;
	if assigned M`alphabet then
	    printf "%o ", noptional eq 0 select ":" else ",";
	    printf "Alphabet := %m", M`alphabet;
	    noptional +:= 1;
	end if;
	if assigned M`states then
	    printf "%o ", noptional eq 0 select ":" else ",";
	    printf "States := %m", M`states;
	    noptional +:= 1;
	end if;
	if assigned M`standard then
	    printf "%o ", noptional eq 0 select ":" else ",";
	    printf "Standard := %m", M`standard;
	    noptional +:= 1;
	end if;
	if assigned M`minimal
	then
	    printf "%o ", noptional eq 0 select ":" else ",";
	    printf "Minimal := %m", M`minimal;
	    noptional +:= 1;
	end if;
	if assigned M`growthfunction
	then
	    printf "%o ", noptional eq 0 select ":" else ",";
	    printf "GrowthFunction := %m",
		<Eltseq(Numerator(gf)), Eltseq(Denominator(gf))>
		where gf := M`growthfunction;
	    noptional +:= 1;
	end if;
	printf ")";
	return;
    end if;

    printf "DFA";
    if level eq "Minimal" then return; end if;
    printf " with %o states and alphabet size %o", Nstates(M), AlphabetSize(M);
    return;

end intrinsic;

intrinsic Nstates(M::DFA) -> RngIntElt
{The number of states of M}
    return #M`transitions;
end intrinsic;

intrinsic AlphabetSize(M::DFA) -> RngIntElt
{The number of states of M}
    if not assigned M`alphabetsize then
	M`alphabetsize := #(M`transitions[1]);
    end if;
    return M`alphabetsize;
end intrinsic;

intrinsic TransitionTable(M::DFA) -> SeqEnum
{The transition table of the DFA M}
    return M`transitions;
end intrinsic;

intrinsic InitialStates(M::DFA) -> SeqEnum
{The initial states of the DFA M}
    if assigned M`States then
	return {M`States[i] : i in M`initial};
    else
	return M`initial;
    end if;
end intrinsic;

intrinsic FinalStates(M::DFA) -> SeqEnum
{The final states of the DFA M}
    if assigned M`States then
	return {M`States[i] : i in M`final};
    else
	return M`final;
    end if;
end intrinsic;

intrinsic BuildDFA(I::SetEnum[RngIntElt], F::SetEnum[RngIntElt],
T::SeqEnum[SeqEnum[RngIntElt]], S::RngIntElt : 
Alphabet := 0, States := 0, Standard := 0, Minimal := 0, GrowthFunction := 0)
    -> DFA
{Make a DFA with intial states I, final states F, transition table T and
alphabet size S}
    require #T eq 0 or #T[1] eq S or S eq -1 : "Incorrect alphabet size";
    res := New(DFA);
    if #T eq 0 then
	res`alphabetsize := S;
    else
	res`alphabetsize := #T[1];
	S := res`alphabetsize;
    end if;
    require #I le 1 and I subset {1..S}: "Incorrect initial set";
    res`initial := I;
    require F subset {1..S}: "Incorrect final set";
    res`final := F;
    SS := {0..S};
    require forall{x: x in T | Seqset(x) subset SS} : "Incorrect transitions";
    res`transitions := T;
    if not (Alphabet cmpeq 0) then
	res`alphabet := Alphabet;
    end if;
    if not (States cmpeq 0) then
	res`states := States;
    end if;
    if not (Standard cmpeq 0) then
	res`standard := Standard;
    end if;
    if not (Minimal cmpeq 0) then
	res`minimal := Minimal;
    end if;
    if not (GrowthFunction cmpeq 0) then
	P := PolynomialRing(Integers());
	res`growthfunction := P!gf[1]/P!gf[2]
	    where gf := GrowthFunction;
    end if;
    return res;
end intrinsic;

intrinsic IsAcceptedWord(dfa::DFA, w::SeqEnum) -> BoolElt
{Is word w in language of dfa?}
  local tab, st;
  if #dfa`initial eq 0 then
    return false;
  end if; 
  tab := dfa`transitions;
  st := Representative(dfa`initial);
  for x in w do
    st := tab[st][x];
    if st eq 0 then return false; end if;
  end for;
  return st in dfa`final;
end intrinsic;

intrinsic Minimize(dfa::DFA) -> DFA
{Return DFA with minimal number of states with same language as dfa}
  //i.e. compute dfa with same language and minimal number of states
  assert #dfa`initial le 1; 
  if assigned dfa`minimal and dfa`minimal then
    return dfa;
  end if;
  tab := dfa`transitions;
  ns := #tab;
  ans := New(DFA);
  ans`alphabetsize := AlphabetSize(dfa);
  if assigned dfa`alphabet then ans`alphabet := dfa`alphabet; end if;
  if #dfa`initial eq 0 then
    ans`initial:={}; ans`final:={}; ans`transitions:=[];
    ans`minimal := true;
    dfa`minimal := Nstates(dfa) eq 0;
    return ans;
  end if; 
  init := Representative(dfa`initial);
  //it is more convenient to make failure state a new state in this function.
  ns +:= 1;
  ng := AlphabetSize(dfa);
  Append(~tab,[0 : i in [1..ng]]);
  for s in [1..ns] do for g in [1..ng] do
    if tab[s][g] eq 0 then tab[s][g]:=ns; end if;
  end for; end for;
  final := [ false: i in [1..ns]];
  for s in dfa`final do final[s] := true; end for; 
  //need to determine which states are accessible
  acc := [false: i in [1..ns]];
  queue := [init];
  ct := 0;
  while ct lt #queue do
    ct +:= 1;
    st := queue[ct];
    acc[st] := true;
    for i in [1..ng] do if not acc[ tab[st][i] ] then
      acc[ tab[st][i] ] := true;
      Append(~queue, tab[st][i]);
    end if; end for;
  end while;
  acc[ns] := true; //convenient

  if not exists{s : s in [1..ns] | acc[s] and final[s] } then //empty language
    ans`initial:={}; ans`final:={}; ans`transitions:=[];
    ans`minimal := true;
    dfa`minimal := Nstates(dfa) eq 0;
    return ans;
  end if;
  stclno := [ acc[s] and final[s] select 1 else 2 : s in [1..ns] ];
  ncs := 2;
  iters := 0;
  repeat
    lookup := {@ @};
    iters +:= 1;
    oldncs := ncs; ncs := 0;
    clid := [];
    nstclno := [];
    for s in [1..ns] do if acc[s] then //not interested in inaccessible states
      clid := [stclno[row[g]]:g in [1..ng]] where row := tab[s];
      clid[ng+1] := stclno[s];
      p := Index(lookup, clid);
      if p eq 0 then
        Include(~lookup, clid);
        ncs +:= 1;
        p := ncs;
      end if;
      nstclno[s] := p;
    end if; end for;
    stclno := nstclno;
  until ncs eq oldncs;
  newtab := [x:x in lookup];
  delete lookup;
  fs := stclno[ns];
  for s in [1..ncs] do if acc[s] then
      row := Prune(newtab[s]);
      for g in [1..ng] do
        if row[g] eq fs then row[g] := 0;
        elif row[g] gt fs then row[g] -:= 1;
        end if;
      end for;
      newtab[s] := row;
  end if; end for;
  for s in [1..ns] do if acc[s] then
     if stclno[s] gt fs then stclno[s] -:= 1; end if;
  end if; end for;
  newtab := [newtab[i] : i in [1..fs-1]] cat [newtab[i] : i in [fs+1..ncs]];
  vprintf DFA, 1: "%o iterations", iters;
  if #newtab eq Nstates(dfa) then
    dfa`minimal := true;
    return dfa;
  end if;
  ans`transitions := newtab;
  ans`initial := {stclno[init]};
  ans`final := {stclno[s]: s in dfa`final | acc[s]};
  ans`minimal := true;
  dfa`minimal := Nstates(dfa) eq Nstates(ans);
  return ans;
end intrinsic;

intrinsic StandardForm(dfa::DFA) -> DFA
{Return DFA in standard form with same number of states and same language as
dfa. Standard form means that the initial state is number 1, and the states
appear in increasing order in the transition table}
  local tab, ns, ng, ans, perm, ct, st, im, newtab;
  assert #dfa`initial le 1;
  if assigned dfa`standard and dfa`standard then
    return dfa;
  end if;
  tab := dfa`transitions;
  ns := #tab;
  ans := New(DFA);
  ng := AlphabetSize(dfa);
  ans`alphabetsize := ng;
  if assigned dfa`alphabet then ans`alphabet := dfa`alphabet; end if;
  if #dfa`initial eq 0 then
    ans`initial:={}; ans`final:={}; ans`transitions:=[];
    ans`standard := true;
    return ans;
  end if; 
  perm := {@ Representative(dfa`initial) @};
  ct := 0;
  repeat
    ct +:= 1;
    st := perm[ct];
    for g in [1..ng] do
      im := tab[st][g];
      if im ne 0 and not im in perm then
        Include(~perm, im);
        if #perm eq ns then break; end if;
      end if;
    end for;
  until #perm eq ns;
  //now renumber everything - first invert state permutation
  if forall{i: i in [1..ns] | perm[i] eq i} then
    dfa`standard := true;
    return dfa;
  else
    dfa`standard := false;
  end if;
  perm := Eltseq( (Sym(ns)!perm)^-1 );
  ans`initial := { 1 };
  ans`final := { perm[t] : t in dfa`final };
  newtab := tab;
  for s in [1..ns] do
    st := perm[s];
    for g in [1..ng] do
      im := tab[s][g];
      newtab[st][g] := im eq 0 select 0 else perm[im];
    end for; 
  end for;
  ans`transitions := newtab;
  ans`standard := true;
  return ans;
end intrinsic;

intrinsic Equal(dfa1::DFA, dfa2::DFA) -> BoolElt
{Are the languages of dfa1 and dfa2 equal?}
  local m1, m2;
  assert #dfa1`initial le 1;
  assert #dfa2`initial le 1;
  assert AlphabetSize(dfa1) eq AlphabetSize(dfa2);
  m1 := StandardForm(Minimize(dfa1));
  m2 := StandardForm(Minimize(dfa2));
  return m1`final eq m2`final and m1`transitions eq m2`transitions;
end intrinsic;

intrinsic 'eq'(dfa1::DFA, dfa2::DFA) -> BoolElt
{Are the languages of dfa1 and dfa2 equal?}
    return Equal(dfa1, dfa2);
end intrinsic;

intrinsic Language(dfa::DFA, min::RngIntElt, max::RngIntElt :
                      words := false) -> SetEnum
{Set of words in language of dfa with lengths from min to max. If word is true
then members of dfa`alphabet should be group elements, and language is returned
as group elements. Otherwise returned as integer lists.}
  local alph, tab, init, acc, ng, lang, cword, elt, done, backtrack, cstate, i,
        clength, fe;
  assert #dfa`initial le 1;
  if words then
    assert assigned dfa`alphabet and #dfa`alphabet eq AlphabetSize(dfa);
    alph := dfa`alphabet;
  end if;
  tab := dfa`transitions;
  if #dfa`initial eq 0 then
    return {};
  end if;
  init := Representative(dfa`initial);
  acc := dfa`final;
  ng := AlphabetSize(dfa);
  lang := {};
  // cword will be the current word in the search (as list of integers)
  // clength its current length, and cstatelist the list of states of dfa
  // arising when scanning the word.
  cword := [Integers()|];
  cstatelist := [init];
  clength := 0;
  done := false;
  while not done do
  // first check if we want the current word.
     if clength ge min and cstatelist[clength+1] in acc then
       if words then
         elt := cword eq [] select alph[1]^0 else &*[alph[w] : w in cword]; 
         Include(~lang, elt);
       else 
         Include(~lang, cword);
       end if;
     end if;
  // now proceed to next word in search.
     fe := 1;
     backtrack:=true;
     while backtrack and not done  do
       if clength lt max then
         cstate := cstatelist[clength+1];
         i := fe;
         while backtrack and i le ng do
           if tab[cstate][i] gt 0 then
           // found next node
             clength +:= 1;
             cword[clength] := i;
             cstatelist[clength+1] := tab[cstate][i];
             backtrack := false;
           end if;
           i +:= 1;
         end while;
       end if;
       if backtrack then
         if clength eq 0 then
           done := true;
         else
           fe := cword[clength]+1;
           Prune(~cword);
           clength -:= 1;
         end if;
       end if;
     end while;
  end while;
  return lang;
end intrinsic;

intrinsic WordCount(dfa::DFA, len::RngIntElt) -> SeqEnum
{returns list l of length len+1 where l[i] is number of words of length i-1
in the language of dfa}
  local sct, nsct, lct, tab, ns, ng, n, row; 
  assert #dfa`initial le 1;
  tab := dfa`transitions;
  ns := #tab;
  if #dfa`initial eq 0 then
    return [ 0 : i in [1..len+1] ];
  end if;
  init := Representative(dfa`initial);
  return LanguageCountInternal(init, dfa`transitions, dfa`final, len);
end intrinsic;

intrinsic GrowthFunction(dfa::DFA) -> FldFunRatUElt
{The growth function of the given DFA}

  local tab, ns, ds, lct, F, prod, vecs, vec, M, sol,
        den, num, dd, dn, p, isc, N; 
  if assigned dfa`growthfunction then
    return dfa`growthfunction;
  end if;
  require #dfa`initial le 1: "Number of initial states must be at most 1";
  tab := dfa`transitions;
  ns := #tab;
  F := FunctionField(Integers());
  if #dfa`initial eq 0 then
    gf := F!0;
    dfa`growthfunction := gf;
    return gf;
  end if;
  x := F.1;
  lct := WordCount(dfa, 2*ns-1);
  if forall{i:i in [ns+1..2*ns] | IsZero(lct[i])} then
    /* finite language */
    gf := &+[lct[i]*x^(i-1):i in [1..ns]];
    dfa`growthfunction := gf;
    return gf;
  end if;
  //set up
  //system of equations to solve for recursion between elements of lct.
  //numerator of growth function has degree at most ns-1,
  //denominator has degree at most ns
  //We first solve modulo a prime, to estimate the degree of the denominator
  p := 32717;
  M := CyclicShiftsMatrix(GF(p), ns, ns, lct);
  vprint DFA, 1: "Have matrix over prime field";
  vec := -Vector(GF(p), lct[ns+1..2*ns]);
  isc, sol, N := IsConsistent(M, vec);
  assert isc;
  ReduceVector(N, ~sol);

  assert not IsZero(sol); //because we've taken out the finite language case

  ds := Depth(sol);
  dd := Max( ns-ds+1, 1); //upper bound on denominator
  P := PolynomialRing(GF(p));
  z := P.1;
  den := 1 + z*P!Reverse(Eltseq(sol));
  assert Degree(den) eq dd;
  num := den * P!lct[1..ns];
  num := P!Eltseq(num)[1..ns];
  dn := Degree(num);
  assert dn lt ns;
  dn := Max(dn, dd-1);
  vprintf DFA, 1:
     "Have solution mod prime. Degrees: %o/%o\n", dn, dd;
  // dd is likely to be correct. We also use dd as initial numerator
  // estimate, but that may be wrong. Numerator can have degree at most ns-1.
  // billu added code to estimate degree of numerator (after a couple of
  // bad experiences). dn is this estimate.
  repeat 
    M := CyclicShiftsMatrix(dd, dd, lct[dn-dd+2..dn+dd]);
    vprint DFA, 1: "Have matrix over integers";
    vec := -Vector(Integers(), lct[dn+2..dn+dd+1]);
    isc, sol, N := IsConsistent(M, vec);
    if isc then
      ReduceVector(N, ~sol);
      //solution is very unlikely to be incorrect, but we should check!
      for i in [dn+3..ns] do
        vec := Vector(Integers(), lct[i..i+dd-1]);
        if InnerProduct(vec,sol) ne -lct[i+dd] then
          vprint DFA, 1:
                     "Unexpected inconsistency - but no cause for concern!";
          isc := false;
          break;
        end if;
      end for;
    end if;
    if isc then
      vprint DFA, 1: "Have solution over integers";
    else vprint DFA, 1: "No solution - increasing degree estimates";
      dd := Min(dd+1, ns);
      dn := Min(dn+10, ns-1);
    end if;
  until isc;
   //We are relying on fact that we have a solution with as many leading
   //0's as possible.
  P := PolynomialRing(Integers());
  z := P.1;
  den := 1 + z*P!Reverse(Eltseq(sol));
  num := den * P!lct[1..ns];
  num := P!Eltseq(num)[1..ns];
  gf := (F!num)/(F!den);
  dfa`growthfunction := gf;
  return gf;
end intrinsic;

intrinsic Size(dfa::DFA) -> RngIntElt
{return size of language of dfa - could be infinity}
  assert #dfa`initial le 1;
  f := GrowthFunction(dfa);
  if Degree(Denominator(f)) gt 0 then
    return Infinity();
  end if;
  return &+Eltseq(Numerator(f));
end intrinsic;

intrinsic Complement(dfa::DFA) -> DFA
{Return DFA whose language is complement of dfa}
 local ans, ns, ng, tab, init, final, acc, queue, ct, st, iters,
        newfinal, newinit, ctab, oldncs, ncs, p, fs;
  assert #dfa`initial le 1;
  tab := dfa`transitions;
  ns := #tab;
  ans := New(DFA);
  ans`alphabetsize := AlphabetSize(dfa);
  if assigned dfa`alphabet then ans`alphabet := dfa`alphabet; end if;
  ng := AlphabetSize(dfa);
  if #dfa`initial eq 0 then
    ans`initial:={1}; ans`final:={1};
    ans`transitions:=[ 1 : i in [1..ng] ];
    return ans;
  end if;
  init := Representative(dfa`initial);
  //it is convenient to make failure state a new state in this function.
  ns +:= 1;
  Append(~tab,[0 : i in [1..ng]]);
  for s in [1..ns] do for g in [1..ng] do
    if tab[s][g] eq 0 then tab[s][g]:=ns; end if;
  end for; end for;
  //now just take complement of final states
  ans`transitions := tab;
  ans`initial := {init};
  ans`final := {1..ns} diff dfa`final;
  if assigned dfa`growthfunction then
    f := dfa`growthfunction;
    P := Parent(f);
    ans`growthfunction := 1/(1-ng*P.1) - f;
  end if;
  return ans;
end intrinsic;

ProdTable := function( dfa1, dfa2 )
//compute dfa of ordered pairs of states from dfa1, dfa2.
//Will be used to construct meet and join of dfa1, dfa2.
//the dfa returned will have no `final component.
//Assume they have initial states. 
  local init1, init2, tab1, tab2, ans, states, ct, ng, st, tab, row, im, p;
  init1 := Representative(dfa1`initial);
  init2 := Representative(dfa2`initial);
  tab1 := dfa1`transitions;
  tab2 := dfa2`transitions;
  ans := New(DFA);
  ans`alphabetsize := AlphabetSize(dfa1);
  ans`initial := {1};
  states := {@ <init1,init2> @};
  ng := AlphabetSize(dfa1);
  ct := 0;
  tab := [];
  while ct lt #states do
    ct +:= 1;
    st := states[ct];
    row := [];
    for g in [1..ng] do
      im := < st[1] eq 0 select 0 else tab1[st[1]][g],
              st[2] eq 0 select 0 else tab2[st[2]][g] >;
      if im[1] eq 0 and im[2] eq 0 then
        p := 0;
      else
        p := Position(states, im);
        if p eq 0 then
          Include(~states, im);
          p := #states;
        end if;
      end if;
      Append(~row, p);
    end for;
    Append(~tab, row);
  end while;
  ans`states := SetToSequence(states);
  ans`transitions := tab;
  return ans;
end function;

intrinsic Meet(dfa1::DFA, dfa2::DFA) -> DFA
{Return DFA whose language is intersection of languages of dfa1 and dfa2}
  local ans, prod, states;
  assert #dfa1`initial le 1;
  assert #dfa2`initial le 1;
  assert AlphabetSize(dfa1) eq AlphabetSize(dfa2);
  ans := New(DFA);
  ans`alphabetsize := AlphabetSize(dfa1);
  if assigned dfa1`alphabet then ans`alphabet := dfa1`alphabet;
  elif assigned dfa2`alphabet then ans`alphabet := dfa2`alphabet;
  end if;
  if #dfa1`initial eq 0 or #dfa2`initial eq 0 then
    ans`initial:={}; ans`final:={}; ans`transitions:=[];
    return ans;
  end if;
  prod := ProdTable(dfa1,dfa2);
  ans`transitions := prod`transitions;
  states := prod`states;
  ans`initial := {1};
  ans`final := {};
  for s in [1..#states] do
    if states[s][1] in dfa1`final and states[s][2] in dfa2`final then
      Include(~ans`final, s);
    end if;
  end for;
  return ans;
end intrinsic;

intrinsic Join(dfa1::DFA, dfa2::DFA) -> DFA
{Return DFA whose language is union of languages of dfa1 and dfa2}
  local ans, prod, states;
  assert #dfa1`initial le 1;
  assert #dfa2`initial le 1;
  assert AlphabetSize(dfa1) eq AlphabetSize(dfa2);
  ans := New(DFA);
  ans`alphabetsize := AlphabetSize(dfa1);
  if assigned dfa1`alphabet then ans`alphabet := dfa1`alphabet;
  elif assigned dfa2`alphabet then ans`alphabet := dfa2`alphabet;
  end if;
  if #dfa1`initial eq 0 then return dfa2;
  elif #dfa2`initial eq 0 then return dfa1;
  end if;
  prod := ProdTable(dfa1,dfa2);
  ans`transitions := prod`transitions;
  states := prod`states;
  ans`initial := {1};
  ans`final := {};
  for s in [1..#states] do
    if states[s][1] in dfa1`final or states[s][2] in dfa2`final then
      Include(~ans`final, s);
    end if;
  end for;
  return ans;
end intrinsic;

intrinsic WordAcceptor(G::GrpAtc) -> DFA
{The record describing the word acceptor of the automatic group G}
    table := WordAcceptorTable(G);
    assert #table gt 0;
    ans := New(DFA);
    ans`initial		:= {1};
    ans`final		:= {1..#table};
    ans`alphabetsize 	:= #table[1];
    ans`transitions	:=  table;
    return ans;
end intrinsic;

intrinsic WordDifferenceAutomaton(G::GrpAtc) -> DFA
{The record describing the word difference automaton of the automatic group G}
    table := WordDifferenceTable(G);
    assert #table gt 0;
    ans := New(DFA);
    ans`initial		:= {1};
    ans`final		:= {1..#table};
    ans`alphabetsize 	:= #table[1];
    ans`transitions	:=  table;
    return ans;
end intrinsic;

intrinsic WordAcceptor(G::GrpFPCox) -> DFA
{The record describing the Brink-Howlett shortlex word acceptor of the coxeter group G}
    table := [];
    a := Ngens(G);
    act := ReflectionTable(G);
    a := #act;
    ss := {@ {Integers()|} @};
    position := 1;
    repeat
	x := ss[position];
	table[position] := [0:i in [1..a]];
	for i := 1 to a do
	    if i notin x then
		target := {y : r in (x join {1..i-1}) | y ne 0 where y := act[i][r]};
		Include(~target, i);
		targetpos := Index(ss, target);
		if targetpos eq 0 then
		    Include(~ss, target);
		    table[position][i] := #ss;
		else
		    table[position][i] := targetpos;
		end if;
	    end if;
	end for;
	position +:= 1;
    until position gt #ss;
    assert #table eq #ss;
    ans := New(DFA);
    ans`initial		:= {1};
    ans`final		:= {1..#table};
    ans`alphabetsize 	:= a;
    ans`transitions	:=  table;
    return ans;
end intrinsic;

intrinsic GrowthFunction(G::GrpAtc:Primes := []) -> FldFunRatUElt
{The growth of G as a rational function over Z.}
    return GrowthFunction(WordAcceptor(G));
end intrinsic;
