AlgGen
{
	chbasis.m
	general.m
}

AlgAss
{
	algebras.m
	degraaf.m
	enum.m
	general.m
	ideals.m
	ideals-jv.m
	order-jv.m
	debug.m
	orders.m
}

AlgFP
{
	action.m
	rosenmann.m
	misc.m
}

AlgLie
{
	AlgCarTyp.m
	Melikian.m
	abelian.m
	attrib.m
	cartan.m
	center.m
	chevbas.m
	conrep.m
	derlie.m
	diagram_auts.m
	dirdec.m
	fplie.m
	freudenthal.m
	isom.m
	levi.m
	modrep.m
	module.m
	morphism.m
	nilporb.m
	nilrad.m
	nonnilp.m
	plesken.m
	plie.m
	quo_with_pullback.m
        rest_mat.m
	rootsystem.m
	semsimalg.m
	slac.m
	sssdb.m
	stsa-char2.m
	stsa-char3.m
	stsa.m
	toral.m
	twisted.m
	type.m

	ChevBas
	{
		diag.m
		cartints.m
		identify_roots.m
		chevbasdata.m
		chevbasmain.m
		chevbasis_A2SC_char3.m
		chevbasis_G2_char3.m
		chevbasis_A1_char2.m
		chevbasis_B2SC_char2.m
		chevbasis_Bn_char2.m
		chevbasis_Cn_char2.m
		chevbasis_Dn_nonAd_nonSC_char2.m
		chevbasis_F4_char2.m
		chevbasis_G2_char2.m
		findframemain.m	
		findframe_A3_char2.m
		findframe_BnAd_char2.m
		findframe_BnSC_char2.m
		findframe_CnAd_char2.m
		findframe_CnSC_char2.m
		findframe_DnSC_char2.m
		findframe_F4_char2.m
		findframe.m
		distort.m
		chevbas.m
		verifychevbas.m
		
		liealg_aut.m
		
		identify.m
		identify_liealg_of_simp_grp.m
		identify_simple_liealg.m
		identify_twisted.m
	}
	
	AlgLieExtr
	{
		f_stuff.m
		extremal-wdg.m
		basic.m
		f_proof.m
		take_out.m
	}
	
	NilpOrbAlgLie
	{
		hackobj.m
	}
	
	KacMoody
	{
		cartan.m
		basic.m
	}
	
	SubSU
	{
		IrredSimple_lib.m
		print.m
	}

}

AlgQuat
{
	algebras.m
	ideals.m
	isomorphisms.m
	representations.m
	embed.m
	enumerate.m
	hilbert.m
	interface.m
	maxorder.m
        predicates.m
	ramified.m
	ringclassfield.m
	units.m
	twosided.m
}

AlgQEA	
{  
	gauss.m
	weyl.m
	qea.m
	module.m
	autom.m
	canbas.m
	hopf.m
	paths.m
}

AlgMatLie
{
	wrappers.m
}

AlgMat
{
	General
	{
		diag.m
		log.m
		unipotent.m
		unitgroup.m
	}

	# Use new code for now:
	#MatPres
	MatPres/new
	{
		big.m
		diag.m
		matfunc.m
		mattr.m
		meataxe.m
		ncond.m
		presentation.m
		radical.m
		rand.m
		relations.m
		semisimple.m
		show.m
		word.m
	}
}

ModAlg
{
	generalfuncs.m
}

AlgStar
{
	+star.spec
}
