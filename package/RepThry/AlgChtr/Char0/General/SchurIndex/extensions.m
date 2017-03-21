freeze;

import "cyclo_gal.m": CycloGal_p, CycloGalStabilizer, CycloGalIndex;

schur_index_extn := function(chi, loc, extn: real := 0)
    if #loc eq 0 then return 1; end if;
    if #extn eq 0 then return LCM([t[2]:t in loc]); end if;
    N := CyclotomicOrder(Universe(extn));
    if N le 2 then return LCM([t[2]:t in loc]); end if;
    N := LCM(N, CyclotomicOrder(Universe(Eltseq(chi))));
    res := 1;
    real_easy := not (real cmpeq 0);
    if real_easy then
	if loc[1,1] eq 0 then
	    if real then res := loc[1,2]; end if;
	end if;
    end if;
    for i := #loc to 1 by -1 do
	if res mod loc[i,2] eq 0 then continue; end if;
	p := loc[i,1];
	m := loc[i,2];
	if p ne 0 then
	    Gamma := CycloGal_p(p, N);
	    Gam_sub := CycloGalStabilizer(Gamma, chi);
	    Gam_sub_2 := CycloGalStabilizer(Gam_sub, extn);
	    m := m div GCD(m, CycloGalIndex(Gam_sub, Gam_sub_2));
	    res := LCM(res, m);
	elif not real_easy then
	    is_real := forall{v:v in extn|v eq ComplexConjugate(v)};
	    if is_real then
		res := LCM(res, m);
	    end if;
	end if;
    end for;
    return res;
end function;
