freeze;

// ----------------------------------------------------------------------------
// The mis-named small groups database access package.
// 
//	Written by Bill Unger (modified an older version without attributions),
//		Bruce Cox, and with additions and fixes by Volker Gebhardt.
//
// This package contains functions to access the small groups database.
// Set up necessary variables

intrinsic IsInSmallGroupDatabase(o::RngIntElt) -> BoolElt
{Return true iff the small groups database contains the groups of order o}
 requirege o, 1;
 if (o eq 1024) then
    return false;
 end if;
 if (o le 2000  or  o eq 5^5  or o eq 7^4 or o eq 3^8) then
    return true;
 end if;
 f := Factorisation(o);
 if forall{i : i in [1..#f] | f[i,2] eq 1 and f[i,1] lt 2^30} then
    return true;  // square-free order
 end if;
 if (#f eq 2  and  exists(i){i : i in [1,2] | f[i][2] eq 1}) then
    p := f[3-i]; // the other prime power...
    if ( p[2] le 2
	 or p[1] eq 2  and  p[2] le 8
         or p[1] eq 3  and  p[2] le 6
         or p[1] eq 5  and  p[2] le 5
         or p[1] eq 7  and  p[2] le 4 ) then
       return true;  // q^n*p for a  q^n | 2^8, 3^6, 5^5 or 7^4  and  p ne q
    end if;
 end if;
 if (#f eq 1 and f[1,2] le 7) then return true; end if;
 return false;
end intrinsic;


intrinsic IsInSmallGroupDatabase(D::DB, o::RngIntElt) -> BoolElt
{Return true iff D contains the groups of order o}
 requirege o, 1;
 return IsInSmallGroupDatabase(o);
end intrinsic;

intrinsic CanIdentifyGroup(o::RngIntElt) -> BoolElt
{Return true iff groups of order o can be identified in the small groups database}
 requirege o, 1;
 db := SmallGroup2Database();
 res := CanIdentifyGroup(db, o);
 delete db;
 return res;
end intrinsic;

function IsSolvableOrder(o)
 f := Factorisation(o);
 if (#f le 1) then
    return true; // trivial group and p-groups
 end if;
 if (#f eq 2  and (f[1][2] eq 1  or  f[2][2] eq 1)) then
    return true; // p^n*q
 end if;
 if (#f eq 3  and f[1][2] eq 1  and  f[2][2] eq 1  and  f[3][1] eq 1) then
    return true; // p*q*r
 end if;
 return false;
end function;


_sg_check_order := procedure(o)
    error if (o le 0),
	"Order must be positive";
    error if (not IsInSmallGroupDatabase(o)),
	"The groups of order", o,
	" are not contained in the small groups database";
end procedure;


_sg_warn_lots := procedure(Number, Warning)
    if (Number gt 100000) and (Warning) then
	printf "Warning:  May return more than 100,000 groups -- this " cat
	       "will take a VERY long time.  " cat
	       "Would a SmallGroupProcess be more appropriate?\n";
    elif (Number gt 10000) and (Warning) then
	printf "Warning: May return more than 10,000 groups -- " cat
	       "perhaps a SmallGroupProcess would be more appropriate?\n";
	printf "\n(To turn off this message, use Warning := false)\n";
    elif (Number gt 1000) and (Warning) then
	printf "Warning: May return more than 1,000 groups -- " cat
	       "this might take a while.\n";
	printf "\n(To turn off this message, use Warning := false)\n";
    end if;
end procedure;


_sg_string_to_tf := function(Search)
    Matched, Dummy, L := 
        Regexp("^(([Nn][Oo][Nn]|[Ii][Nn])?.?" cat 
	       "([Ss][Oo][Ll][Vv][Aa][Bb][Ll][Ee]" cat "|" cat 
	        "[Ss][Oo][Ll][Uu][Bb][Ll][Ee])|[Aa][Ll][Ll])", Search);
    if Matched then
        if Regexp("^[Aa][Ll][Ll]", L[1]) then
            return true, true;
        end if;
        if Regexp("^([Ss][Oo][Ll][Vv][Aa][Bb][Ll][Ee]" cat "|" cat 
		  "[Ss][Oo][Ll][Uu][Bb][Ll][Ee])", L[1]) then
            return true, false;
        end if;
        if Regexp("^[Nn][Oo][Nn]", L[2]) then
            return false, true;
        end if;
        if Regexp("^[Ii][Nn]", L[2]) then
            return false, true;
        end if;
        return false, false;
    else
        printf "Error: Parameter \"Search\" must be either " cat
	       "\"%o\", \"%o\" (or \"%o\") or \"%o\" (or \"%o\").",
               "All", "Soluble", "Solvable", "Insoluble", "Nonsolvable";
        error "";
    end if;
end function;


procedure Advance(db, ~o, ~n, ~N, Sol, Insol : LimitOrder := false)
/*
   Advance o (if LimitOrder eq true) and n to point to the next suitable
   group.  N should be the number of groups of order o or -1. Sol/Insol
   indicate whether solvable/insolvable groups are considered. (At least
   one flag had better be set...)
*/
 if (N eq -1) then
    N := NumberOfGroups(db, o);
 end if;
 repeat
    n +:= 1;
    if (n gt N) then
       o +:= 1;
       if (LimitOrder) then
          return;
       end if;
       while (not IsInSmallGroupDatabase(o)) do
          o +:= 1;
       end while;
       n := 1;
       N := NumberOfGroups(db, o);
    end if;
    if (Sol) then
       if (Insol) then
          return;
       end if;
       if (IsSoluble(db, o, n)) then
          return;
       end if;
    end if;
    if (Insol) then
       if (not IsSoluble(db, o, n)) then
          return;
       end if;
    end if;
 until false;
end procedure;


// The following set (as of 17/4/02; "completeness" limit 2000) contains ALL
// pairs (o,n) such that SmallGroup(o,n) is not solvable. (Note that the
// infinite series contained in the database consist only of solvable groups,
// i.e., there are only finitely many possibilities for insolvable groups.)
_insol_pairs :=
{ car<IntegerRing(),IntegerRing()> |
 <960,10863>,<1440,4604>,<1920,240624>,<1920,240493>,<480,955>,
 <1920,240625>,<672,1044>,<1920,240785>,<1920,240613>,<1920,240777>,
 <1920,240549>,<1440,5850>,<1920,240849>,<1920,241003>,<1380,9>,
 <1920,240691>,<1920,240535>,<480,953>,<1920,240472>,<960,5733>,
 <1920,240727>,<960,10874>,<960,5743>,<1320,133>,<1680,400>,<480,943>,
 <1920,240930>,<1440,4591>,<1920,240635>,<1920,240949>,<660,14>,
 <1920,240505>,<1920,240626>,<360,122>,<1920,240816>,<1344,11305>,
 <672,1047>,<1920,240564>,<1920,240969>,<960,10880>,<1920,240897>,
 <1920,240984>,<1344,11289>,<1920,240526>,<1920,240968>,<1200,939>,
 <1920,240854>,<960,5702>,<1920,240707>,<1512,437>,<1920,240466>,
 <1080,263>,<960,5712>,<1440,4651>,<960,5697>,<1680,931>,<1920,240756>,
 <1440,4636>,<1920,240965>,<600,54>,<960,5725>,<1920,240655>,<1440,5846>,
 <1080,488>,<1920,240580>,<960,5718>,<1920,240492>,<1920,240435>,
 <1920,240508>,<1920,240772>,<1920,240966>,<1920,240926>,<960,5728>,
 <1440,4625>,<1920,240983>,<1200,477>,<600,144>,<1920,240601>,<1200,482>,
 <1920,240992>,<336,208>,<1920,240958>,<1920,240842>,<1080,262>,<960,640>,
 <1920,240530>,<360,118>,<1920,240552>,<1920,240627>,<1920,240801>,
 <1920,240960>,<1920,240702>,<1920,240630>,<480,957>,<1920,240574>,
 <660,13>,<1920,240720>,<1440,4641>,<1920,240832>,<960,10885>,<1344,6312>,
 <1920,240713>,<1920,240933>,<1800,558>,<120,35>,<1920,240913>,
 <1920,240788>,<960,5687>,<1920,240464>,<1440,1686>,<1200,943>,
 <1920,240561>,<1440,1690>,<1920,240740>,<1920,240447>,<1200,940>,
 <1920,240815>,<1200,481>,<1920,240510>,<1920,240690>,<1920,240603>,
 <960,5717>,<960,5739>,<1440,5843>,<1092,25>,<1920,240705>,<1512,781>,
 <1920,240616>,<720,763>,<1920,240786>,<1200,945>,<1920,240656>,
 <1920,240735>,<1440,1682>,<960,10876>,<1920,240908>,<1440,4631>,
 <1920,240870>,<672,1254>,<1920,240670>,<1920,240931>,<1800,563>,
 <1008,883>,<1920,240621>,<480,222>,<1920,240915>,<960,10879>,
 <1920,241002>,<1920,240576>,<1920,240541>,<1920,240673>,<1920,240503>,
 <1920,240982>,<1920,240896>,<1920,240666>,<1920,240797>,<1920,240781>,
 <1440,4628>,<1920,240877>,<1920,240664>,<1920,240798>,<1920,240729>,
 <720,413>,<1920,240811>,<1680,398>,<1920,240419>,<1920,240525>,
 <1920,240640>,<1920,240988>,<720,765>,<1920,240796>,<1440,4616>,
 <1920,240491>,<1920,240429>,<960,10884>,<1920,240677>,<1920,240809>,
 <1920,240840>,<1920,240734>,<1920,240873>,<1200,944>,<960,5681>,
 <1920,240742>,<1920,240799>,<960,5684>,<1920,240699>,<960,5716>,
 <1920,240634>,<1920,240521>,<1920,240461>,<1920,240498>,<1920,240943>,
 <1920,240942>,<480,949>,<1980,57>,<1920,240696>,<1920,240768>,<720,410>,
 <1920,240919>,<180,19>,<1920,240836>,<840,134>,<960,5744>,<1440,4655>,
 <1920,240477>,<720,414>,<120,34>,<1920,240567>,<1920,240962>,
 <480,1186>,<1920,240572>,<1920,240712>,<480,218>,<1920,240866>,
 <1920,240990>,<1680,401>,<1440,4627>,<1920,240928>,<1920,240818>,
 <1920,240737>,<1920,240941>,<1920,240888>,<240,189>,<1920,240822>,
 <1920,240551>,<1920,240905>,<1920,240500>,<1344,11685>,<1920,240946>,
 <1440,4614>,<1440,4624>,<720,421>,<1440,4597>,<1920,240867>,
 <1920,240708>,<1680,405>,<1920,240748>,<1920,240423>,<1800,328>,
 <1920,240689>,<1920,240471>,<1920,241004>,<1920,240862>,<1920,240449>,
 <1920,240770>,<720,417>,<1920,240467>,<1920,240718>,<1920,240953>,
 <1848,127>,<960,5685>,<1920,240861>,<1440,4638>,<60,5>,<1920,240733>,
 <1920,240631>,<1920,240871>,<1680,929>,<1920,240787>,<1920,240563>,
 <1920,240652>,<1920,240944>,<1920,240932>,<1920,240427>,<1920,240473>,
 <960,10883>,<1344,11292>,<240,92>,<1440,5854>,<1920,240651>,<672,1043>,
 <1920,240643>,<1920,240868>,<1920,240653>,<1200,474>,<1920,240641>,
 <1440,4607>,<1440,4606>,<1920,240680>,<1020,9>,<1344,11300>,<960,5715>,
 <1920,240542>,<1920,240758>,<1008,880>,<1800,562>,<1920,240876>,
 <1260,62>,<1920,240934>,<1920,240923>,<1920,240539>,<480,959>,
 <1440,4634>,<1920,240611>,<1920,240528>,<840,136>,<1920,240961>,
 <1920,240789>,<960,10867>,<600,147>,<960,10890>,<1920,240558>,
 <1920,240807>,<1440,5844>,<1920,240835>,<960,641>,<1620,71>,
 <1440,4599>,<1200,479>,<960,5722>,<960,5699>,<1920,240532>,
 <1920,240847>,<1440,4632>,<1560,147>,<1920,240534>,<1344,11301>,
 <1344,11304>,<1920,240654>,<1920,240710>,<1344,6316>,<1920,240701>,
 <1620,263>,<1440,4622>,<960,5698>,<1920,240774>,<960,10878>,
 <960,10892>,<1440,5847>,<1920,240778>,<1920,240956>,<1920,240617>,
 <1440,4615>,<240,89>,<1920,240714>,<1920,240681>,<1200,476>,
 <1920,240422>,<1920,240606>,<1920,240639>,<1920,240852>,<1920,240469>,
 <1920,240566>,<960,10873>,<1680,924>,<1920,240869>,<1920,240511>,
 <1920,240996>,<960,11358>,<960,5741>,<960,5731>,<1920,240448>,
 <1920,240667>,<1920,240609>,<1920,240684>,<1920,240812>,<1920,240883>,
 <480,221>,<1920,240559>,<1920,240954>,<960,637>,<1920,240633>,
 <1920,240517>,<960,10888>,<1920,240916>,<1920,240746>,<1920,240418>,
 <1920,240594>,<1920,240766>,<1920,240662>,<960,5720>,<1512,780>,
 <1344,11302>,<960,639>,<720,416>,<960,5740>,<1920,240892>,<1320,136>,
 <960,10866>,<1920,240749>,<1260,61>,<1920,240688>,<480,960>,
 <1920,240432>,<1440,4596>,<1920,240936>,<720,766>,<1920,240638>,
 <1200,483>,<960,10875>,<1440,4603>,<900,88>,<1740,9>,<1920,240546>,
 <1920,240856>,<1920,240460>,<1920,240560>,<1920,240751>,<1344,11295>,
 <1920,240577>,<1440,4650>,<1440,4653>,<1440,4598>,<1920,240454>,
 <336,209>,<1200,484>,<480,948>,<1680,926>,<1920,240872>,<1920,240570>,
 <1920,240442>,<1920,240642>,<1920,240825>,<1920,240844>,<1440,4609>,
 <1920,240568>,<1920,240800>,<1920,240682>,<1680,402>,<1920,240850>,
 <1920,240834>,<1920,240674>,<1920,240967>,<1920,240993>,<1440,4630>,
 <1440,4600>,<1920,240675>,<1920,240600>,<1680,409>,<1920,240875>,
 <720,418>,<1920,240581>,<1920,240671>,<1920,240739>,<1440,4621>,
 <960,5703>,<1920,240841>,<1920,240895>,<1440,4654>,<1920,240439>,
 <1920,240455>,<1920,240436>,<1920,240506>,<1920,240544>,<1800,561>,
 <1920,240963>,<1860,19>,<1680,408>,<1080,261>,<1680,397>,<1920,240518>,
 <1920,240425>,<1920,240741>,<1440,4608>,<1920,240858>,<1920,240637>,
 <1920,240644>,<1920,240829>,<1920,240612>,<1920,240767>,<1440,4649>,
 <960,5729>,<1920,240826>,<1920,240977>,<1920,240806>,<1344,11684>,
 <1920,240622>,<1920,240421>,<1920,240771>,<960,5682>,<1920,240587>,
 <720,411>,<1680,932>,<1920,240803>,<1920,240698>,<840,138>,
 <1440,4656>,<1920,240593>,<1920,240935>,<1344,6314>,<1080,493>,
 <1920,240483>,<480,954>,<1440,1683>,<1920,240927>,<1920,240999>,
 <1008,517>,<1920,240431>,<1920,240463>,<1920,240814>,<960,10865>,
 <1440,4602>,<1920,240819>,<1920,240987>,<1920,240599>,<1920,240562>,
 <1080,491>,<1920,240669>,<960,5732>,<1920,240790>,<1344,11293>,
 <1920,240881>,<960,5706>,<1200,478>,<1920,240475>,<1920,240853>,
 <1200,941>,<1920,240440>,<1920,240685>,<1920,240795>,<1920,240536>,
 <300,22>,<960,5691>,<1344,11290>,<1920,240499>,<1080,487>,<480,956>,
 <1920,240957>,<1920,240865>,<1920,240904>,<1800,557>,<1920,240658>,
 <1920,240683>,<1920,240474>,<480,217>,<960,5709>,<1920,240584>,
 <1920,240514>,<1440,4623>,<1920,240981>,<1920,240661>,<672,1046>,
 <1920,240846>,<1500,112>,<1920,240497>,<1920,240889>,<1920,240513>,
 <1920,240763>,<960,5734>,<960,11355>,<1680,406>,<1080,260>,
 <1920,240457>,<1344,6315>,<1920,240762>,<1620,262>,<1080,363>,
 <1920,240827>,<1320,134>,<1920,240694>,<960,10871>,<1920,240918>,
 <1920,240556>,<960,5688>,<1920,240465>,<840,13>,<480,1187>,
 <1920,240614>,<1920,240695>,<1920,240515>,<960,11356>,<480,952>,
 <1920,240864>,<1920,240706>,<1920,240945>,<1920,240443>,<360,51>,
 <1920,240555>,<1920,240764>,<1140,13>,<1920,240618>,<960,5727>,
 <1920,240782>,<1920,240605>,<1920,240900>,<1920,240693>,<1920,240557>,
 <1920,240678>,<1920,240632>,<1920,240636>,<1920,240951>,<1920,240716>,
 <1920,240863>,<1920,240509>,<1920,240700>,<1440,4595>,<1920,240545>,
 <1920,240547>,<1920,240901>,<1920,240478>,<1920,240890>,<1440,1687>,
 <1920,240911>,<1920,240857>,<504,157>,<480,945>,<1920,240940>,
 <1440,1691>,<1920,240833>,<504,156>,<1176,212>,<1920,240759>,
 <1920,240855>,<1920,240519>,<240,91>,<1560,149>,<1920,240794>,
 <720,415>,<1920,240752>,<1920,240585>,<1440,4620>,<1920,240914>,
 <1920,240715>,<960,11357>,<960,5707>,<1920,240554>,<1920,240490>,
 <1920,240985>,<1920,240484>,<1920,240417>,<1920,240524>,<1920,240516>,
 <1920,240719>,<1920,240902>,<1920,240948>,<1920,240754>,<480,220>,
 <1920,240823>,<1920,240470>,<1920,240495>,<1344,814>,<1920,240765>,
 <1920,240692>,<1920,240441>,<720,764>,<1440,4605>,<1440,4633>,
 <1920,240879>,<672,1048>,<1920,240588>,<1920,240924>,<1920,240480>,
 <1920,240665>,<1080,489>,<1620,418>,<1920,240504>,<960,5689>,
 <1440,4626>,<960,5700>,<1920,240650>,<1920,240830>,<1920,240885>,
 <1920,240533>,<1080,63>,<1920,240874>,<1920,240571>,<1200,942>,
 <540,31>,<1680,930>,<1920,240592>,<780,13>,<1920,240810>,<1440,1685>,
 <720,769>,<1440,4644>,<720,770>,<1920,240459>,<1920,240980>,
 <960,10889>,<1920,240959>,<1440,4635>,<1512,779>,<960,5724>,
 <960,5686>,<1920,240828>,<1800,560>,<1920,240481>,<1500,34>,
 <1920,240462>,<1920,240479>,<1680,403>,<1440,4618>,<1920,240939>,
 <1920,240903>,<960,5742>,<1344,11686>,<480,947>,<1320,137>,
 <1920,240732>,<1920,240921>,<480,958>,<1920,240925>,<1920,240775>,
 <960,5692>,<1920,240907>,<1920,240728>,<720,419>,<1920,240805>,
 <1920,240779>,<1920,240531>,<420,13>,<1920,240679>,<1920,240502>,
 <720,771>,<1920,240773>,<1800,559>,<1344,11297>,<240,94>,<1920,240704>,
 <1920,240887>,<1920,240586>,<1920,240426>,<1920,240976>,<1920,240540>,
 <1920,240433>,<1920,240649>,<1920,240793>,<1920,240645>,<960,10872>,
 <1008,882>,<1920,240769>,<1920,240859>,<240,190>,<1560,146>,
 <1920,240776>,<1920,240434>,<1920,240783>,<960,5710>,<1920,240578>,
 <1920,240878>,<960,10882>,<1440,4593>,<1920,240579>,<960,10887>,
 <1920,240839>,<1920,240824>,<1920,240453>,<1920,240686>,<1440,4652>,
 <1920,240808>,<1080,264>,<960,5708>,<1440,4610>,<960,5714>,<1440,4639>,
 <1344,11291>,<1920,240725>,<960,5690>,<1920,240482>,<1440,4611>,
 <1920,240452>,<1620,264>,<960,5719>,<840,135>,<1920,240920>,
 <960,10886>,<960,5694>,<1920,240970>,<1920,240575>,<120,5>,
 <1920,240910>,<1920,240780>,<1920,240843>,<960,5704>,<1920,240838>,
 <1920,240660>,<1920,240602>,<720,772>,<600,146>,<336,114>,
 <1920,240444>,<1920,240964>,<1920,240520>,<1920,240485>,<1920,240753>,
 <1320,13>,<1920,240974>,<1920,240791>,<1920,240489>,<1344,11296>,
 <1440,4612>,<1920,240709>,<672,1045>,<1344,6311>,<1920,240882>,
 <1920,240451>,<1440,5849>,<1920,240543>,<1440,4647>,<1440,4643>,
 <1920,240721>,<960,5705>,<1920,240802>,<1920,240938>,<1920,240523>,
 <1440,4629>,<1920,240468>,<1440,1692>,<1920,240548>,<1920,240971>,
 <168,42>,<1344,6313>,<1440,4619>,<1344,11303>,<1344,11294>,
 <1920,240950>,<1920,240747>,<960,5735>,<960,5736>,<1920,240648>,
 <360,119>,<1920,240676>,<1440,4594>,<1920,240837>,<1920,240589>,
 <1920,240573>,<1320,135>,<1920,240487>,<1920,240979>,<1440,4637>,
 <960,5726>,<1920,240722>,<960,5696>,<720,412>,<1920,240731>,<1800,555>,
 <480,951>,<1920,240845>,<1920,240610>,<1920,240997>,<1920,240620>,
 <1440,4646>,<1920,240657>,<1920,241000>,<1440,4613>,<1920,240831>,
 <1920,240598>,<1920,240738>,<1920,240430>,<1920,240893>,<1920,240607>,
 <960,5683>,<1920,240755>,<1920,240994>,<540,88>,<1920,240792>,
 <1920,240820>,<1440,5841>,<1920,240952>,<1080,492>,<1920,240615>,
 <1920,240697>,<1920,240450>,<1920,240604>,<1440,5845>,<1920,240989>,
 <1920,240529>,<1920,240955>,<1920,240597>,<1920,240565>,<1920,240619>,
 <360,120>,<1200,480>,<1920,240628>,<1920,240821>,<1920,240476>,
 <1920,240623>,<960,5693>,<1920,240582>,<1920,240446>,<1920,240972>,
 <960,5745>,<1440,1688>,<1920,240723>,<960,5746>,<960,638>,
 <1920,240726>,<1920,240537>,<960,10881>,<960,10870>,<1920,240428>,
 <1920,240672>,<1680,399>,<960,642>,<1920,240437>,<1680,925>,
 <960,5738>,<960,10877>,<960,10869>,<960,5713>,<1920,240851>,
 <1440,5848>,<840,137>,<1920,240596>,<1440,4645>,<1920,240456>,
 <1920,240750>,<1920,240986>,<1920,240703>,<1440,4648>,<960,5747>,
 <1920,240591>,<1320,14>,<1080,490>,<1920,240717>,<600,145>,<480,219>,
 <1920,240538>,<1440,1684>,<1680,928>,<1344,11288>,<1680,407>,
 <1920,240512>,<960,5730>,<1980,58>,<1440,4617>,<1920,240711>,
 <672,1255>,<960,5711>,<1920,240947>,<1920,240761>,<1920,240663>,
 <1008,884>,<1920,240937>,<1920,240975>,<1920,240569>,<960,10868>,
 <1920,240647>,<1920,240507>,<1920,240995>,<1920,240804>,
 <1920,240743>,<1920,240813>,<1920,240899>,<1920,240909>,
 <1920,240784>,<1920,240668>,<1440,4590>,<1920,240486>,<1440,4642>,
 <360,121>,<480,944>,<1440,5853>,<1440,5852>,<720,409>,<1920,240458>,
 <1920,240608>,<1920,240744>,<1920,240488>,<1920,240496>,<1920,240906>,
 <1680,404>,<1920,240687>,<1920,240724>,<1920,240991>,<1920,240550>,
 <720,420>,<1920,240501>,<1920,240848>,<1560,148>,<1200,473>,
 <1920,240929>,<1920,240912>,<1920,240445>,<1920,240424>,<1344,11299>,
 <1920,240817>,<1920,240917>,<1920,240595>,<1920,240646>,<1560,13>,
 <1920,240973>,<240,90>,<1440,5851>,<1920,240629>,<1200,475>,
 <1920,240494>,<1440,5842>,<480,946>,<1920,240736>,<1920,240527>,
 <1440,4601>,<960,10891>,<1920,240860>,<1920,240978>,<1920,241001>,
 <960,5695>,<1920,240894>,<1920,240730>,<1920,240898>,<960,10864>,
 <1920,240420>,<1920,240583>,<1920,240760>,<1344,11298>,<1920,240922>,
 <1920,240659>,<240,93>,<1920,240522>,<1440,1689>,<960,5723>,
 <1920,240891>,<1920,240880>,<1440,4640>,<1920,240745>,<960,5737>,
 <1008,881>,<720,767>,<1920,240998>,<1440,4592>,<1920,240884>,
 <480,950>,<960,5701>,<960,5721>,<1920,240590>,<1920,240438>,
 <1920,240886>,<1920,240757>,<1320,138>,<1920,240553>,<720,768>,
 <1800,556>,<1680,927>,<1440,1693>};

// === First, some wrapper functions that open and shut the database each time.

/* 
//Defined to be identical to IsSoluble in bind/i.b, so superfluous,
//so commented out -- DR 2 nov 2010.
intrinsic IsSolvable(D::DB, o::RngIntElt, n::RngIntElt) -> BoolElt
{Return true iff SmallGroup(D, o, n) is soluble}
    _sg_check_order(o);
    if (IsSolvableOrder(o)) then
       return true;
    end if;
    return  <o,n> notin _insol_pairs;
end intrinsic;
*/

intrinsic IsSoluble(D::DB, o::RngIntElt, n::RngIntElt) -> BoolElt
{Return true iff SmallGroup(D, o, n) is soluble}
    _sg_check_order(o);
    if (IsSolvableOrder(o)) then
       return true;
    end if;
    return  <o,n> notin _insol_pairs;
end intrinsic;

intrinsic SmallGroup(o::RngIntElt, n::RngIntElt) -> Grp
{Returns the group number n of order o from the small groups database}
    _sg_check_order(o);
    requirerange n, 1, NumberOfSmallGroups(o);
    db := SmallGroup2Database();
    res := SmallGroup(db, o, n);
    delete db;
    return res;
end intrinsic;

intrinsic SmallGroupIsSolvable(D::DB, o::RngIntElt, n::RngIntElt) -> BoolElt
{Return true if SmallGroup(D, o, n) is soluble (does not load the group)}
    _sg_check_order(o);
    requirerange n, 1, NumberOfSmallGroups(o);
    return IsSoluble(D, o, n);
end intrinsic;

intrinsic SmallGroupIsSoluble(D::DB, o::RngIntElt, n::RngIntElt) -> BoolElt
{Return true if SmallGroup(D, o, n) is soluble (does not load the group)}
    _sg_check_order(o);
    requirerange n, 1, NumberOfSmallGroups(o);
    return IsSoluble(D, o, n);
end intrinsic;

intrinsic SmallGroupIsSolvable(o::RngIntElt, n::RngIntElt) -> BoolElt
{Return true if SmallGroup(o, n) is soluble (does not load the group)}
    local db, res;
    _sg_check_order(o);
    requirerange n, 1, NumberOfSmallGroups(o);
    db := SmallGroup2Database();
    res := IsSoluble(db, o, n);
    delete db;
    return res;
end intrinsic;

intrinsic SmallGroupIsSoluble(o::RngIntElt, n::RngIntElt) -> BoolElt
{Return true if SmallGroup(o, n) is soluble (does not load the group)}
    local db, res;
    _sg_check_order(o);
    requirerange n, 1, NumberOfSmallGroups(o);
    db := SmallGroup2Database();
    res := IsSoluble(db, o, n);
    delete db;
    return res;
end intrinsic;

intrinsic SmallGroupIsInsolvable(o::RngIntElt, n::RngIntElt) -> BoolElt
{Return true if SmallGroup(o, n) is insoluble (does not load the group)}
    return not SmallGroupIsSoluble(o, n);
end intrinsic;

intrinsic SmallGroupIsInsoluble(o::RngIntElt, n::RngIntElt) -> BoolElt
{Return true if SmallGroup(o, n) is insoluble (does not load the group)}
    return not SmallGroupIsSoluble(o, n);
end intrinsic;

intrinsic SmallGroupIsInsolvable(D::DB, o::RngIntElt, n::RngIntElt) -> BoolElt
{Return true if SmallGroup(D, o, n) is insoluble (does not load the group)}
    return not SmallGroupIsSoluble(D, o, n);
end intrinsic;

intrinsic SmallGroupIsInsoluble(D::DB, o::RngIntElt, n::RngIntElt) -> BoolElt
{Return true if SmallGroup(D, o, n) is insoluble (does not load the group)}
    return not SmallGroupIsSoluble(D, o, n);
end intrinsic;

intrinsic IdentifyGroup(G::Grp) -> Tup
{The size and number of the group isomorphic to G in the small groups database}
    require Type(G) in {GrpPerm, GrpMat, GrpPC, GrpAb, GrpAuto, GrpFP}:
	"Unable to identify groups of this type";
    require CanIdentifyGroup(#G): "Unable to identify groups of order", #G;
    db := SmallGroup2Database();
    res := IdentifyGroup(db, G);
    ClearIdentificationTree();
    delete db;
    return res;
end intrinsic;

intrinsic NumberOfSmallGroups(D::DB, n::RngIntElt) -> RngIntElt
{The number of groups of order n stored in the database D}
    _sg_check_order(n);
    return NumberOfGroups(D, n);
end intrinsic;

intrinsic NumberOfSmallGroups(n::RngIntElt) -> RngIntElt
{The number of groups of order n stored in the database of small groups}
    local	db, res;
    _sg_check_order(n);
    db := SmallGroup2Database();
    res := NumberOfGroups(db, n);
    delete db;
    return res;
end intrinsic;

intrinsic SmallGroupDatabaseLimit(D::DB) -> RngIntElt
{The order up to which the small groups database D contains all groups}
    return LargestOrder(D);
end intrinsic;

intrinsic SmallGroupDatabaseLimit() -> RngIntElt
{The order up to which the small groups database contains all groups}
    db := SmallGroup2Database();
    res := LargestOrder(db);
    delete db;
    return res;
end intrinsic;

intrinsic SmallGroupDatabase() -> DB
{Return the small groups database, opened for an extended search}
    return SmallGroup2Database();
end intrinsic

intrinsic OpenSmallGroupDatabase() -> DB
{Return the small groups database, opened for an extended search}
    return SmallGroup2Database();
end intrinsic

intrinsic CloseSmallGroupDatabase(~D::DB) 
{Close the smallgroup database}
// ########   delete D;
    ClearIdentificationTree();
end intrinsic;

// Now, some functions that open the database for extended searches:
//
// SmallGroup(order s, predicate f)
//    Returns the first group g of order s which satisfies f(g). If s is a list
//    of integers, it attempts to return a group g of each order in s which
//    satisfies f(g).
// 
// SmallGroups(order s, predicate )
//    Returns all groups g of order s which satisfy f(g).  If s is a list/set,
//    returns all groups g of order in s which satisfy f(g).
// 
// 
// A process P is an object used to iterate through the groups database. To use
// a process, one creates the process with SmallGroupProcess().  To extract the
// current group of a process P, one uses Current(P).  To move to
// the next group, one uses Advance(P).
// 
// 
// SmallGroupProcess(order s, Predicate:=true)
//    Returns a process which iterates through all groups with order
//    in s and which satisfy Predicate.  The Predicate is either
//    the boolean value true or a function Group->BoolElt.
// 
// InternalSmallGroupProcessRestart(process_tuple ~p)
//    Return a process to its first group.
// 
// InternalSmallGroupProcessIsEmpty(process_tuple p)
//    Returns true if p points to a group or false if no more groups satisfying
//    the given conditions are available.
// 
// InternalNextSmallGroup(process_tuple ~p)
//    Moves p to the next groups satisfying the given conditions or to an empty
//    state if no more groups are found.
// 
// InternalExtractSmallGroup(process_tuple p)
//    Extracts the current group of p.
// 
// InternalExtractSmallGroupLabel(process_tuple p)
//    Returns the label (s, n) of the current group of p.
//    ExtractGroup(p) eq SmallGroup(s,n).
// 
//
// All functions take two named parameters, Insoluble := true and
// Soluble := true
// ----------------------------------------------------------------------------



// Process is a tuple <order, num, group predicate, orders, whichorder, 
//   Soluble, Insoluble, database>
// group predicate may be the boolean value "true" to save evaluation
// order will range over [low..high].  
//
// Process will loop through all groups with order between low and high
// inclusive which further satisfy the predicate (or all of Predicate eq true).
//
// Process only includes soluble groups if Soluble eq true and non-soluble
// groups if Insoluble eq true.

intrinsic InternalNextSmallGroup(~p::Tup)
{Moves the small group process tuple p to its next group};
    error if InternalSmallGroupProcessIsEmpty(p),
        "Process finished";
    repeat
        N := -1;
        Advance(p[8], ~p[1], ~p[2], ~N, p[6], p[7] : LimitOrder := true);
        if (p[1] ne p[4][p[5]]) then    // We have exhausted current order
            p[5] +:= 1;
            p[2] := 0;
            if (p[5] gt #p[4]) then
                p[1] := 0;
                    break;
            else
                p[1] := p[4][p[5]];
            end if;
        end if;
    until (p[1] eq 0)  or
	  (p[2] ne 0  and  p[3](SmallGroup(p[8], p[1], p[2])));
end intrinsic;

intrinsic InternalSmallGroupProcessRestart(~p::Tup)
{Returns the small group process tuple p to its first group};
    p[5] := 1;
    p[1] := p[4][p[5]];
    p[2] := 0;
    InternalNextSmallGroup(~p);
    /*
    error if (p[1] eq 0),
        "No small groups in the specified range satisfy the predicate";
    */
end intrinsic;

intrinsic SmallGroupProcess(Orders::[RngIntElt] :
			  Search := "All")-> Process
{Returns a small group process.  This will iterate through all groups with 
order in Orders.  To extract the current group from a process, use
ExtractGroup().  To move to the next group in a process, use
NextGroup().  To find out which group the process currently points 
to, use ExtractLabel().  The user may limit the process to soluble or
insoluble groups by setting Search.  Search may take the values "All", 
"Soluble" or "Insoluble" (or variants thereof).}

    return SmallGroupProcess(Orders, func<x|true> : Search := Search);
end intrinsic;

intrinsic SmallGroupProcess(Orders::[RngIntElt], Predicate::Program : 
			    Search := "All") ->  Process
{Returns a small group process as described above.  This will iterate through 
all groups (g) with order in Orders which satisfy Predicate(g).}

    Soluble, Insoluble := _sg_string_to_tf(Search);
    if #Set(Orders) ne #Orders then
        R := [o : o in Orders | not o in Self()];
    else
        R := Orders;
    end if;
    for o in R do
	_sg_check_order(o);
    end for;

    case Type(Predicate):
        when Intrinsic:
            Pred := func<x|Predicate(x)>;
        else
            Pred := Predicate;
    end case;

    tup := <0, 0, Pred, R, 1, Soluble, Insoluble, SmallGroup2Database()>;
    InternalSmallGroupProcessRestart(~tup);
    P := InternalCreateProcess("Small Group", tup,
			InternalSmallGroupProcessIsEmpty,
			InternalNextSmallGroup,
			InternalExtractSmallGroup,
			InternalExtractSmallGroupLabel);
    return P;
end intrinsic;

intrinsic SmallGroupProcess(o::RngIntElt :
			  Search := "All")-> Process
{Returns a small group process as described above.  This will iterate through 
all groups with order o.}
    return SmallGroupProcess([o]: Search := Search);
end intrinsic;

intrinsic SmallGroupProcess(o::RngIntElt, Predicate::Program : 
			    Search := "All") ->  Process
{Returns a small group process as described above.  This will iterate through 
all groups (g) of order o which satisfy Predicate(g).}
    return SmallGroupProcess([o], Predicate: Search := Search);
end intrinsic;

intrinsic InternalSmallGroupProcessIsEmpty(p::Tup) -> BoolElt
{Returns true if the small group process tuple has passed its last group.};

    return (p[1] eq 0);
end intrinsic;

intrinsic InternalExtractSmallGroup(p::Tup) -> Grp
{Returns the current group of the small group process tuple p};
    error if InternalSmallGroupProcessIsEmpty(p),
        "Process finished";
    return SmallGroup(p[8], p[1], p[2]);
end intrinsic;

intrinsic InternalExtractSmallGroupLabel(p::Tup) -> RngIntElt, RngIntElt
{Returns the label (s,n) of the small group process tuple p.  This is the order and
number of the current group of p};
    return p[1], p[2];
end intrinsic;


intrinsic SmallGroup(D::DB, o::RngIntElt, Predicate::Program :
                     Search := "All") -> Grp
{Returns the first group of order o which satisfies Predicate.
The user may limit the the search to soluble or insoluble groups by setting
the parameter Search.  Search may take the values "All", "Soluble" or 
"Insoluble" (or variants).}

    Soluble, Insoluble := _sg_string_to_tf(Search);
    _sg_check_order(o);
    Order := o;
    Num := 0;
    N := -1;
    Advance(D, ~Order, ~Num, ~N, Soluble, Insoluble : LimitOrder := true);

    if (Order gt o) then
	printf "Error: There are no groups of order %o satisfying the " cat 
	       "predicate in the small groups database", o;
        error "";
    end if;
    while (Order eq o) do
	G := SmallGroup(D, Order, Num);
        if Predicate(G) then
            return G;
        end if;
        delete G;
        Advance(D, ~Order, ~Num, ~N, Soluble, Insoluble : LimitOrder := true);
    end while;
    printf "Error: There are no groups of order %o satisfying the " cat 
	   "predicate in the small groups database", o;
    error "";
end intrinsic;

intrinsic SmallGroup(o::RngIntElt, Predicate::Program :
                     Search := "All") -> Grp
{Returns the first group of order o which satisfies Predicate.
The user may limit the the search to soluble or insoluble groups by setting
the parameter Search.  Search may take the values "All", "Soluble" or 
"Insoluble" (or variants).}

    local	db;

    Soluble, Insoluble := _sg_string_to_tf(Search);
    _sg_check_order(o);
    db := SmallGroup2Database();
    Order := o;
    Num := 0;
    N := -1;
    Advance(db, ~Order, ~Num, ~N, Soluble, Insoluble : LimitOrder := true);

    if (Order gt o) then
	delete db;
	printf "Error: There are no groups of order %o satisfying the " cat 
	       "predicate in the small groups database", o;
        error "";
    end if;
    while (Order eq o) do
	G := SmallGroup(db, Order, Num);
        if Predicate(G) then
	    delete db;
            return G;
        end if;
        delete G;
        Advance(db, ~Order, ~Num, ~N, Soluble, Insoluble : LimitOrder := true);
    end while;
    delete db;
    printf "Error: There are no groups of order %o satisfying the " cat 
	   "predicate in the small groups database", o;
    error "";
end intrinsic;

intrinsic SmallGroup(Orders::SeqEnum, Predicate::Program : 
		     Search := "All") -> Grp
{Returns the first group with order in Orders which satisfies the 
predicate and the search condition specified by Search (see above).}

    local	db;

    db := SmallGroup2Database();
    Soluble, Insoluble := _sg_string_to_tf(Search);
    for o in Orders do
        _sg_check_order(o);
        Order := o;
        Num := 0;
        N := -1;
        Advance(db, ~Order, ~Num, ~N, Soluble, Insoluble : LimitOrder := true);
        while (Order eq o) do
            G := SmallGroup(db, Order, Num);
            if (Predicate(G)) then
                delete db;
                return G;
            end if;
            Advance(db, ~Order, ~Num, ~N, Soluble, Insoluble
                                                       : LimitOrder := true);
        end while;
    end for;
    delete db;
    printf "Error: No groups of the specified order%o satisfy the predicate",
	   (#Orders eq 1) select "" else "s";
    error "";
end intrinsic;

intrinsic SmallGroup(D::DB, Orders::SeqEnum, Predicate::Program : 
		     Search := "All") -> Grp
{Returns the first group with order in Orders which satisfies the 
predicate and the search condition specified by Search (see above).}

    Soluble, Insoluble := _sg_string_to_tf(Search);
    for o in Orders do
        _sg_check_order(o);
        Order := o;
        Num := 0;
        N := -1;
        Advance(D, ~Order, ~Num, ~N, Soluble, Insoluble : LimitOrder := true);
        while (Order eq o) do
            G := SmallGroup(D, Order, Num);
            if (Predicate(G)) then
                return G;
            end if;
            Advance(D, ~Order, ~Num, ~N, Soluble, Insoluble
                                                       : LimitOrder := true);
        end while;
    end for;
    printf "Error: No groups of the specified order%o satisfy the predicate",
	   (#Orders eq 1) select "" else "s";
    error "";
end intrinsic;


intrinsic SmallGroup(o::RngIntElt : Search := "All") -> Grp
{Returns the first group of order o which satisfies the search condition 
specified by Search (see above).}
    local	db;

    db := SmallGroup2Database();
    Soluble, Insoluble := _sg_string_to_tf(Search);
    _sg_check_order(o);
    Order := o;
    Num := 0;
    N := -1;
    Advance(db, ~Order, ~Num, ~N, Soluble, Insoluble : LimitOrder := true);
    if (Order gt o) then
	delete db;
	printf "Error: There are no groups of order %o satisfying the " cat
	       "search criteria in the small groups database", o;
	error "";
    end if;
    res :=  SmallGroup(db, Order, Num);
    delete db;
    return res;
end intrinsic;

intrinsic SmallGroup(D::DB, o::RngIntElt : Search := "All") -> Grp
{Returns the first group of order o which satisfies the search condition 
specified by Search (see above).}

    Soluble, Insoluble := _sg_string_to_tf(Search);
    _sg_check_order(o);
    Order := o;
    Num := 0;
    N := -1;
    Advance(D, ~Order, ~Num, ~N, Soluble, Insoluble : LimitOrder := true);
    if (Order gt o) then
	printf "Error: There are no groups of order %o satisfying the " cat
	       "search criteria in the small groups database", o;
	error "";
    end if;
    return SmallGroup(D, Order, Num);
end intrinsic;

intrinsic SmallGroups(D::DB, o::RngIntElt :
		      Search := "All", Warning := true) -> List
{Returns a list of all groups of order o.  The user may limit the search to 
soluble or insoluble groups by setting the parameter Search.  Search may take 
the value "All", "Soluble" or "Insoluble" (or variants thereof).  Some orders
will produce a very large list of groups -- in such cases a warning will be 
printed unless the user specifies Warning := false.}

    _sg_check_order(o);
    Soluble, Insoluble := _sg_string_to_tf(Search);

    // no warning for insoluble groups; there are just 1024 in total; not
    //    worth sorting this out for individual group orders...
    _sg_warn_lots(Soluble select NumberOfGroups(D, o) else 1, Warning);

    return &cat[[*SmallGroup(D, o, n)*] : n in [1..NumberOfGroups(D, o)] |
		           (Soluble and (Insoluble or IsSoluble(D, o, n)))
                            or (Insoluble and not IsSoluble(D, o, n))];
end intrinsic;

intrinsic SmallGroups(o::RngIntElt :
		      Search := "All", Warning := true) -> List
{Returns a list of all groups of order o.  The user may limit the search to 
soluble or insoluble groups by setting the parameter Search.  Search may take 
the value "All", "Soluble" or "Insoluble" (or variants thereof).  Some orders
will produce a very large list of groups -- in such cases a warning will be 
printed unless the user specifies Warning := false.}
    local	db, res;

    _sg_check_order(o);
    db := SmallGroup2Database();
    Soluble, Insoluble := _sg_string_to_tf(Search);

    // no warning for insoluble groups; there are just 1024 in total; not
    //    worth sorting this out for individual group orders...
    _sg_warn_lots(Soluble select NumberOfGroups(db, o) else 1, Warning);

    res := &cat[[*SmallGroup(db, o, n)*] : n in [1..NumberOfGroups(db, o)] |
		           (Soluble and (Insoluble or IsSoluble(db, o, n)))
                            or (Insoluble and not IsSoluble(db, o, n))];
    delete db;
    return res;
end intrinsic;

intrinsic SmallGroups(D::DB, Orders::SeqEnum : 
		      Search := "All", Warning := true) -> List
{As above, but with a list of orders.}

    S := Set(Orders);
    for o in S do
	_sg_check_order(o);
    end for;

    Soluble, Insoluble := _sg_string_to_tf(Search);

    if Soluble then
	Number := &+ [Integers() | NumberOfGroups(D, o) : o in S];
    else
        // no warning for insoluble groups; there are just 1024 in total; not
        //    worth sorting this out for individual group orders...
	Number := 1;
    end if;
    _sg_warn_lots(Number, Warning);

    Result := [**];
    for o in S do
	L := [n : n in [1..NumberOfGroups(D, o)] |
	      (Soluble and (Insoluble or IsSoluble(D, o, n)))
                            or (Insoluble and not IsSoluble(D, o, n))];
	Result cat:= &cat ([[*SmallGroup(D, o, n)*] : n in L] cat [[**]]);
    end for;
    return Result;
end intrinsic;

intrinsic SmallGroups(Orders::SeqEnum : 
		      Search := "All", Warning := true) -> List
{As above, but with a list of orders.}

    S := Set(Orders);
    for o in S do
	_sg_check_order(o);
    end for;

    db := SmallGroup2Database();
    Soluble, Insoluble := _sg_string_to_tf(Search);

    if Soluble then
	Number := &+ [Integers() | NumberOfGroups(db, o) : o in S];
    else
        // no warning for insoluble groups; there are just 1024 in total; not
        //    worth sorting this out for individual group orders...
	Number := 1;
    end if;
    _sg_warn_lots(Number, Warning);

    Result := [**];
    for o in S do
	L := [n : n in [1..NumberOfGroups(db, o)] |
	      (Soluble and (Insoluble or IsSoluble(db, o, n)))
                            or (Insoluble and not IsSoluble(db, o, n))];
	Result cat:= &cat ([[*SmallGroup(db, o, n)*] : n in L] cat [[**]]);
    end for;
    delete db;
    return Result;
end intrinsic;


intrinsic SmallGroups(D::DB, o::RngIntElt, Predicate::Program :
		      Search := "All", Warning := true) -> List
{Returns a list of all groups (g) with order o which satisfy Predicate(g) eq 
true and the search condition specified by Search}

    _sg_check_order(o);

    Soluble, Insoluble := _sg_string_to_tf(Search);

    L := [n : n in [1..NumberOfGroups(D, o)] |
	  (Soluble and (Insoluble or IsSoluble(D, o, n)))
           or (Insoluble and not IsSoluble(D, o, n))];
    Result := &cat [[*g*] : n in L | Predicate(g)
		    where g is SmallGroup(D, o, n)];
    if (#Result eq 0) then
	Result := [**];
    end if;
    return Result;
end intrinsic;

intrinsic SmallGroups(o::RngIntElt, Predicate::Program :
		      Search := "All", Warning := true) -> List
{Returns a list of all groups (g) with order o which satisfy Predicate(g) eq 
true and the search condition specified by Search}

    _sg_check_order(o);
    db := SmallGroup2Database();
    Result := SmallGroups(db, o, Predicate : Search := Search, Warning := Warning);
    delete db;
    return Result;
end intrinsic;

intrinsic SmallGroups(D::DB, Orders::SeqEnum, Predicate::Program :
		      Search := "All", Warning := true) -> List
{As above, but with a list of orders.}

    S := Set(Orders);
    for o in S do
	_sg_check_order(o);
    end for;

    Soluble, Insoluble := _sg_string_to_tf(Search);

    return &cat [SmallGroups(D, o, Predicate : Search := Search, Warning := Warning) : o in S];
end intrinsic;

intrinsic SmallGroups(Orders::SeqEnum, Predicate::Program :
		      Search := "All", Warning := true) -> List
{As above, but with a list of orders.}

    S := Set(Orders);
    for o in S do
	_sg_check_order(o);
    end for;

    Soluble, Insoluble := _sg_string_to_tf(Search);

    db := SmallGroup2Database();
    res :=  &cat [SmallGroups(db, o, Predicate : Search := Search, Warning := Warning) : o in S];
    delete db;
    return res;
end intrinsic;

intrinsic SmallGroupEncoding(G::GrpPC) -> RngIntElt, RngIntElt
{Encode a pc-group as an integer using the small groups data coding}
    l := NPCgens(G);
    indices := PCPrimes(G);
    mi := Maximum(indices) - 1;
    code := 0;
    base := 1;

    if #Set(indices) gt 1 then
	for i in [l .. 1 by -1] do
	    code +:= base * (indices[i] - 2);
	    base *:= mi;
	end for;
    end if;

    nt := [];
    for i in [1 .. l - 1] do
	r := G.i^indices[i];
	if not IsIdentity(r) then
	    Append(~nt, r);
	    code +:= base;
	end if;
	base *:= 2;
    end for;

    for i in [1 .. l - 1] do
	for j in [i + 1 .. l] do
	    r := (G.j, G.i);
	    if not IsIdentity(r) then
		Append(~nt, r);
		code +:= base;
	    end if;
	    base *:= 2;
	end for;
    end for;

    indices := [&* indices[x + 1 .. l]: x in [1 .. l]];
    size := #G;
    for i in nt do
	x := Eltseq(i);
	code +:= base * &+ [Integers() | indices[j] * x[j]: j in [1 .. l]];
	base *:= size;
    end for;
    return code, size;
end intrinsic;

function RelatorsFromCode(code, size, gens)
    ff := Factorisation(size);
    f := &cat [ [x[1]: i in [1 .. x[2]]]: x in ff];
    l := #f;
    mi := Maximum(f) - 1;
    n := code;
    if #Set(f) gt 1 then
	n, n1 := Quotrem(n, mi^l);
	indices := [];
	for i in [1 .. l] do
	    n1, r := Quotrem(n1, mi);
	    indices[i] := r + 2;
	end for;
	indices := Reverse(indices);
    else
	indices := f;
    end if;

    rels := [];
    rr := [];

    id := gens[1]^0;
    for i in [1 .. l] do
	rels[i] := (gens[i]^indices[i] = id);
    end for;

    ll := l * (l + 1) div 2 - 1;
    uc := [Integers() | ];
    n, n1 := Quotrem(n, 2^ll);
    for i in [1 .. ll] do
	n1, r := Quotrem(n1, 2);
	uc[i] := r;
    end for;

    for i in [1 .. &+ uc] do
	n, n1 := Quotrem(n, size);
	g := id;
	for j in [l .. 1 by -1] do
	    n1, r := Quotrem(n1, indices[j]);
	    if r gt 0 then
		g := gens[j]^r * g;
	    end if;
	end for;
	Append(~rr, g);
    end for;
    z := 1;
    for i in [1 .. l - 1] do
	if uc[i] eq 1 then
	    rels[i] := (LHS(rels[i]) = RHS(rels[i]) * rr[z]);
	    z +:= 1;
	end if;
    end for;
    z2 := l - 1;
    for i in [1 .. l] do
	for j in [i + 1 .. l] do
	    z2 +:= 1;
	    if uc[z2] eq 1 then
		Append(~rels, (gens[j], gens[i]) = rr[z]);
		z +:= 1;
	    end if;
	end for;
    end for;
    return rels;
end function;

intrinsic SmallGroupDecoding(code::RngIntElt, size::RngIntElt) -> GrpPC
{Decode a small groups data code representing a pc-group}
    if size eq 1 then
	return CyclicGroup(GrpPC, 1);
    end if;

    F := FreeGroup(&+ [Integers() | x[2]: x in Factorisation(size)]);
    gens := [F.i: i in [1 .. Ngens(F)]];
    return quo<F | RelatorsFromCode(code, size, gens):
	Class := "PolycyclicGroup">;
end intrinsic;

