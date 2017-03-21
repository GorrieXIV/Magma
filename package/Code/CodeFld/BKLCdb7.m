freeze;
// BestKnownLinearCodes DataBase for GF(7)
// insert useful info here

q_str    := "7";
start_k := 1;
MAXN := 100;
Div1 := 20;
Div2 := 30;
ConstructionEnum := [
"trivial",// 1
"dual-all-1",// 2
"shorten",// 3
"residue",// 4
"ConstaCyclic",// 5
"constructionB",// 6
"subcode",// 7
"puncture",// 8
"AG_divisor",// 9
"gen",// 10
"quasicyclic",// 11
"concatenation",// 12
"cyclic",// 13
"extend",// 14
"QR",// 15
"X",// 16
"quasicyclic_stack",// 17
"quasitwistedcyclic",// 18
"XL",// 19
"Dual",// 20
"lengthening",// 21
"constructionB2",// 22
"add_column",// 23
"XX",// 24
"BCH",// 25
"Hamming",// 26
"PG",// 27
"SubfieldSubcode",// 28
"SubcodeBetweenCode",// 29
"BZ",// 30
"Curve",// 31
"AGDivDeg1",// 32
"MDS"//33
];

GF7ConstructionEnum := ConstructionEnum;
GF7MAXN := MAXN;



GF7Index := [
\[0],
\[57,114],
\[171,228,285],
\[342,399,474,531],
\[588,645,720,795,852],
\[909,966,1041,1116,1191,1248],
\[1305,1362,1437,4399,4474,4549,4606],
\[4663,4720,4795,4870,4963,5038,5113,5170],
\[5227,5284,5359,5434,5509,5584,5659,5734,5791
],
\[5848,5905,5980,6055,6130,6205,6280,6355,6430
,6487],
\[6544,6601,6676,6751,6826,6901,6976,7051,7126
,7201,7258],
\[7315,7372,7447,7522,7597,7672,7747,7822,7897
,7972,8047,8104],
\[8161,8218,8293,8368,8443,8825,8900,8975,9050
,9125,9200,9275,9332],
\[9389,9446,9521,9596,9924,9999,10074,10209,10284
,10359,10434,10509,10584,10641],
\[10698,10755,10830,11109,11184,11259,11334,11409,11484
,11951,12026,12101,12176,12251,12308],
\[12365,12422,12515,12590,12665,12740,12815,12890,12965
,13040,13115,13190,13265,13340,13415,13472],
\[13529,13586,13661,13736,13811,13886,13961,14036,14111
,14186,14261,14336,14411,14486,14561,14636,14693],
\[14750,14807,14882,14957,15032,15183,15336,15411,15486
,15561,15636,15711,15786,16270,16345,16420,16495,16552
],
\[16609,16666,16741,16816,16891,16966,17096,17171,17246
,17321,17425,18171,18246,18321,18396,18471,18546,18621
,18678],
\[18735,18792,18867,18942,19113,19411,19486,19709,19936
,20011,20088,20163,20238,20313,20388,20463,20538,20613
,20688,20745],
\[20802,20859,20934,21009,21084,21159,21320,21575,21693
,21768,21843,21918,21993,22068,22143,22218,22293,22368
,22443,22518,22575],
\[22632,22689,22764,23146,23221,23296,23371,23489,23564
,23639,23714,23789,23864,23939,24014,24089,24164,24239
,24314,24389,24464,24521],
\[24578,24635,24710,24785,24860,24935,25010,25085,25160
,25235,25310,25385,25460,25535,25610,25685,25760,25835
,25910,25985,26060,26135,26192],
\[26249,26306,26399,26474,26549,26887,27079,27246,27401
,27476,27551,27626,27798,27873,28021,28095,28170,28245
,28320,28395,28470,28545,28620,28677],
\[28734,28791,28866,28941,29136,29211,29286,29361,29479
,29554,29629,29704,29779,29854,29929,30004,30079,30154
,30229,30304,30379,30454,30529,30604,30661],
\[30718,30775,30850,30925,31198,31273,31348,31423,31498
,31573,31648,31723,31798,31873,31948,32023,32098,32173
,32248,32323,32398,32473,32548,32623,32698,32755],
\[32812,32869,32944,33019,33333,33408,33483,33656,34055
,34463,34538,34613,34688,34763,34838,34913,34988,35063
,35146,35221,35296,35371,35446,35521,35596,35671,35728
],
\[35785,35842,35917,35992,36067,36412,36487,36562,36680
,36798,36873,36948,37023,37098,37173,37248,37323,37398
,37473,37548,37623,37698,37773,37848,37923,37998,38073
,38130],
\[38187,38244,38319,38804,38879,39269,39344,39518,39593
,39668,39743,39818,39893,39968,40043,40118,40193,40268
,40343,40418,40493,40568,40643,40718,40793,40868,40943
,41018,41075],
\[41132,41189,41264,41339,41414,41812,41887,41962,42106
,42181,42256,42331,42406,42481,42556,42631,42706,42781
,42856,42944,43019,43094,43169,43244,43319,43394,43469
,43544,43619,43676],
\[43733,43790,43865,43940,44015,44090,44165,44240,44315
,44390,44465,44540,44615,44690,44765,44840,44944,45019
,45094,45169,45244,45319,45394,45469,45544,45619,45694
,45769,45844,45919,45976],
\[46033,46090,46183,46258,46481,46556,46779,47056,47487
,47708,47845,48166,48391,48466,48541,48616,48693,48768
,48843,48918,48993,49070,49145,49220,49295,49370,49445
,49520,49595,49670,49745,49802],
\[49859,49916,49991,50066,50235,50310,50385,50460,50578
,50653,50798,50873,50948,51023,51098,51173,51248,51323
,51398,51473,51548,51623,51698,51773,51848,51923,51998
,52073,52148,52223,52298,52373,52430],
\[52487,52544,52619,52694,52769,52844,52919,52994,53069
,53144,53219,53294,53369,53444,53519,53594,53669,53902
,53977,54052,54127,54202,54277,54352,54427,54502,54577
,54652,54727,54802,54877,54952,55027,55084],
\[55141,55198,55273,55348,55423,57177,57252,60197,60272
,60347,60422,60497,60572,60647,60722,60797,63377,63452
,63527,63602,63677,63752,63827,63902,63977,64052,64127
,64202,65423,65498,65573,65648,65723,65798,65855],
\[65912,65969,66044,66630,66705,67163,67238,67594,67788
,67863,68545,69227,69618,70300,70674,71065,71747,72426
,74014,74089,74164,74239,74314,74389,74464,74539,74614
,74689,74764,74839,74914,74989,75064,75139,75214,75271
],
\[75328,75385,75460,75535,75610,75685,75760,75835,75910
,75985,76060,76135,76210,76285,76360,76435,76510,76585
,76660,76735,76810,76885,76960,77035,77110,77185,77260
,77383,77458,77533,77608,77683,77758,77833,77908,77983
,78040],
\[78097,78154,78229,78304,78379,78454,78704,78779,78933
,79297,79779,79854,80106,80181,80256,80331,80406,80481
,80556,80631,80706,80781,80856,80931,81006,81081,81156
,81231,81308,81383,81458,81533,81608,81683,81758,81833
,81908,81965],
\[82022,82079,82154,82229,82304,82379,82454,82529,82604
,82679,82794,82869,83128,83280,83355,83430,83505,83580
,83655,83730,83805,83880,83955,84030,84105,84180,84255
,84330,84405,85275,85350,85425,85500,85575,85650,85725
,85800,85875,85932],
\[85989,86046,86139,86214,86423,86796,86871,86946,87021
,87096,87255,87410,87485,87560,87635,87710,87785,87860
,87935,88010,88185,88260,88335,88410,88485,88560,88635
,88710,88785,88860,89750,89825,89900,89975,90050,90125
,90200,90275,90350,90407],
\[90464,90521,90596,90671,90746,90864,90939,91014,91089
,91164,91239,91314,91389,91464,91539,91614,91689,91764
,91839,91914,91989,92064,92139,92214,92289,92364,92439
,92514,92589,92664,92739,93649,93724,93799,93874,93949
,94024,94099,94174,94249,94306],
\[94363,94420,94495,94570,94791,95311,95532,95607,95682
,95757,95832,95907,95982,96057,96132,96207,96282,96357
,96432,96507,96582,96657,96732,96807,96882,96957,97032
,97107,97182,97257,97332,97407,97482,97557,97632,97707
,97829,97904,98026,98101,98176,98233],
\[98290,98347,98422,98497,98572,98647,98722,98968,99043
,99118,99193,99268,99343,99418,99493,99568,99643,99718
,99793,99868,99943,100018,100093,100168,100243,100318,100393
,100468,100543,100618,100693,100768,100843,100918,100993,101068
,101224,101299,101374,101449,101524,101599,101656],
\[101713,101770,101845,101920,101995,102070,102145,102220,102295
,102370,102445,102520,102595,102670,102745,102820,102895,102970
,103045,103120,103195,103270,103345,103420,103495,103570,103645
,103720,103795,103870,103945,104020,104095,104170,104245,104320
,104395,104470,104585,104660,104735,104810,104885,104942],
\[104999,105056,105131,105206,105281,105563,105638,105713,105788
,105863,105938,106013,106088,106163,106238,106313,106388,106463
,106538,106613,106688,106763,106838,106913,106988,107063,107138
,107213,107288,107363,107438,107513,107588,107663,107738,107813
,107888,107963,108038,108113,108188,108263,108338,108413,108470
],
\[108527,108584,108659,108734,108809,109369,109444,109519,109594
,109669,109744,109819,109894,109969,110044,110119,110194,110269
,110344,110419,110494,110569,110644,110719,110794,110869,110944
,111019,111094,111169,111244,111319,111394,111469,111544,111619
,111694,111769,111844,111919,111994,112069,112144,112219,112294
,112351],
\[112408,112465,112540,112615,112690,113258,113333,113408,113483
,113558,113633,113708,113783,113858,113933,114008,114083,114158
,114233,114308,114383,114458,114533,114608,114683,114758,114833
,114908,114983,115058,115133,115208,115283,115358,115433,115508
,115583,115658,115733,115808,115883,115958,116033,116108,116183
,116258,116315],
\[116372,116429,116504,116579,117026,117651,118738,119096,119751
,120168,120451,120968,121625,122018,122449,122932,123407,124016
,124283,124966,125317,126066,126493,126870,127241,127480,127759
,127834,128348,128423,129053,129198,129793,130066,130441,130826
,131021,131304,131435,131698,131773,132040,132115,132313,132388
,132463,132538,132595],
\[132652,132709,132784,133151,133226,133301,133495,133570,133645
,133720,133795,133870,133985,134060,134135,134210,134285,134360
,134435,134510,134585,134660,134735,134810,134885,134960,135035
,135110,135185,135260,135335,135410,135485,135560,135635,135710
,135785,135860,135935,136010,136085,136160,136235,136310,136385
,136460,136535,136610,136667],
\[136724,136820,136952,137066,138233,138683,138832,138983,139097
,139329,139692,139806,140242,140433,140583,140697,141111,141225
,141339,141489,141603,141811,141925,142076,142190,142390,142541
,142655,142872,142986,143137,143251,143448,143562,143713,143827
,144006,144120,144393,144544,144658,144826,145807,145958,146072
,146186,146445,146562,146676,146772],
\[146868,146925,147194,147562,147637,147712,147787,147862,148014
,148089,148164,148239,148314,148389,148464,148616,148691,148847
,148922,148997,149072,149147,149299,149374,149526,149601,149676
,149751,149826,149901,149976,150051,150126,150201,150276,150428
,150503,150618,150693,150768,150843,150918,151030,151105,151180
,151255,151330,151405,151480,151555,151612],
\[151669,151726,151801,151876,151951,152569,152644,152719,152794
,152869,152944,153019,153094,153169,153284,153359,153434,153509
,153584,153736,153811,153963,154038,154190,154305,154380,154455
,154530,154682,154757,154909,154984,155136,155211,155363,155478
,155553,155628,155780,155855,155930,156082,156157,156232,156307
,156382,156457,156532,156607,156682,156757,156814],
\[156871,156928,157003,157078,157153,158348,159052,159127,159202
,159354,159429,159504,159579,159654,159729,159881,160033,160148
,160263,160338,160413,160528,160603,160678,160753,160905,161113
,161317,161392,161467,161542,161617,161732,161807,161922,161997
,162149,162224,162299,162374,162449,162524,162599,162674,163714
,163789,163864,163939,164014,164089,164164,164239,164296],
\[164353,164410,164485,164560,164635,165273,166021,166096,166171
,166246,166321,166396,166471,166546,166621,166696,166771,166846
,166998,167073,167148,167223,167375,167450,167525,167600,167675
,167789,167864,167939,168014,168089,168164,168239,168314,168466
,168541,168616,168691,168766,168841,168916,168991,169066,169141
,169216,169291,169366,169441,169516,169591,169666,169741,169798
],
\[169855,169912,169987,170062,170137,170212,170287,170362,170437
,170512,170711,170786,170861,170936,171011,171086,171198,171273
,171348,171423,171498,171573,171648,171800,171875,171987,172062
,172137,172212,172287,172362,172437,172512,172587,172739,172814
,172889,172964,173039,173114,173189,173264,173339,173414,173489
,173564,173639,173714,173789,173864,173939,174014,174089,174164
,174221],
\[174278,174335,174405,174480,174996,175655,176425,176500,176575
,176650,176725,176800,176875,176950,177025,177100,177175,177250
,177325,177400,177475,177550,177625,177700,177775,177850,177925
,178000,178075,178150,178225,178300,178375,178450,178525,178600
,178675,178750,178825,178900,178975,179050,179125,179200,179275
,179350,179425,179500,179575,179650,179725,179800,179875,179950
,180025,180082],
\[180139,180196,180271,180346,180847,180922,181108,181683,181835
,182079,182500,182652,182935,183134,183209,183360,183627,183702
,184072,184554,184929,185281,185674,186124,186461,186636,186711
,186786,186861,187120,187195,187402,187777,187892,188169,188523
,188632,188739,188918,189021,189096,189171,189268,189343,189436
,189527,189602,189745,189820,189895,190076,190151,190226,190345
,190521,190596,190653],
\[190710,190767,190842,190917,191446,191521,192315,192700,193038
,193113,193188,193302,193377,193452,193731,193928,194003,194078
,194153,194228,194303,194378,194625,194846,194921,195036,195111
,195186,195261,195336,195411,195486,195561,195636,195711,195786
,195861,195936,196011,196086,196161,196236,196403,196566,196641
,196716,196791,196866,196941,197016,197091,197168,197243,197318
,197393,197468,197543,197600],
\[197657,197714,197789,197864,197939,198629,199435,200361,200476
,200551,200626,200701,200776,200851,200926,201001,201076,201151
,201226,201301,201376,201451,201526,201601,201676,201751,201826
,201901,201976,202202,202422,202497,202572,202647,202722,202834
,202909,202984,203059,203134,203209,203284,203359,203471,203546
,203621,203696,203771,203846,203921,203996,204071,204146,204221
,204296,204371,204446,204521,204578],
\[204635,204692,204767,204842,205420,205495,205570,205645,206031
,206235,206619,206813,207023,207223,207298,207373,207448,207640
,207832,207907,207982,208057,208132,208401,208911,209262,209613
,209847,209922,209997,210111,210263,210375,210450,210562,210637
,210712,210787,210862,210937,211012,211087,211162,211237,211312
,211387,211462,211537,211612,211687,211799,211874,211949,212024
,212099,212174,212249,212324,212399,212456],
\[212513,212570,212645,212720,212795,212870,212945,213020,213095
,213210,213285,213360,213435,213510,213585,213697,213772,213847
,213922,214037,214112,214187,214302,214377,214492,214567,214642
,214757,214832,214907,214982,215057,215169,215244,215319,215431
,215506,215581,215696,215771,215846,215921,215996,216071,216146
,216221,216296,216371,216446,216521,216596,216671,216746,216858
,216933,217008,217083,217158,217233,217308,217365],
\[217422,217479,217554,217629,217903,218622,219465,219540,219615
,219767,219882,219957,220069,220181,220256,220449,220805,220880
,220955,221030,221105,221220,221295,221407,221519,221634,221709
,221784,221859,221934,222009,222138,222213,222288,222363,222438
,222513,222588,222663,222738,222813,222888,222963,223038,223113
,223188,223263,223338,223413,223488,223563,223638,223713,223788
,223863,223938,224013,224088,224163,224238,224313,224370],
\[224427,224484,224559,224634,224709,224784,224859,224971,225046
,225121,225196,225271,225346,225421,225496,226036,226621,226696
,227730,228432,228675,228750,228883,228958,232276,235662,235737
,236044,236119,236194,236269,240469,240614,244746,244891,245198
,245389,245590,249102,249303,249504,249579,249780,249855,250056
,250257,250458,250659,250860,251061,251136,251211,251286,251361
,251436,251511,251586,251661,251736,251811,251886,251961,252018
],
\[252075,252132,252202,252277,252527,253106,253318,254086,254635
,255174,255249,255961,256343,256772,257500,257872,257984,258181
,258378,258657,259184,259546,260653,261436,262967,264081,264766
,265509,265867,266725,266800,266875,271421,271496,271571,271646
,275408,275483,275558,275633,275708,275783,275858,275933,276008
,276083,276357,276432,276706,276781,276856,276931,277006,277081
,277156,277231,277306,277381,277456,277531,277606,277681,277756
,277813],
\[277870,277927,278002,278077,278152,278270,279148,279223,279298
,279373,279485,279560,279772,279986,280098,280210,280285,282558
,282670,282782,282894,282969,283044,283119,283352,283467,283542
,283617,283692,283767,283842,287934,288009,288121,288196,288308
,288383,288458,288570,288645,288720,288795,288870,288945,289020
,289095,289170,289245,289320,289395,289470,289545,289620,289695
,289770,289845,289920,289995,290995,291070,291145,291220,291295
,291370,291427],
\[291484,291541,291616,292074,292320,293078,293153,293228,293382
,293496,293717,293829,293904,293979,294093,294207,294282,294357
,294469,294544,294929,295484,295878,295953,296068,296143,296218
,296330,296405,296520,296595,297696,298237,298687,298762,298837
,298912,298987,299062,299137,299212,299287,299362,299437,299512
,299587,299662,299737,299812,299887,299962,300037,300112,300187
,300262,300337,300412,300487,300562,301581,301656,301731,301806
,301881,301956,302013],
\[302070,302127,302202,302277,302352,302427,303330,303445,303569
,303688,303763,303838,303913,304022,304171,304246,304321,304396
,304471,304546,304621,304736,304849,304964,305039,305151,305266
,305341,305416,305491,305566,305641,305754,305829,305941,306016
,306128,306203,306315,306390,306465,306540,306615,306690,306765
,306840,306915,306990,307065,307140,307215,307290,307365,307440
,307515,307590,307665,307740,309032,309107,309182,309257,309332
,309407,309482,309557,309614],
\[309671,309728,309803,309878,310520,311299,311374,311449,311524
,311599,311674,311749,311868,311987,312062,312137,312348,312533
,312645,312720,312795,312870,312945,313060,313209,313324,313399
,313511,313588,313666,313741,313816,313968,314083,314158,314270
,314345,314420,314495,314570,314645,314720,314795,314870,314945
,315020,315095,315170,315245,315320,315395,315470,315545,315620
,315695,315770,315845,315920,315995,316070,316145,316220,316295
,316370,316445,316520,316595,316652],
\[316709,316766,316841,316916,316991,317066,317141,317290,317365
,317440,317515,317627,317702,317777,317852,317927,318002,318077
,318152,318227,318302,318377,318590,318665,318740,318815,318893
,318968,319083,319158,319233,319345,319420,319495,319570,319645
,319757,319832,319907,319982,320057,320132,320207,320282,320357
,320432,320507,320582,320657,320732,320807,320882,320957,321032
,321107,321182,321257,321332,321407,321482,321557,321632,321707
,321782,321857,321932,322007,322082,322139],
\[322196,322253,322328,322403,322478,322553,323708,324172,324247
,324322,324397,324472,324690,324912,324987,325062,325137,325212
,325287,325362,325437,325512,325587,325662,325737,325812,325964
,326039,326117,326232,326307,326382,326457,326609,326684,326743
,326818,326893,326968,327043,327118,327193,327268,327343,327418
,327493,327568,327643,327718,327793,327868,327943,328018,328093
,328168,328243,328318,328393,328468,328543,328618,328693,328768
,329812,329887,329962,330037,330112,330187,330244],
\[330301,330358,330433,330508,330583,330658,330733,330848,330923
,330998,331073,331148,331223,331298,331373,331448,331523,331598
,331673,331748,331823,331898,331973,332048,332123,332198,332273
,332388,332463,332538,332613,332688,332799,332874,332949,333024
,333099,333174,333249,333324,333399,333474,333549,333624,333699
,333774,333849,333924,333999,334074,334149,334224,334299,334374
,334449,334524,334599,334674,334749,334824,334899,334974,335049
,335124,335199,335274,335349,335424,335499,335574,335631],
\[335688,335745,335817,336080,336486,336754,337030,337472,337919
,338513,339340,340134,340902,341862,343201,344165,344571,344839
,345100,345175,345438,345697,345772,345847,345922,345997,346072
,346147,346222,346374,346449,346508,346583,346658,346733,346808
,346883,346958,347033,347108,347183,347258,347333,347408,347483
,347558,347633,347708,347783,347858,347933,348008,348083,348158
,348233,348308,348383,348458,348533,348608,348683,348758,348833
,348908,348983,349058,349133,349208,349283,349358,349433,349490
],
\[349547,349604,349679,349754,349866,349941,350916,351031,351106
,351181,351256,351368,351443,351555,351630,351742,351817,351892
,351967,352042,352117,352192,352267,352342,352641,352936,353085
,353160,353235,353310,353385,353460,353535,353610,353685,353760
,353819,353894,353969,354044,354119,354194,354269,354344,354419
,354494,354569,354644,354719,354794,354869,354944,355019,355094
,355169,355244,355319,355394,355469,355544,355619,355694,355769
,355844,355919,355994,356069,356144,356219,356294,356369,356444
,356501],
\[356558,356615,356690,357196,357271,357346,357421,357535,357610
,358201,358605,358754,358829,358904,359016,359091,359203,359278
,359495,359818,360137,360249,360324,360399,360474,360586,360661
,360736,360811,360963,361022,361097,361172,361247,361306,361381
,361456,361531,361606,361681,361756,361831,361906,361981,362056
,362131,362206,362281,362356,362431,362506,362581,362656,362731
,362806,362881,362956,363031,363106,363181,363256,363331,363406
,363481,363556,363631,363706,363781,363856,363931,364006,364081
,364156,364213],
\[364270,364327,364402,364477,364893,365309,365384,365523,365942
,366017,366092,366167,366773,367381,367493,367568,367643,367865
,367940,368015,368090,368165,368240,368315,368390,368465,368540
,368615,368690,368765,368840,368915,368990,369065,369140,369215
,369290,369365,369440,369515,369590,369665,369740,369815,369890
,369965,370040,370115,370190,370265,370340,370415,370490,370565
,370674,370749,370824,370899,370974,371049,371124,371199,371274
,371349,371424,371499,371574,371649,371724,371799,371874,371949
,372024,372099,372156],
\[372213,372270,372345,372420,372649,372724,373336,373764,373988
,374403,374515,374737,374964,375188,375407,376036,376462,376537
,378486,379092,379204,381702,383442,383852,385594,387530,387605
,389548,390345,390404,391188,391263,391338,391397,391472,391547
,391622,391697,391772,391847,391922,391997,392072,392147,392222
,392297,392372,392447,392522,392597,392672,392747,392822,392897
,392972,393047,393122,393197,393272,393347,393422,393497,393572
,393647,393722,393797,393872,393947,394022,394097,394172,394247
,394322,394397,394472,394529],
\[394586,394643,394718,394793,395508,395623,396646,396758,396833
,396908,396983,397058,397133,397208,397320,397395,397470,397582
,397657,397732,397807,397882,397957,398032,398107,398222,398297
,398372,398487,398562,398637,398696,398771,398846,398921,398996
,399071,399146,399205,399280,399355,399430,399505,399580,399655
,399730,399805,399880,399955,400030,400105,400180,400255,400330
,400405,400480,400555,400630,400705,400780,400855,400930,401005
,401080,401155,401230,401305,401380,401455,401530,401605,401680
,401755,401830,401905,401980,402037],
\[402094,402151,402226,402301,402376,403284,404285,404360,404435
,404510,404585,404660,404905,405017,405092,405167,405279,405354
,405466,405541,405616,405691,405806,405921,405996,406071,406146
,406221,406299,406374,406449,406524,406599,406674,406749,406824
,406883,406958,407033,407108,407183,407258,407333,407408,407483
,407558,407633,407708,407783,407858,407933,408008,408083,408158
,408233,408308,408383,408458,408533,408608,408683,408758,408833
,408908,408983,409058,409133,409208,409283,409358,409433,409508
,409583,409658,409733,409808,409883,409940],
\[409997,410054,410129,410204,410279,411167,411242,411317,411392
,411467,411542,411617,411692,411767,411842,411917,411992,412067
,412142,412217,412292,412367,412442,412517,412592,412667,412742
,412817,412892,412967,413042,413117,413192,413267,413326,413401
,413476,413551,413626,413701,413776,413851,413926,414001,414076
,414151,414226,414301,414376,414451,414526,414601,414676,414751
,414826,414901,414976,415051,415126,415201,415276,415351,415426
,415501,415576,415651,415726,415801,415876,415951,416026,416101
,416176,416251,416326,416401,416476,416551,416608],
\[416665,416722,416794,416869,417134,418032,419487,419948,420412
,420843,421072,421874,422692,423352,423806,424038,424475,424702
,425327,425758,426185,427014,427441,427870,428102,428177,428252
,428367,428442,428517,428592,428651,428726,428801,428876,428951
,429026,429101,429176,429235,429310,429385,429460,429535,429610
,429685,429760,429835,429910,429985,430060,430135,430210,430285
,430360,430435,430510,430585,430660,430735,430810,430885,430960
,431035,431110,431185,431260,431335,431410,431499,431574,431649
,431724,431799,431874,431949,432024,432099,432174,432231],
\[432288,432345,432420,432495,432570,432645,433745,433820,433934
,434009,434084,434159,434274,434423,434535,434610,434685,434760
,434872,434947,435022,435551,435785,435860,436179,436294,436369
,436444,436519,436594,436705,436780,436855,436914,436989,437064
,437139,437198,437273,437348,437423,437498,437573,437648,437723
,437798,437873,437948,438023,438098,438173,438248,438323,438398
,438473,438548,438623,438698,438773,438848,438923,438998,439073
,439148,439223,439298,439373,439448,439523,439598,439673,439748
,439823,439898,439973,440048,440123,440198,440273,440348,440405
],
\[440462,440519,440594,441148,441223,442171,443253,443328,443443
,443518,443593,443708,443783,443895,443970,444045,444120,444195
,444270,444382,444457,444572,444647,444762,444837,444912,444987
,445062,445177,445252,445367,445442,445517,445592,445667,445742
,445817,445892,445967,446042,446117,446192,446267,446342,446417
,446492,446567,446642,446717,446792,446867,446942,447017,447092
,447167,447242,447317,447392,447467,447542,447617,447692,447767
,447842,447917,447992,448067,448142,448217,448292,448367,448442
,448517,448592,448667,448742,448817,448892,448967,449042,449117
,449174],
\[449231,449288,449363,449438,449513,449588,449663,449738,449813
,449928,450003,450078,450153,450228,450303,450378,450453,450528
,450603,450678,450753,450828,450943,451018,451093,451208,451267
,451342,451417,451492,451567,451642,451701,451776,451851,451926
,451985,452060,452135,452210,452285,452360,452435,452510,452585
,452660,452735,452810,452885,452960,453035,453110,453185,453260
,453335,453410,453485,453560,453635,453710,453785,453860,453935
,454010,454085,454160,454235,454310,454385,454460,454535,454610
,454685,454760,454835,454910,454985,455060,455135,455210,455285
,455360,455417],
\[455474,455531,455606,455681,456462,457402,457477,457552,458056
,458320,458820,458895,458970,459452,459932,460224,460299,460589
,461475,461720,462621,462773,462888,462946,463098,463173,463248
,463363,463422,463481,463556,463631,463706,463781,463856,463931
,464006,464081,464156,464231,464306,464365,464440,464515,464590
,464665,464740,464815,464890,464965,465040,465115,465190,465265
,465340,465415,465490,465565,465640,465715,465790,465865,465940
,466015,466090,466165,466240,466315,466390,466465,466540,466615
,466690,466765,466840,466915,466990,467065,467140,467215,467290
,467365,467440,467497],
\[467554,467611,467686,467761,467836,469073,469148,469223,469298
,469373,469448,469523,469598,469673,469785,469860,470239,470614
,470689,470764,470839,470991,471106,471181,471256,471331,471406
,471481,471556,471631,471706,471765,471840,471915,471990,472049
,472124,472199,472274,472333,472408,472483,472558,472633,472708
,472783,472858,472933,473008,473083,473158,473233,473308,473383
,473458,473533,473608,473683,473758,473833,473908,473983,474058
,474133,474208,474283,474358,474433,474508,474583,474658,474733
,474808,474883,474958,475033,475108,475183,475258,475333,475408
,475483,475558,475633,475690],
\[475747,475804,475879,475954,476029,476104,476563,477218,477293
,477368,477483,477558,477797,478036,478111,478186,478261,478373
,478825,479280,479395,479470,479545,479620,479732,479884,479943
,480095,480170,480245,480397,480472,480547,480622,480697,480772
,480847,480906,480981,481056,481131,481206,481281,481356,481431
,481506,481581,481656,481731,481806,481881,481956,482031,482106
,482181,482256,482331,482406,482481,482556,482631,482706,482781
,482856,482931,483006,483081,483156,483231,483306,483381,483456
,483531,483606,483681,483756,483831,483906,483981,484056,484131
,484206,484281,484356,484431,484488],
\[484545,484602,484677,484752,484827,484902,486044,487580,488046
,488121,488250,488325,488400,488475,488939,489403,489517,489592
,489667,489742,489854,490323,490792,490867,490942,491017,491092
,491167,491242,491301,491376,491451,491526,491601,491660,491735
,491810,491885,491960,492035,492110,492185,492260,492335,492410
,492485,492560,492635,492710,492785,492860,492935,493010,493085
,493160,493235,493310,493385,493460,493535,493610,493685,493760
,493835,493910,493985,494060,494135,494210,494285,494360,494435
,494510,494585,494660,494735,494810,494885,494960,495035,495110
,495185,495260,495335,495410,495485,495542],
\[495599,495656,495728,495803,495878,496164,497580,497962,498238
,498313,498388,498663,498738,498813,498888,498963,499038,499113
,499188,499300,500217,501001,502386,508206,508321,508468,508543
,508658,508733,508808,508883,508942,509017,509092,509167,509242
,509301,509376,509451,509526,509601,509676,509751,509810,509885
,509960,510035,510110,510185,510260,510335,510410,510485,510560
,510635,510710,510785,510860,510935,511010,511085,511160,511235
,511310,511385,511460,511535,511610,511685,511760,511835,511910
,511985,512060,512135,512210,512285,512360,512435,512510,512585
,512660,512735,512810,512885,512960,513035,513092],
\[513149,513206,513281,513356,513431,513506,514672,516046,516165
,516240,516315,516434,516509,516584,516659,516771,516846,516921
,517033,517108,517220,517295,517410,517485,517560,517635,517694
,517753,517905,517980,518055,518130,518205,518264,518339,518414
,518489,518564,518639,518714,518789,518848,518923,518998,519073
,519148,519223,519298,519373,519448,519523,519598,519673,519748
,519823,519898,519973,520048,520123,520198,520273,520348,520423
,520498,520573,520648,520723,520798,520873,520948,521023,521098
,521173,521248,521323,521398,521473,521548,521623,521698,521773
,521848,521923,521998,522073,522148,522223,522298,522355],
\[522412,522469,522544,523712,524300,524863,524938,525013,525127
,525393,526379,526875,527414,528143,529099,529828,530601,532491
,533034,537854,537929,538044,538119,538234,538309,538420,538495
,538570,538645,538704,538763,538838,538913,538988,539063,539122
,539197,539272,539347,539425,539500,539575,539650,539725,539800
,539875,539950,540025,540100,540175,540250,540325,540400,540475
,540550,540625,540700,540775,540850,540925,541000,541075,541150
,541225,541300,541375,541450,541525,541600,541675,541750,541825
,541900,541975,542050,542125,542200,542275,542350,542425,542500
,542575,542650,542725,542800,542875,542950,543025,543100,543157
],
\[543214,543271,543346,543421,543496,544504,545724,546026,546101
,546176,546251,546326,546602,546714,546826,546938,547050,547162
,550506,550581,550656,550731,550806,550958,551033,551108,551183
,551258,551333,551408,551483,551558,551617,551692,551767,551842
,551917,551992,552067,552142,559527,559602,559677,559752,559811
,559886,559961,560036,560111,560186,560261,560336,560411,560486
,560561,560636,560711,560786,560861,560936,561011,561086,561161
,561236,561311,561386,561461,561536,561611,561686,561761,561836
,561911,561986,562061,562136,562211,562286,562361,562436,562511
,562586,562661,562736,562811,562886,562961,563036,563111,563186
,563243],
\[563300,563357,563432,563507,563659,563734,563809,563884,563959
,564034,564109,564258,564362,564437,564512,564587,564662,564774
,564886,564998,565122,565197,565312,565427,565502,565561,565620
,565679,565754,565829,565904,565979,566054,566129,566188,566263
,566338,566413,566472,566547,566622,574228,574287,574362,574437
,574512,574587,574662,574737,574812,574887,574962,575037,575112
,575187,575262,575337,575412,575487,575562,575637,575712,575787
,575862,575937,576012,576087,576162,576237,576312,576387,576462
,576537,576612,576687,576762,576837,576912,576987,577062,577137
,577212,577287,577362,577437,577512,577587,577662,577737,577812
,577887,577944],
\[578001,578058,578133,578208,578283,579311,579386,579461,579536
,579611,579686,579761,579836,579911,580023,580513,581225,581300
,581449,581564,581639,581714,581789,581864,581939,582091,582166
,582241,582316,582375,582434,582509,582584,582659,582734,582809
,582884,582959,583034,583109,590614,590689,590764,590839,590914
,590989,591064,591139,591214,591289,591364,591439,591514,591589
,591664,591739,591814,591889,591964,592039,592114,592189,592264
,592339,592414,592489,592564,592639,592714,592789,592864,592939
,593014,593089,593164,593239,593314,593389,593464,593539,593614
,593689,593764,593839,593914,593989,594064,594139,594214,594289
,594364,594439,594496],
\[594553,594610,594685,594760,594835,595903,595978,596053,596128
,596203,596278,596353,596428,596503,596578,596653,596728,596803
,596878,596953,597028,597103,597178,597253,597328,597403,597478
,597553,597628,597703,597778,597853,597912,597987,598062,598137
,598212,598271,598346,598421,598496,598571,598646,598721,598796
,598871,598946,599021,599096,599171,599246,599321,599396,599471
,599546,599621,599696,599771,599846,599921,599996,600071,600146
,600221,600296,600371,600446,600521,600596,600671,600746,600821
,600896,600971,601046,601121,601196,601271,601346,601421,601496
,601571,601646,601721,601796,601871,601946,602021,602096,602171
,602246,602321,602396,602453],
\[602510,602567,602642,602717,602792,602867,602942,603222,603297
,603577,603652,603727,603997,604072,604147,604222,604334,604409
,604926,605382,605457,605516,605591,605706,605781,605840,605899
,605958,606017,606092,606167,606242,606317,606392,606451,606526
,606601,606676,606751,606810,606885,606960,607035,607110,607185
,607260,607319,607394,607469,607544,607619,607694,607769,607844
,607919,607994,608069,608144,608219,608294,608369,608444,608519
,608594,608669,608744,608819,608894,608969,609044,609119,609194
,609269,609344,609419,609494,609569,609644,609719,609794,609869
,609944,610019,610094,610169,610244,610319,610394,610469,610544
,610619,610694,610769,610844,610901],
\[610958,611015,611087,611162,611237,612767,613518,614277,615023
,615289,616005,616987,617532,618259,618992,619721,619987,620247
,620322,620677,620752,620827,620902,620977,621052,621127,621202
,621277,621352,621427,621486,621561,621636,621711,621786,621861
,621920,621995,622070,622145,622220,622295,622370,622445,622504
,622579,622654,622729,622804,622879,622954,623029,623104,623179
,623254,623329,623404,623479,623554,623629,623704,623779,623854
,623929,624004,624079,624154,624229,624304,624379,624454,624529
,624604,624679,624754,624829,624904,624979,625054,625129,625204
,625279,625354,625429,625504,625579,625654,625729,625804,625879
,625954,626029,626104,626179,626254,626311],
\[626368,626425,626500,626575,626650,626725,626800,626915,626990
,627065,627140,627215,627330,627405,627520,627635,627710,627785
,627860,627935,628010,628085,628160,628235,628310,628385,628460
,628535,628610,628685,628760,628835,628894,628953,629028,629103
,629178,629253,629312,629387,629462,629537,629596,629671,629746
,629821,629896,629971,630046,630121,630196,630271,630346,630421
,630496,630571,630646,630721,630796,630871,630946,631021,631096
,631171,631246,631321,631396,631471,631546,631621,631696,631771
,631846,631921,631996,632071,632146,632221,632296,632371,632446
,632521,632596,632671,632746,632821,632896,632971,633046,633121
,633196,633271,633346,633421,633496,633571,633628],
\[633685,633742,633817,633899,634510,635137,635255,636727,636802
,636877,636952,637027,637102,637390,637465,637540,637615,637690
,637765,637840,637915,637990,638065,638124,638183,638242,638301
,638360,638419,638494,638569,638644,638719,638794,638869,638928
,639003,639078,639153,639228,639303,639378,639453,639528,639603
,639678,639753,639812,639887,639962,640037,640112,640187,640262
,640337,640412,640487,640562,640637,640712,640787,640862,640937
,641012,641087,641162,641237,641312,641387,641462,641537,641612
,641687,641762,641837,641912,641987,642062,642137,642212,642287
,642362,642437,642512,642587,642662,642737,642812,642887,642962
,643037,643112,643187,643262,643337,643412,643487,643544],
\[643601,643658,643733,643808,643883,643958,644033,644108,644183
,644258,644603,644984,645059,645134,645209,645324,645399,645474
,645549,645624,645699,645774,645849,645924,645999,646074,646149
,646224,646299,646374,646433,646492,646567,646642,646717,646792
,646867,646926,647001,647076,647151,647210,647285,647360,647435
,647494,647569,647644,647719,647794,647869,647944,648019,648094
,648169,648244,648319,648394,648469,648544,648619,648694,648769
,648844,648919,648994,649069,649144,649219,649294,649369,649444
,649519,649594,649669,649744,649819,649894,649969,650044,650119
,650194,650269,650344,650419,650494,650569,650644,650719,650794
,650869,650944,651019,651094,651169,651244,651319,651394,651451
],
\[651508,651781,651856,651931,652415,652762,653318,653433,653717
,653991,654265,654377,654902,655177,655708,655988,656507,656787
,657553,657840,658847,663554,663824,663883,663942,664001,664060
,664119,664178,664237,664296,664355,664430,664489,664548,664607
,664666,664725,664800,664859,664918,664977,665052,665111,665170
,665229,665304,665363,665464,665539,665640,665715,665816,665891
,665992,666067,666168,666243,666344,666419,666520,666595,666696
,666771,666872,666947,667048,667123,667224,667299,667400,667475
,667576,667651,667752,667827,667928,668003,668104,668179,668280
,668355,668456,668531,668632,668707,668808,668883,668984,669059
,669160,669245,669346,669427,669502,669579,669656,669731,669806
,669863],
\[669920]];