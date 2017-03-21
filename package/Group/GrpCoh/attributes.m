freeze;

declare attributes 
                ModCoho: 
                gptype,
               modtype,
                module,
                    gr,
                    gf,
                 gftoG,
                   gpc,
                  ring,
                relpos,
                   dim,
                 invar,
                  mats,
                 imats,
                   cem,
                   csm,
        SplitExtension,
 SplitExtensionPermRep,
                nsgens,
                    Z0,
                    H0,
                Z0toH0,
                    Z1,
                    B1,
                    H1,
                Z1toH1,
                    Z2,
                Z2gens,
                    B2,
                    H2,
                Z2toH2,
	       QmodZH1,
	    QmodZinvar,
            QmodZtrans,
             QmodZemat,
               QmodZH2;
declare verbose ModCoho, 2;

declare attributes GrpFP:
                NormalForm,
                Projection,
                 Injection;

declare attributes GrpPC:
                Projection,
                 Injection,
                modrepinfo;

declare attributes GrpPerm:
                modrepinfo;

declare attributes GrpMat:
                modrepinfo;

declare attributes GrpGPC:
                Projection,
                 Injection;
