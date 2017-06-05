concrete MiniGrammarLat of MiniGrammar = open MiniResLat, Prelude in {


  lincat
  
     N   = Noun ;
     PN  = ProperName ;
		 A   = Adjective ;
		 V   = Verb;
		 V2  = Verb2;
		 Adv = Adverb ;
		 
		 CN  = Noun ;  --  : {s : Number => Case => Str; g : Gender};
		 
		 AP  = Adjective; -- : Gender => Number => Case => Str
 		 NP  = {s : Case =>  Str; a : Agreement; typ : NPType} ;
		 
		 Prep = Preposition;
		 
		 VP  = {v : GVerb; obj : Agreement => Str; compl : Str};
		 		 
		 Det  = {s : Gender => Case => Str; n : Number};
		 Cl   = {s : Bool => Str};
		 Pron = {s : Case => Str ; a : Agreement} ;
		
		 Pol = {s : Str ; b : Bool} ;
			 		 
	lin
    UttS s = s ;
    UttNP np = {s = np.s ! Ack} ;
		
    UsePresCl pol cl = {
      s = pol.s ++ cl.s ! pol.b
      } ;
			
    AdjCN ap cn = {
      s = table {n => table {c => ap.s ! cn.g ! n ! c  ++ cn.s ! n ! c}};
			g = cn.g
      } ;
			
    UseN n =
      n ;
			
		PositA a = a ;

		DetCN det cn = {s = table {cas => det.s ! cn.g ! cas ++  cn.s ! det.n ! cas};
		                a = Agr cn.g det.n Per3;
										typ = NPNoun};
										
		a_Det     = {s = table {g => table {cas => ""} }; n = Sg};
		the_Det   = {s = table {g => table {cas => ""} }; n = Sg};  
		aPl_Det   = {s = table {g => table {cas => ""} }; n = Pl};
		thePl_Det = {s = table {g => table {cas => ""} }; n = Pl};
		
		every_Det = let tabl = mkA "omnis" "omne" Third in 
		  {s = table { g => table {cas => tabl.s!g!Sg!cas} };
			 n = Sg};
			 
		all_Det = let tabl = mkA "omnis" "omne" Third in 
		  {s = table { g => table {cas => tabl.s!g!Pl!cas} };
			 n = Pl};
		
		
	--	mkA "omnis" "omne" 
		
--		Third (Gender => Number => Case => String)
	--	{s = table {g => "omnis"; n }-- {s = "every" ; n = Sg} ;
		
		UsePN pn  = {s = pn.s; a = Agr pn.g Sg Per3; typ = NPPN pn.typ};
    UsePron p = {s = table {Nom => "";
		                        cas => p.s ! cas};
		             a = p.a;
								 typ = NPPron} ;
				
    MassNP cn = {
      s = table {cas => cn.s ! Sg ! cas };
      a = Agr cn.g Sg Per3;
			typ = NPNoun
      } ;
			
			--Verb : Type = {inf : Str; s : Number => Person => Str};
		UseV v = {
		   v = verb2gverb v; 
			 obj = \\_ => [];
			 compl = ""};
	
    ComplV2 v2 np = {
      v =  verb2gverb v2 ;
      obj = \\_ => v2.c ++ np.s ! Ack;
			compl = ""
      } ;
			 
    PredVP np vp = 
      let 
        subj = np.s ! Nom ;
        obj  = vp.obj ! np.a ;
        verb =  agrV vp.v np.a ;
				compl = vp.compl
                  
      in {
        s = \\b => subj ++ vp.compl ++  case b of {False => "non"; True => ""} ++ obj ++ verb
      } ;
			
	    UseAP ap = {
	      v   = be_GVerb ;
	      obj = table {Agr g n p => ap.s ! g ! n ! Nom};
				compl = ""
	      } ;
				
    AdvVP vp adv =
      vp ** {compl = vp.compl ++ adv.s} ;
			
			

			
	
		InPrepNP np = case np.typ of
		   {NPPN Place => {s = np.s ! Gen; } ; 
        NPPN _     => {s = nonExist};
				_          => {s = "in" ++ np.s ! Abl }
				};	
				
		WithPrepNP np = { s = case np.typ of
		  {NPPron => case np.a of 
			             {Agr _ _ Per3 => "cum" ++ np.s ! Abl;
									 _             => np.s ! Abl ++ BIND ++ "cum"};
			 _      => "cum" ++ np.s ! Abl}};	
		 
		
		
 --   in_Prep   = {s = "in"; c = Abl; ctype = Pre }; -- concatfun = \_,st -> "in" ++ st } ;
	--	to_Prep   = {s = "ad"; c = Ack; Pre} --concatfun = \_,st -> s ++ st};
   -- on_Prep   = {s = "in"} ;
    
		with_Prep = {s = "cum"; c = Abl; ctype = Suff}; -- concatfun = \nptype,st -> case nptype of {NPPron => st + "cum" ; _ => "cum" ++ st}} ;
	
	
    i_Pron = {
      s = table {Nom => "ego" ; Ack => "me"; Gen => "mei"; Dat => "mihi"; Abl => "me"; Voc => nonExist};
      a = Agr Fem Sg Per1
      } ;
    youSg_Pron = {
      s = table {Nom => "tu" ; Ack => "te"; Gen => "tui"; Dat => "tibi"; Abl => "te"; Voc => nonExist};
      a = Agr Masc Sg Per2
      } ;
    he_Pron = {
      s = table {Nom => "is" ; Ack => "eum"; Gen => "eius"; Dat => "ei"; Abl => "eo"; Voc => nonExist};
      a = Agr Masc Sg Per3
      } ;
    she_Pron = {
      s = table {Nom => "ea" ; Ack => "eam"; Gen => "eius"; Dat => "ei"; Abl => "ea"; Voc => nonExist};
      a = Agr Fem Sg Per3
      } ;
    we_Pron = {
       s = table {Nom => "nos" ; Ack => "nos"; Gen => "nostri"; Dat => "nobis"; Abl => "nobis"; Voc => nonExist};
      a = Agr Masc Pl Per1
      } ;
    youPl_Pron = {
       s = table {Nom => "vos" ; Ack => "vos"; Gen => "vestri"; Dat => "vobis"; Abl => "vobis"; Voc => nonExist};
      a = Agr Masc Pl Per2
      } ;
    they_Pron = {
      s = table {Nom => "ii" ; Ack => "eos"; Gen => "eorum"; Dat => "iis"; Abl => "iis"; Voc => "?"};
      a = Agr Masc Pl Per3
      } ;
			
	--	refl_Pron = {
	--	  s = table {Nom => nonExist} ... 
	-- 	};
			
    CoordS conj a b = {s = a.s ++ conj.s ++ b.s} ;
    
    PPos  = {s = [] ; b = True} ;
    PNeg  = {s = [] ; b = False} ;

    and_Conj = {s = "et"} ;
    or_Conj = {s = "aut"} ;
		
}
