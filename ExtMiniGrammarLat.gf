concrete ExtMiniGrammarLat of ExtMiniGrammar = open MiniResLat, Prelude, Predef in {

  lincat
  
     N   = Noun ;
     PN  = ProperName ;
     A   = Adjective ;
     V   = Verb;
     VV  = Verb; -- V2;
     V2  = Verb2;
     VS  = SComplVerb; 
     Adv = Adverb ;
     Interj = Interjection ; 
     Prep = Preposition;
     AdA  = AdjA;
     
     Utt = SS;
     Conj = SS;
     
     Imp = {s : Number => Str; inf : Str};
     S  = {s : {stress : ClauseStress; npstress : NPStress} => Str};
     QS = {s : {stress : ClauseStress; npstress : NPStress} => Gender => Number => Str};
     CN = {s : NPStress => Number => Case => {s : Str; firsttok : Str; rest : Str}; g : Gender};
  
     AP  = {s  : Gender => Number => Case => Tokens};        
     NP  = {s : NPStress => Case =>  Tokens; a : Agreement; typ : NPType} ;
     VP   = {v : GVerb; compl : Mood => Tempus => Agreement => Tokens; imp : Number => Str; inf : Str};  
     
               
     Cl   = {s : {stress : ClauseStress; npstress : NPStress; q : Bool} =>        
              Tempus => Bool => Str};
              
     ClSlash = {cl : Cl; slashstress : {objstress : NPStress; vpstress : VPStress}}; 
     QCl  = {cl : {stress : ClauseStress;npstress : NPStress} => Gender => Number => Tempus => Bool => Str};
     Det  = {s : Gender => Case => Str; n : Number; empty : Bool};
     Pron = {s : Case => Str ; a : Agreement} ;
     IP = {s : Gender => Number => Case => Str}; 
     Pol  = Bool;
     Comp = {s  :Gender => Number => Tokens};   
          
     VPSlash = {v : Verb2; vpstress : VPStress; objstress : NPStress};
              
     Tense = MiniResLat.Tense;
     Ant = Ante;
     Temp = Tempus;
     
            
  lin
  
    TTAnt = \tense,ant -> case <tense,ant> of {
   
       <TPr,Sim>   => Pres;
       <TPr,Anter> => Perf;
       <TPa,Sim>   => Imperf;
       <TPa,Anter> => PluPerf
    
    };
      TPres = TPr;
      TPast = TPa;
      ASimul = Sim;
      AAnter = Anter;
      
      
   UseN n = {g = n.g; s = \\stress,num,cas => let str = n.s ! num ! cas in
                                       {s = str; firsttok = str; rest = ""}};
                                                                                          
   DetCN det cn = 
     
    {
         s = \\stress,cas => 
                let cns = (cn.s ! stress ! det.n ! cas) ;
                    dets = det.s ! cn.g ! cas
                in
                {s = dets ++  cns.s;
                 firsttok = case det.empty of {True => cns.firsttok; False => dets}; 
                 rest = case det.empty of {True => cns.rest; False => cns.s}};                              
          a = Agr cn.g det.n Per3;   
          typ = NPNoun
         };

   emptytable = {s = table {g => table {cas => "" }}; n = Sg; empty=True};

         
   a_Det     = emptytable;
   the_Det   = emptytable;  
   aPl_Det   = emptytable;
   thePl_Det = emptytable;
    
   every_Det = let tabl = mkA "omnis" "omne" Third in 
           {s = table { g => table {cas => tabl.s!g!Sg!cas} };
            n = Sg; empty=False};
       
   all_Det = let tabl = mkA "omnis" "omne" Third in 
           {s = table { g => table {cas => tabl.s!g!Pl!cas} };
            n = Pl;empty=False};
            
   MassNP cn = {
     s = \\stress,cas => let cns = cn.s !  stress ! Sg ! cas in 
                  {s = cns.s; firsttok = cns.firsttok; rest = cns.rest};
     a = Agr cn.g Sg Per3;
     typ = NPNoun
     } ;


   PositA a = {s = \\gen,num,cas => let st = (a.s)!gen!num!cas in
      {s = st; firsttok = st; rest = ""}} ;
   
   AdAP adv ap = {s =      
     \\g,n,c => let firsttok = adv.s;
                    rest     = ((ap.s)!g!n!c).s;
                    s        = firsttok ++ rest in
                 {s = s; firsttok = firsttok;rest = rest}
   };
        
        
   
   AdjCN ap cn = {
    s = \\stress,num,cas  => let adjs = (ap.s ! cn.g ! num ! cas) ;
                                 cns  =  cn.s ! stress ! num ! cas in
                              chooseStressNP stress cns adjs;
    g = cn.g
    } ;
   
    
    UsePN pn  = {s = \\stress,cas => {s = pn.s ! cas; firsttok = pn.s ! cas; rest = ""}; 
                 a = Agr pn.g Sg Per3; 
                 typ = NPPN pn.typ};
    
    UsePron p = 
      {     
      s = \\stress,cas => case <stress,cas> of {
         <AdjFirst,Nom> => {s = "";firsttok = ""; rest = ""}; 
         _              => {s = p.s ! cas; firsttok = p.s ! cas; rest = ""}};
      typ = NPPron;
      a   = p.a
      };
      
    CompAP ap =   {s = \\gen,num => (ap.s!gen!num!Nom)};
    
    
    CompNP np =   {s = \\_,_ => 
       case np.typ of {
            NPPron => (np.s ! NounFirst ! Nom); -- "Jag är jag" ? 
            _      => variants {
                       np.s ! NounFirst ! Nom
                       ;
                       np.s ! AdjFirst ! Nom 
                       }}};
                                        
                                      
    CompAdv adv = {s = \\_,_ => {s = adv.s; firsttok = adv.s; rest = ""}} ;
  
    CompCN cn =  {s = \\gen,num => 
    
    --- TODO: What about gender? Do they have to match ?
    -- e.g. Puella puer est. (Puella magnus/magna puer est)?
    -- 
      variants {
         (cn.s!NounFirst!num!Nom);
         (cn.s!AdjFirst!num!Nom)          
      }
    };  

    UseV v' = let gv = verb2gverb v' 
       in {
       v = gv; 
       compl = \\m,t => 
        table {Agr _ n p   => 
            let r = (v'.s ! m ! t !  n ! p) in
            {s = r; firsttok = r ; rest = ""}                         
     };
       imp = \\num => v'.imp ! num;
       inf = gv.s ! VInf 
     };
                                               
    --want to run
    -- ordföljd:
    -- volo currere (vellem currere)
    -- ... si currere vellem
    ComplVV vv vp = {
       v     = verb2gverb vv;
       compl = \\mood,t,a => case a of {Agr _ num per => 
                 let vvs = vv.s ! mood ! t ! num ! per in
                {s = vvs ++ vp.inf; firsttok = vvs; rest = vp.inf}};
       imp   = \\num => nonExist;
       inf   = vv.inf ++ vp.inf 
    };
    
    AdvVP vp adv = {
        v = vp.v; 
        compl = \\mood,t,a => 
          let vps = vp.compl!mood!t!a in
             {s = adv.s ++ vps.s; firsttok = adv.s; rest = vps.s};
        imp = \\num => adv.s ++ vp.imp ! num;
        inf = adv.s ++ vp.inf };
        
    PredVP np vp = 
    {s = 
      \\stress,t,b => 
        let 
            typ  = np.typ;
            subj = (np.s ! stress.npstress ! Nom)  ;
            subjstressed = (np.s ! NounFirst ! Nom);             
            pol  = case b of {False => "non"; True => ""};
            vs   = (vp.compl ! Ind ! t ! np.a) 
                                        
         in                  
        case stress.stress of {
            NPFirst => case <stress.q,b> of {
                <False,_>     => subj.s ++ pol ++ vs.s;            
                <True,True>   => subjstressed.firsttok ++ BIND ++ "ne" ++ subj.rest ++ vs.s;
                <True,False>  => "nonne" ++ subj.s ++ vs.s};
                        
            VPFirst => case <stress.q,b> of {
                <False,_> =>    pol ++ vs.s ++ subj.s;
                <True,True> =>  vs.firsttok ++ BIND ++ "ne" ++ vs.rest ++ subj.s;
                <True,False> => "nonne" ++ vs.s ++ subj.s
                        } }                     
                       };
  
   
     QuestVP ip vp = {
        cl = \\stress,gen,num,t,_ => 
                (ip.s ! gen ! num ! Nom ) ++ (vp.compl ! Ind ! t ! (Agr gen num Per3)).s
  
     }   ;     
                                     
    QuestCl cl =  { cl = \\stress,_,_,t,b => 
        (cl.s ! {stress=stress.stress;npstress=stress.npstress;q=True} ! t ! b)};

       
    UseCl tmp pol cl = {
      s = \\stress => 
         (cl.s ! {stress=stress.stress;npstress=stress.npstress;q = False} ! tmp ! pol)};
       
      
    UttAdv adv = adv;
     
    UttIAdv iadv = iadv;
      
    UttCN cn = {s = (cn.s ! npstressVariants!numberVariants!caseVariants).s};  
        
    UttAP ap = {s = (ap.s ! genderVariants ! numberVariants ! caseVariants ).s};
        
    UttImpPl pol imp = 
       case pol of {True   => {s = imp.s ! Pl};
                    False  => {s = "nolite" ++ imp.inf ++ BIND ++ "!"}}; 
                    
    UttImpSg pol imp = 
       case pol of {True   => {s = imp.s ! Sg};
                    False  => {s = "noli" ++ imp.inf ++ BIND ++ "!"}}; 

    UttQS qs = {s = qs.s ! {stress=clausestressVariants;npstress=npstressVariants} ! genderVariants ! numberVariants};
           
    UttVP vp = {s = (vp.compl ! moodVariants ! tempusVariants ! (Agr genderVariants numberVariants personVariants))  . s};  
    
    UttS s   =  {s = s.s ! {stress = clausestressVariants; npstress = npstressVariants}};
    
    UttNP np = -- let stress = variants {NounFirst;AdjFirst} in
       {s = variants{  (np.s ! npstressVariants ! caseVariants).s}};
                          
    UttInterj i = {s = i.s ++ BIND ++ "!"} ;  
    
    
    
    UseQCl tmp pol qcl =  {
      s =  \\stress,gen,num => (qcl.cl ! {stress = stress.stress;npstress=stress.npstress } ! gen ! num !  tmp ! pol) ++ BIND ++ "?"};
       
      
    SlashV2a v2 = {v = v2; objstress=variants {NounFirst;AdjFirst};vpstress= variants{VerbFirst;ObjFirst}};
    
    ComplSlash vps np =  let nps = (np.s ! vps.objstress ! Ack ) in -- "love it"
       let vp' = UseV vps.v in
       {v     = vp'.v;
        compl = \\mood,temp,agr => 
          let vpcompl = vp'.compl ! mood ! temp ! agr 
              
          in 
            chooseStressVP vps.vpstress vpcompl nps;
        imp = \\num => 
               case vps.vpstress of {
                  VerbFirst => vp'.imp ! num ++ nps.s ;
                  ObjFirst  => nps.s ++ vp'.imp ! num 
               };
        inf = case vps.vpstress of {VerbFirst => vp'.inf ++ nps.s;
                                    ObjFirst  => nps.s ++ vp'.inf
        
          
         }};


     SlashVP np vps = -- "(whom) he sees"
       let vp' = UseV vps.v in
       {cl = PredVP np vp'; slashstress =  {vpstress = vps.vpstress; objstress = vps.objstress}}; 
       
       
       
     QuestSlash ip cls =  -- "who does he see"
        {cl = \\stress,gen,num,temp,bool =>
             ip.s ! gen ! num ! Ack ++ cls.cl.s ! {stress =stress.stress;npstress=stress.npstress;q=False} ! temp ! bool};



 
         


     
--    SubjS subj s = {s = subj.s ++ s.s}; 
--    SSubjS s subj s2 = {s = s.s ++ subj.s ++ s2.s};




 --  ComplV2 v2 np = let v' = verb2gverb v2 in {
--     v =  v' ;
--    compl = \\m => table {t => table {Agr _ n p => {s = "";firsttok = "";}}}};
--  
    
    
    -- \\t => table {Agr _ n p => (np.s ! Ack ++ v'.s ! (Vf n p t)) ++ v2.c };
  --   } ;
      
  
    
--    ComplVS vs s = let v' = verb2gverb {inf = vs.inf; stem = vs.stem; s = vs.s; decl = vs.decl} in {
      
--       v       = v';
--       compl   = \\m => table {t => table { Agr g n p   => {s = vs.conj ++ s.s; 
--                                                           firsttok = v'.s ! (Vf n p t m) }}}};
                                                           
                                                           
 



      
    
     ImpVP vp = 
        {s =  \\num => vp.imp!num ++ BIND ++  "!"; vp.inf} ; -- inf should be nonExist for posse,volle etc..
        
  --QuestIAdv iadv cl = {q = iadv.s; cl = cl.s};   

{-      
  
    InPrepNP np = case np.typ of
       {NPPN Place => {s = (np.s ! Gen).s; } ; 
        NPPN _     => {s = nonExist};
        _          => {s = "in" ++ (np.s ! Abl).s }
        };  
        
    WithPrepNP np = { s = case np.typ of
      {NPPron => case np.a of 
                   {Agr _ _ Per3  => "cum" ++ (np.s ! Abl).s;
                   _             => (np.s ! Abl).s ++ BIND ++ "cum"};
       _      => "cum" ++ (np.s ! Abl).s}};  
     
 -}   
    
 
    with_Prep = {s = "cum"; c = Abl; ctype = Post}; 
  
    i_Pron = {
      s = makeCaseTable "ego" "mei" "mihi" "me" "me" nonExist;
      a = Agr Fem Sg Per1 
      } ;
    youSg_Pron = {
      s = makeCaseTable "tu" "tui" "tibi" "te" "te" nonExist;
      a = Agr Masc Sg Per2 
      } ;
      
    -- Note: ille/illa/illud ("that") can be used as 3rd person pronoun.
    he_Pron = {
      s = makeCaseTable "is" "eius" "ei" "eum" "eo" nonExist ; 
      a = Agr Masc Sg Per3 
      } ;
    she_Pron = {
      s = makeCaseTable "ea" "eius" "ei" "eam" "ea" nonExist ; 
      a = Agr Fem Sg Per3 
      } ;
    we_Pron = {
       s = makeCaseTable "nos" "nostri" "nobis" "nos" "nobis" nonExist ; 
      a = Agr Masc Pl Per1  
      } ;
    youPl_Pron = {
       s = makeCaseTable "vos" "vestri" "vobis" "vos" "vobis" nonExist ; 
      a = Agr Masc Pl Per2 
      } ;
    they_Pron = {
      s = makeCaseTable "ii" "eorum" "iis" "eos" "iis" nonExist ; 
      a = Agr Masc Pl Per3 
      } ;
      

    who_IP  = {s = \\gen,num,cas => 
        let
           pickW : Str -> Str -> Str -> Str -> Str -> Str -> Str = 
            \s1,s2,s3,s4,s5,s6 -> 
             case gen of {Masc => case num of {Sg => s1; Pl => s4};
                          Fem  => case num of {Sg => s2; Pl => s5};
                          Neut => case num of {Sg => s3; Pl => s6}} in
          case cas of {Nom => pickW "qui" "quae" "quod" "qui" "quae" "quae";
                       Ack => pickW "quem" "quad" "quod" "quos" "quas" "quae";
                       _   => nonExist -- we don't need other cases yet.
                       
   }};    


    CoordS conj a b = {s = a.s ++ conj.s ++ b.s} ;
    
    PPos  = True ;
    PNeg  = False ;

    and_Conj = {s = "et"} ;
    or_Conj = {s = "aut"} ;
    
   oper
   
      Tokens : Type = {s : Str;firsttok : Str;rest : Str};
   
      chooseStressVP : VPStress -> Tokens -> Tokens -> Tokens = 
         \stress,s1,s2 -> 
            case stress of {
               VerbFirst  => {s = s1.s ++ s2.s; firsttok= s1.firsttok;rest = s1.rest++s2.s};
               ObjFirst   => {s = s2.s ++ s1.s; firsttok=s2.firsttok; rest = s2.rest++s1.s}};
             
      chooseStressNP : NPStress -> Tokens -> Tokens -> Tokens = 
         \stress,s1,s2 -> 
            case stress of {
                NounFirst => {s = s1.s ++ s2.s;firsttok=s1.firsttok;rest = s1.rest++s2.s};
                AdjFirst  => {s = s2.s ++ s1.s; firsttok=s2.firsttok;rest = s2.rest++s1.s}};
    
}
