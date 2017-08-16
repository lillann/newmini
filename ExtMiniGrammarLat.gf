concrete ExtMiniGrammarLat of ExtMiniGrammar = open MiniResLat, Prelude, Predef in {

  lincat
  
     N      = Noun ;
     PN     = ProperName ;
     A      = Adjective ;
     V      = Verb;
     VV     = Verb; 
     V2     = Verb2;
     VS     = SComplVerb; 
     Adv    = Adverb ;
     Interj = Interjection ; 
     Prep   = Preposition;
     AdA    = AdjA;
     Num    = Number;
     
     Utt  = SS;
     Conj = SS;
     
     Imp = {s : Number => Str; inf : Str};
     S   = {s : {stress : ClauseStress; npstress : NPStress; vpstress : VPStress} => Str};
     QS  = {s : {stress : ClauseStress; npstress : NPStress} => Gender => Number => Str};
     CN  = {s : NPStress => Number => Case => {s : Str; firsttok : Str; rest : Str}; g : Gender};
  
     AP  = {s  : Gender => Number => Case => Tokens};        
     NP  = {s : NPStress => Case => Tokens; a : Agreement; typ : NPType} ;
          
     VP  = {
            
            v : Verb;
            compl : {obj : NP ; adv : Adv; compl : S }; 
            imp : Number => Str; 
           };

     Cl   = {s : {stress : ClauseStress; npstress : NPStress; vpstress : VPStress; q : Bool} =>        
                 Tempus => Bool => Str};
              
     ClSlash = {cl : Cl; slashstress : {objstress : NPStress; vpstress : VPStress}}; 
     QCl  = {cl : {stress : ClauseStress;npstress : NPStress} => Gender => Number => Tempus => Bool => Str};
     Det  = {s : Gender => Case => Str; n : Number; empty : Bool};
     Pron = {s : Case => Str ; a : Agreement} ;
     IP = {s : Gender => Number => Case => Str}; 
     Pol  = Bool;
     Comp = {s  : Gender => Number => Tokens};   
          
     VPSlash = {v : Verb2; vpstress : VPStress; objstress : NPStress};
     
     Quant = Quantifier;
     Tense = MiniResLat.Tense;
     Ant   = Ante;
     Temp  = Tempus;
        
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
      
    NumSg    = Sg;
    NumPl    = Pl;  
      
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
         
    UseN n = 
      {g = n.g; s = \\stress,num,cas => 
        let str = n.s ! num ! cas in
          {s = str; firsttok = str; rest = ""}};
    
    UsePron p = 
      {     
      s = \\stress,cas => case <stress,cas> of {
         <AdjFirst,Nom> => {s = "";firsttok = ""; rest = ""}; 
         _              => let ps = p.s ! cas in {s = ps; firsttok = ps; rest = ""}};
      typ = NPPron;
      a   = p.a
      };
      
    UsePN pn  = {s = \\stress,cas => {s = pn.s ! cas; firsttok = pn.s ! cas; rest = ""}; 
                 a = Agr pn.g Sg Per3; 
                 typ = NPPN pn.typ};
    
      
      
   --   CN  = {s : NPStress => Number => Case => {s : Str; firsttok : Str; rest : Str}; g : Gender};
  --    NP  = {s : NPStress => Case => Tokens; a : Agreement; typ : NPType} ;
      
      
   IndefArt = {s = \\_,_,_ => ""; empty = True};
   DefArt   = {s = \\_,_,_ => ""; empty = True}; 
    
 -- {s : Num => Case => Gender => Str};
  
    
    
    this_Quant = {s = \\num,cas => 
     
     case num of {
      Sg => 
       case cas of
        {
         Nom => genderTable "hic" "haec" "hoc";
         Gen => genderTable "huius" "huius" "huius";
         Dat => genderTable "huic" "huic" "huic";
         Ack => genderTable "hunc" "hanc" "hoc";
         Abl => genderTable "hoc" "hac" "hoc";
         Voc => genderTable nonExist nonExist nonExist  
         };
      Pl => 
        case cas of
        {
         Nom => genderTable "hi" "hae" "hae";
         Gen => genderTable "horum" "harum" "horum";
         Dat => genderTable "his" "his" "his";
         Ack => genderTable "hos" "has" "haec";
         Abl => genderTable "his" "his" "his";
         Voc => genderTable nonExist nonExist nonExist
        
        }};
           
         empty = False
    };
     
    DetQuant quant num = 
     {s = \\g,cas => quant.s ! num ! cas ! g; 
      n = num; 
      empty = quant.empty};
      
    DetCN det cn = 
    
     {
          s = \\stress,cas => 
                 let cns = (cn.s ! stress ! det.n ! cas) ;
                     dets = det.s ! cn.g ! cas
                 in
                 {s = dets ++ cns.s;
                  firsttok = case det.empty of {True => cns.firsttok; False => dets}; 
                  rest = case det.empty of {True => cns.rest; False => cns.s}};                              
           a = Agr cn.g det.n Per3;   
           typ = NPNoun
          };
          
    PositA a = {s = \\gen,num,cas => let st = (a.s)!gen!num!cas in
      {s = st; firsttok = st; rest = ""}} ;
      
    AdAP adv ap = {s =      
        \\g,n,c => let firsttok = adv.s;
                       rest     = ((ap.s)!g!n!c).s;
                       s        = firsttok ++ rest in
                    {s = s; firsttok = firsttok;rest = rest}
      };
    
      
      
      -- CN  = {s : NPStress => Number => Case => {s : Str; firsttok : Str; rest : Str}; g : Gender};
      --   AP  = {s  : Gender => Number => Case => Tokens}; 
  
    AdjCN ap cn = {
      s = \\stress,num,cas  => let adjs = (ap.s ! cn.g ! num ! cas) ;
                                   cns  =  cn.s ! stress ! num ! cas in
                                chooseStressNP stress cns adjs;
      g = cn.g
      } ;
      
 
    UseV v = 
      {
      v     = v;   
      compl = {obj = nonExist; adv = nonExist; compl = nonExist};
      imp   = v.imp;
      s = v.s ! Ind ! Pres ! Sg ! Per3  -- to linearize vps (?)
    };
    
    CompNP np =   {s = \\_,_ => 
       case np.typ of {
            NPPron => (np.s ! NounFirst ! Nom); -- "Jag är jag" ? 
            _      => variants {
                       np.s ! NounFirst ! Nom
                       ;
                       np.s ! AdjFirst ! Nom 
                       }}};
                       
    CompAP ap =   {s = \\gen,num => (ap.s!gen!num!Nom)};
    
    

                                        
                                      
    CompAdv adv = {s = \\_,_ => {s = adv.s; firsttok = adv.s; rest = ""}} ;
    
    
    -- Cl   = {s : {stress : ClauseStress; npstress : NPStress; vpstress : VPStress; q : Bool} =>        
   --              Tempus => Bool => Str};
   --  NP  = {s : NPStress => Case => Tokens; a : Agreement; typ : NPType} ;
          
 --    VP  = {
  --          v : Verb;
  --          compl : {obj : NP ; adv : Adv; compl : S }; 
  --          imp : Number => Str; 
  --         };
  
 --  Verb : Type  = {inf : Str;  imp : Number => Str; s :  Mood => Tempus => Number => Person => Str}; 
 
 
 {-   
    PredVP np vp = 
       {s = 
         \\stress,t,b => 
           let 
               typ  =         np.typ;
               subj =         (np.s ! stress.npstress ! Nom)  ;
               subjstressed = (np.s ! NounFirst ! Nom);             
               pol  = case b of {False => "non"; True => ""};
            
               v           = (vp.v.s) ! Ind ! t ! case np.a of {Agr _ num p => num ! p};
               vs          = (vp.v.s) ! Ind ! t ! stress.vpstress ! stress.npstress ! np.a
                                        
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
-}  
    
    
    
      
 oper  
      
   Tokens : Type = {s : Str;firsttok : Str;rest : Str};
   
   genderTable : Str -> Str -> Str -> Gender => Str = 
     \s1,s2,s3 -> table {Masc => s1; Fem => s2; Neut => s3};
     
   chooseStressNP : NPStress -> Tokens -> Tokens -> Tokens = 
             \stress,s1,s2 -> 
                case stress of {
                    NounFirst => {s = s1.s ++ s2.s; firsttok=s1.firsttok;rest = s1.rest++s2.s};
                    AdjFirst  => {s = s2.s ++ s1.s; firsttok=s2.firsttok;rest = s2.rest++s1.s}};
 
}
