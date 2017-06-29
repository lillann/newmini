concrete ExtMiniGrammarLat of ExtMiniGrammar = open MiniResLat, Prelude, Predef in {


  lincat
  
     N   = Noun ;
     PN  = ProperName ;
     A   = Adjective ;
     V   = Verb;
     V2  = Verb2;
     VS  = SComplVerb; 
     Adv = Adverb ;
     Interj = Interjection ; 
     Prep = Preposition;
     AdA  = AdjA;
     
     Utt = SS;
     Conj = SS;
     
     Imp = {s : Number => Str};
     S  = {s : {stress : ClauseStress; npstress : NPStress; vpstress : VPStress} => Str};
     QS = {s : {stress : ClauseStress; npstress : NPStress; vpstress : VPStress} => Str};
     CN = {s : NPStress => Number => Case => {s : Str; firsttok : Str; rest : Str}; g : Gender};
     
     
     AP  = {s  : Gender => Number => Case => Tokens};   
     
     NP  = {s : NPStress => Case =>  Tokens; a : Agreement; typ : NPType} ;
     
     VP  = {v : GVerb; compl : {stress : VPStress; objstress : NPStress; q : Bool} => Mood => Tempus => Agreement => Tokens};
          
     Cl   = {s : {stress : ClauseStress; npstress : NPStress; vpstress : VPStress; q : Bool} => 
              Tempus => Bool => Tokens};
          
     QCl  = {q : Str; cl : {stress : ClauseStress; npstress : NPStress; vpstress : VPStress} 
               => Tempus => Bool => Str};
          
     Det  = {s : Gender => Case => Str; n : Number; empty : Bool};
    
     Pron = {s : Case => Str ; a : Agreement} ;
    
     Pol = {s : Str ; b : Bool} ;
     
     Comp  = {s  : NPStress => Gender => Number => Tokens};   
              
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
                                                                                          
   DetCN det cn = {
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
         
         a_Det     = {s = table {g => table {cas => "" }}; n = Sg; empty=True};
         the_Det   = {s = table {g => table {cas => ""} }; n = Sg; empty=True};  
         aPl_Det   = {s = table {g => table {cas => ""} }; n = Pl; empty=True};
         thePl_Det = {s = table {g => table {cas => ""} }; n = Pl; empty=True};
    
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
      
    CompAP ap = {s = \\stress,gen,num => (ap.s!gen!num!Nom)};
    CompNP np = {s = \\stress,gen,num => np.s ! stress ! Nom};
    CompAdv adv = {s = \\_,_,_ => {s = adv.s; firsttok = adv.s; rest = ""}} ;
    CompCN cn = {s = \\stress,gen,num => cn.s ! stress ! num ! Nom };
   
    
    UseComp comp = let be  = be_GVerb 
                   in
     {v     = be; 
      compl = \\stress,mood,temp,agr => 
         case agr of {Agr g n p => 
           
              let aps = comp.s ! stress.objstress ! g ! n ;
                  bes = be.s ! (Vf n p temp mood) in
              
              chooseStressVP stress.stress {s = bes; firsttok = bes; rest = ""} aps
        
        }};
    
    
    UseV v' = {
       v = verb2gverb v';
       compl = \\stress,m,t => table {Agr _ n p   => 
       
            let r = (v'.s ! m ! t !  n ! p) in
                                               {s = r; firsttok = r ; rest = ""}}};
                                               

    AdvVP vp adv = {v = vp.v; compl = \\stress,mood,t,a => 
        let vps = vp.compl!stress!mood!t!a in
        {s = adv.s ++ vps.s; firsttok = adv.s; rest = vps.s}};
   
      
    PredVP np vp = 
    {s = 
          \\stress,t,b => let 
                         typ  = np.typ;
                         subj = (np.s ! stress.npstress ! Nom)  ;
                         subjstressed = (np.s ! NounFirst ! Nom);
                        
                         pol  = case b of {False => "non"; True => ""};
                         vs   = (vp.compl ! {stress=stress.vpstress;objstress=stress.npstress;q=stress.q} ! Ind ! t ! np.a) 
                                        
                     in
                   
          case stress.stress of {
            NPFirst => case <stress.q,b> of {
                        <False,_>    => {s = subj.s ++ pol ++ vs.s; firsttok = ""; rest = "" };
                       
                        <True,True>  => {s = subjstressed.firsttok ++ BIND ++ "ne" ++ subj.rest ++ vs.s; firsttok = ""; rest = ""};
                        
   
                        <True,False>  => {s = "nonne" ++ subj.s ++ vs.s; firsttok = ""; rest = ""}};
            VPFirst => case <stress.q,b> of {
                        <False,_> => {s = pol ++ vs.s ++ subj.s ; firsttok = ""; rest = ""};
                        <True,True> => {s = vs.firsttok ++ BIND ++ "ne" ++ vs.rest ++ subj.s; firsttok=""; rest = ""};
                        <True,False> => {s = "nonne" ++ vs.s ++ subj.s; firsttok = ""; rest = ""
                        } }            
             }
                       };
                       
                            
     QuestCl cl = {
         q = ""; cl = \\stress,t,b => (cl.s ! {stress=stress.stress;npstress=stress.npstress;vpstress=stress.vpstress;q=True} ! t ! b).s};
       
       
  

    
  
  
--    UttS s = s ;
--    UttNP np = {s = (np.s ! Ack).s} ; -- 
    UttInterj i = {s = i.s ++ BIND ++ "!"} ;  
    
--    CNInterjSg cn = {s = (cn.s ! Sg ! Voc) . s};
--    CNInterjPl cn = {s = (cn.s ! Pl ! Voc) . s};
    
  
    UseCl tmp pol cl = {
      s = \\stress => 
         (cl.s ! {stress=stress.stress;npstress=stress.npstress;vpstress=stress.vpstress;q = False} ! tmp ! pol.b).s};
        
        
    UseQCl tmp pol qcl =  {
      s =  \\stress => qcl.q ++ (qcl.cl ! stress ! tmp ! pol.b) ++ BIND ++ "?"};
       
       
 



     
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
                                                           
                                                           
 



      
    
--      ImpVP vp = 
--        {s =  vp.v.imp};
        
  
      

   
  
      
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
    
 --   in_Prep   = {s = "in"; c = Abl; ctype = Pre }; -- concatfun = \_,st -> "in" ++ st } ;
  --  to_Prep   = {s = "ad"; c = Ack; Pre} --concatfun = \_,st -> s ++ st};
   -- on_Prep   = {s = "in"} ;
    
    with_Prep = {s = "cum"; c = Abl; ctype = Post}; 
  
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
      
  --  refl_Pron = {
  --    s = table {Nom => nonExist} ... 
  --   };
      
    CoordS conj a b = {s = a.s ++ conj.s ++ b.s} ;
    
    PPos  = {s = [] ; b = True} ;
    PNeg  = {s = [] ; b = False} ;

    and_Conj = {s = "et"} ;
    or_Conj = {s = "aut"} ;
    
   oper
   
      Tokens : Type = {s : Str;firsttok : Str;rest : Str};
   
   
      chooseStressVP : VPStress -> Tokens -> Tokens -> Tokens = 
         \stress,s1,s2 -> case stress of {
                              VerbFirst => {s = s1.s ++ s2.s;firsttok=s1.firsttok;rest = s1.rest++s2.s};
                              ObjFirst  => {s = s2.s ++ s1.s; firsttok=s2.firsttok;rest = s2.rest++s1.s}};
         
   
      chooseStressNP : NPStress -> Tokens -> Tokens -> Tokens = 
         \stress,s1,s2 -> case stress of {
                              NounFirst => {s = s1.s ++ s2.s;firsttok=s1.firsttok;rest = s1.rest++s2.s};
                              AdjFirst  => {s = s2.s ++ s1.s; firsttok=s2.firsttok;rest = s2.rest++s1.s}};
    
}
