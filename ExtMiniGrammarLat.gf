concrete ExtMiniGrammarLat of ExtMiniGrammar = open MiniResLat, Prelude, Predef, Coordination in {

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
     S   = Sentence ; 
     QS  = QSentence ; 
     CN  = CNoun;
  
     AP  = AdjectivePhrase;       
     NP  = NounPhrase ;
             
     VP  = VerbPhrase;
     
     Cl   = {s : {stress : ClauseStress; npstress : NPStress; vpstress : VPStress; advstress : AdvStress; q : Bool} =>  
               Tempus => Bool => Str};
              
     ClSlash = {cl : Cl; slashstress : {objstress : NPStress; vpstress : VPStress}}; 
     QCl  = {cl : {stress : ClauseStress;npstress : NPStress; vpstress : VPStress; advstress : AdvStress} => 
              Gender => Number => Tempus => Bool => Str};
     Det  = {s : Gender => Case => Str; n : Number; empty : Bool};
     Pron = {s : Case => Str ; a : Agreement} ;
     IP = IPron ; -- {s : Gender => Number => Case => Str}; 
     Pol  = Bool;
     Comp = {adv : {isFilled : Bool; value : Str};   -- TODO: Probably needs to be a Token, to pick out the first adv in the case of a question.
             cn  : {isFilled  : Bool; value : CNoun};
             np  : {isFilled  : Bool; value : NounPhrase};
             ap  : {isFilled  : Bool; value : AdjectivePhrase}};
           
     VPSlash = {v : Verb2; vpstress : VPStress; objstress : NPStress};

     ListAP  = {s : Case => Gender => Number => {first : Str; second : Str}};
     
     ListAdv = {first : Str; second : Str};
     
     ListNP = {s : Case => NPStress => {first : Str; second : Str}};
     
     ListS = {s : SentenceStress => {first: Str; second : Str}};
 --    ListNP  = {s : Case => NPStress => Tokens} ;
 --    ListS   = {};
 
 
 
     
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
    
    PPos = True;
    PNeg = False;
    
    and_Conj = {s = "et"};
    or_Conj  = {s = "aut"}; -- exclusive or 
    -- vel - inclusive or
      
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
      {g = n.g; s = \\cas,stress,num => 
        let str = n.s ! num ! cas in
          {s = str; firsttok = str; rest = ""}};
    
    UsePron p = 
      {     
      s = \\cas,stress => case <stress,cas> of {
         <AdjFirst,Nom> => {s = "";firsttok = ""; rest = ""}; 
         _              => let ps = p.s ! cas in {s = ps; firsttok = ps; rest = ""}};
      typ = NPPron;
      a   = p.a
      };
      
    UsePN pn  = {s = \\cas,stress => {s = pn.s ! cas; firsttok = pn.s ! cas; rest = ""}; 
                 a = Agr pn.g Sg Per3; 
                 typ = NPPN pn.typ};
    
      
      
   IndefArt = {s = \\_,_,_ => ""; empty = True};
   DefArt   = {s = \\_,_,_ => ""; empty = True}; 
    
  
    this_Quant = {s = \\num,cas => 
     
     case num of {
      Sg => 
       case cas of
        {
         Nom => genderTable "hic"   "haec" "hoc";
         Gen => genderTable "huius" "huius" "huius";
         Dat => genderTable "huic"  "huic" "huic";
         Ack => genderTable "hunc"  "hanc" "hoc";
         Abl => genderTable "hoc"   "hac" "hoc";
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
          s = \\cas,stress => 
                 let cns = (cn.s ! cas ! stress ! det.n ) ;
                     dets = det.s ! cn.g ! cas
                 in
                 {s = dets ++ cns.s;
                  firsttok = case det.empty of {True => cns.firsttok; False => dets}; 
                  rest     = case det.empty of {True => cns.rest; False => cns.s}};                              
           a = Agr cn.g det.n Per3;   
           typ = NPNoun
          };
          
    PositA a = {s = \\cas,gen,num => let st = (a.s)!gen!num!cas in
      {s = st; firsttok = st; rest = ""}} ;
      
    AdAP adv ap = {s =      
        \\g,n,c => let firsttok = adv.s;
                       rest     = ((ap.s)!g!n!c).s;
                       s        = firsttok ++ rest in
                    {s = s; firsttok = firsttok;rest = rest}
      };
    
    
    AdjCN ap cn = {
      s = \\cas,stress,num  => let adjs = (ap.s ! cas ! cn.g ! num) ;
                                   cns  =  cn.s ! cas ! stress ! num  in
                                chooseStressNP stress cns adjs;
      g = cn.g
      } ;
      
       
    UseV v = 
      {
        v     = v;   
        compl = dummyVPTable;
        s = v.inf 
      };
      
      
    AdvVP vp adv = 
       {
       v     = vp.v;
       compl = vp.compl ** 
                {adv = {isFilled = True;
                        value    = (vp.compl.adv.value) ++ adv.s
                            }
                };
       s = vp.s ++ adv.s
       };
                
    ComplVV vv vp = 
          {
          v = vv;
          compl = vp.compl ** 
            {vp = 
               {isFilled = True; 
                value = {inf = vp.v.inf ++ vp.s; 
                imp = \\num => nonExist; 
                s = \\m,t,n,p => 
                   {s = vp.v.inf ++ (vp.compl.vp.value.s ! m ! t ! n ! p) . s; 
                    firsttok =vp.v.inf;
                    rest = (vp.compl.vp.value.s ! m ! t ! n ! p) . s };
                                 
             }}};   
   
          s = vp.s ++ vv.inf --infinitive form  
          };
          
       
     ComplVS vs s = 
         {
          v     = vs.v;
          compl = dummyVPTable ** 
                    {s = {isFilled = True;
                          value    = {s = \\stress => vs.conj.s ! stress ++ s.s ! stress}}};    
          s = (s.s ! dummySentenceStress) ++ vs.v.inf};
          
      
     PredVP np vp = 
       {

         s = \\stress,t,b => 
         let 
             typ  =         np.typ;
   
             linnp  = (np.s ! Nom ! stress.npstress);
             agrnp  = np.a;
             linv      =  case np.a of {Agr _ n p => vp.v.s ! Ind ! t !  n ! p};
             vpcompl   =  case np.a of {Agr g n p =>  vp.compl.vp.value.s ! Ind ! t ! n ! p}; -- TODO modify mood
             scompl    = (vp.compl.s.value.s ! (clausestress2sentencestress stress)); -- str
             npcompl   = (vp.compl.np.value.s ! Ack ! stress.npstress); --tokens
             advcompl  = vp.compl.adv.value ; --str
             cncompl   = case np.a of {Agr g n p => (vp.compl.cn.value.s ! Nom ! stress.npstress ! n)} ;  --tokens
             apcompl   = case np.a of {Agr g n p => (vp.compl.ap.value.s ! Nom ! g ! n)} ;  -- tokens
                        
             linvp = lin_vp vp np.a stress t
          in 
          case stress.stress of {
             NPFirst => 
                case <b,stress.q> of {<False,False> => linnp.s ++ "non" ++ linvp.s;
                                      <True, False> => linnp.s ++ linvp.s;
                                      <False,True>  => "nonne" ++ linnp.s ++ linvp.s;
                                      <True,True>   => linnp.firsttok ++ linnp.rest ++ BIND ++ "ne" ++ linvp.s};
             VPFirst => 
                 case <b,stress.q> of {<False,False> => "non" ++ linvp.s ++ linnp.s;
                                       <True, False> => linvp.s ++ linnp.s;
                                       <False,True>  => "nonne" ++ linvp.s ++ linnp.s;
                                       <True,True>   => linvp.firsttok ++ BIND ++ "ne" ++ linvp.rest ++  linnp.s
                                       }}};
         
      
    CompNP np   = dummyCompTable ** {np = {isFilled = True; value = np}};
 
    CompAP ap   = dummyCompTable ** {ap = {isFilled = True; value = ap}};
                                    
    CompAdv adv = dummyCompTable ** {adv = {isFilled = True; value = adv.s}};
    
    CompCN cn   = dummyCompTable ** {cn =  {isFilled = True; value = cn};
                                     s  = (cn.s ! Nom ! NounFirst ! Sg).s};
                                     
    UseComp comp = 
              {
              v     = mkVBe;
              compl = dummyVPTable ** {np = comp.np};
              s =  "esse" 
              };
           
    UseCl tmp pol cl = {
      s = \\stress => cl.s ! (sentencestress2clausestress stress False) ! tmp ! pol} ;
         
    AdvS adv s = 
     {s = \\stress => case stress.advstress of 
       { AdvFirst => adv.s ++ s.s ! stress;
         AdvLast  => s.s ! stress }      
     };
     
     
    BaseAdv adv1 adv2 = {first = adv1.s; second = adv2.s};
    
    BaseAP ap1 ap2    = {s = \\cas,num,gen => 
                               {first = (ap1.s ! cas ! num ! gen).s;
                                second = (ap2.s ! cas ! num ! gen).s}};
                       
                       
-- {s : Case => NPStress => Tokens; a : Agreement; typ : NPType} ;         
    BaseNP np1 np2 = {s = \\cas,npstress =>
                         {first  = (np1.s ! cas ! npstress ).s;
                          second = (np2.s ! cas ! npstress ).s}};
                          
                          
    BaseS s1 s2 = {s = \\stress =>
                     {first  = s1.s ! stress;
                      second = s2.s ! stress}};
    
                   
    ConjAP conj listap = {s = \\cas,gen,num => let lap = listap.s ! cas ! gen ! num in
                         {firsttok = lap.first;
                          rest = conj.s ++ lap.second;
                          s    = lap.first ++ conj.s ++ lap.second
                          }};
                          
    ConjAdv conj listadv = {s = listadv.first ++ conj.s ++ listadv.second};
    
    ConjNP conj listnp = {s = \\cas,npstress => let lnp = listnp.s ! cas ! npstress in
                         {firsttok = lnp.first;
                          rest = conj.s ++ lnp.second;
                          s    = lnp.first ++ conj.s ++ lnp.second}; a = Agr Masc Pl Per3; typ = NPNoun };
                          --TODO: change gender to Fem when all female
                          
    ConjS conj lists = {s = \\stress => (lists.s!stress).first ++ conj.s ++ (lists.s!stress).second};
                         

    QuestVP ip vp = {cl = \\stress,gen,num,temp,_ => 
                            ip.s ! gen ! num ! Nom ++ (lin_vp vp (Agr gen num Per3) (stress**{q  = False}) temp).s};
                            
    QuestCl cl = {cl = \\stress,_,_,temp,b => 
      cl.s ! (sentencestress2clausestress stress False) ! temp ! b
    };
    
 oper --{s : Case => Gender => Number => Tokens};  
 

 
 lin_vp : VP -> Agreement -> ClStress -> Tempus -> Tokens =
         \vp,agr,stress,t -> 

       let
            linv      =  case agr of {Agr _ n p => vp.v.s ! Ind ! t !  n ! p};
            vpcompl   =  case agr of {Agr g n p =>  vp.compl.vp.value.s ! Ind ! t ! n ! p}; -- TODO modify mood
            scompl    = (vp.compl.s.value.s ! (clausestress2sentencestress stress)); -- str
            npcompl   = (vp.compl.np.value.s ! Ack ! stress.npstress); --tokens
            advcompl  = vp.compl.adv.value ; --str
            cncompl   = case agr of {Agr g n p => (vp.compl.cn.value.s ! Nom ! stress.npstress ! n)} ;  --tokens
            apcompl   = case agr of {Agr g n p => (vp.compl.ap.value.s ! Nom ! g ! n)} ;  -- tokens
            vptoks  =
             case <vp.compl.vp.isFilled,vp.compl.s.isFilled, vp.compl.np.isFilled, 
                   vp.compl.adv.isFilled,vp.compl.cn.isFilled>  of  
                 {<True,_,_,_,_>  => 
                     <vpcompl.firsttok, vpcompl.rest ++ scompl ++ npcompl.s ++ advcompl ++ cncompl.s ++ apcompl.s>;    
                  <False,True,_,_,_> => 
                     <scompl, npcompl.s ++ advcompl ++ cncompl.s ++ apcompl.s>;
                  <False,False,True,_,_>   => <npcompl.firsttok,npcompl.rest++advcompl ++ cncompl.s ++ apcompl.s>;
                  <False,False,False,True,_>     => <advcompl,  cncompl.s ++ apcompl.s>;
                  <False,False,False,False,True> => <cncompl.firsttok, cncompl.rest ++ apcompl.s>;
                  <_,_,_,_,False>    => <apcompl.firsttok,apcompl.rest> };
                    
             vps = vptoks.p1 ++ vptoks.p2
             
        in  case stress.vpstress of 
                     {VerbFirst => {firsttok = linv.s; 
                                    rest = vps; 
                                    s = linv.s ++ vps}; 
                      ObjFirst  => {firsttok = vptoks.p1; 
                                    rest = vptoks.p2 ++ linv.s; 
                                    s= vps ++ linv.s}};  
 
  dummyCompTable =
                  {
                   adv =  {isFilled    = False; value = ""};
                   st   =  "";
                   np  =  {isFilled    = False; value = dummyNP};
                   ap  =  {isFilled    = False; value = dummyAP};
                   cn  =  {isFilled    = False; value = dummyCN}};
                              
  dummyVPTable  =
                dummyCompTable ** {vp = {isFilled = False; value = dummyVerb};
                                   s  = {isFilled = False; value = dummySentence}} ;
              
        
   dummyAgr = Agr Fem Sg Per1;
   
   dummyCN       : CNoun = {s = \\_,_,_ => dummyTokens; g = Fem};
   dummySentence : Sentence =   {s = \\_ => ""}; 
   dummyNP       : NounPhrase            =   {s = \\_,_ => dummyTokens; a = dummyAgr; typ = NPNoun};
   dummyTokens   : Tokens = {s = ""; firsttok = ""; rest = ""};
   dummyVerb     : Verb = {inf = ""; imp = \\_=>""; s = \\_,_,_,_ => dummyTokens};
   dummyAP       : AdjectivePhrase = {s = \\_,_,_ => dummyTokens};
   
   dummySentenceStress : SentenceStress = 
           {stress = NPFirst; npstress = NounFirst; vpstress = VerbFirst; advstress = AdvFirst};
             
   genderTable : Str -> Str -> Str -> Gender => Str = 
     \s1,s2,s3 -> table {Masc => s1; Fem => s2; Neut => s3};

 
    clausestress2sentencestress : ClStress -> SentenceStress = \stress -> 
      {stress=stress.stress;npstress=stress.npstress;vpstress=stress.vpstress;advstress=stress.advstress};
      
    sentencestress2clausestress : SentenceStress -> Bool -> ClStress = \stress,b -> 
      {stress=stress.stress;npstress=stress.npstress;vpstress=stress.vpstress;advstress=stress.advstress;q = b};
    
       
   chooseStressNP : NPStress -> Tokens -> Tokens -> Tokens = 
             \stress,s1,s2 -> 
                case stress of {
                    NounFirst => {s = s1.s ++ s2.s; firsttok=s1.firsttok;rest = s1.rest++s2.s};
                    AdjFirst  => {s = s2.s ++ s1.s; firsttok=s2.firsttok;rest = s2.rest++s1.s}};
 
}
