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
              
     ClSlash = {cl : Cl}; --  slashstress : {objstress : NPStress; vpstress : VPStress}}; 
     
     Subj  = Subjunction;
     IAdv = IAdverb;
     QCl  = {cl : {stress : ClauseStress;npstress : NPStress; vpstress : VPStress; advstress : AdvStress} => 
              Gender => Number => Tempus => Bool => Str};
     Det  = {s : Gender => Case => Str; n : Number; empty : Bool};
     Pron = {s : Case => Str ; a : Agreement} ;
     IP = IPron ;  
     Pol  = Bool;
     Comp = {adv : {isFilled : Bool; value : Str};   -- TODO: Probably needs to be a Token, to pick out the first adv in the case of a question.
             cn  : {isFilled  : Bool; value : CNoun}; 
             np  : {isFilled  : Bool; value : NounPhrase};
             ap  : {isFilled  : Bool; value : AdjectivePhrase}};
           
     VPSlash = VerbPhrase;

     ListAP  = {s : Case => Gender => Number => {first : Str; second : Str}};
     
     ListAdv = {first : Str; second : Str};
     
     ListNP = {s : Case => NPStress => {first : Str; second : Str}};
     
     ListS = {s : SentenceStress => {first: Str; second : Str}};
     
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
    
    who_IP = mkIPWho;   
    want_VV = mkVWant;
    can_VV = mkVCan;
    very_AdA   = mkAdjA "multum";
    
    because_Subj = mkSubj "quod" Sub;
    if_Subj = mkSubj "si" Ind;
    
    and_Conj = {s = "et"};
    or_Conj  = {s = "aut"}; -- exclusive or 
    -- vel - inclusive or
    
    when_IAdv = mkIAdv "quando";-- {s : "quando"}; -- interrogative : quando, relative : cum, ubi
    why_IAdv  = mkIAdv "cur"; -- {s = "cur"};
      
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
          {s = str; firsttok = str; rest = ""};
       hasAdj = False};
    
    UsePron p = 
      {     
      s = \\cas,stress => case <stress,cas> of {
      --   <AdjLast,Nom> => {s = "";firsttok = ""; rest = ""}; 
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
      g = cn.g;
      hasAdj = True
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
          
     ImpVP vp = {s = \\num => ((lin_vp vp (Agr Neut num Per3) (sentencestress2clausestress dummySentenceStress False)  Pres  VImp ).s);
                 inf = vp.v.inf };
          
      
     PredVP np vp = 
       {
         s = \\stress,t,b => 
         let 
             typ  =         np.typ;   
             linnp  = (np.s ! Nom ! stress.npstress);
             linvp = lin_vp vp np.a stress t VTempus
          in 
          case stress.stress of {
             NPFirst => 
                case <b,stress.q> of {<False,False> => linnp.s ++ "non" ++ linvp.s;
                                      <True, False> => linnp.s ++ linvp.s;
                                      <False,True>  => "nonne" ++ linnp.s ++ linvp.s;
                                      <True,True>   => case typ of {NPPron => linvp.firsttok ++ BIND ++ "ne" ++ linvp.rest;
                                                                    _      =>
                                                                               linnp.firsttok ++ BIND ++ "ne" ++  linnp.rest ++ linvp.s}};
             VPFirst => 
                 case <b,stress.q> of {<False,False> => "non" ++ linvp.s ++ linnp.s;
                                       <True, False> => linvp.s ++ linnp.s;
                                       <False,True>  => "nonne" ++ linvp.s ++ linnp.s;
                                       <True,True>   => linvp.firsttok ++ BIND ++ "ne" ++ linvp.rest ++  linnp.s
                                       }}};

    SlashVP np vpslash = {cl = PredVP np vpslash}; 
            
    QuestSlash ip clslash = {cl = \\stress,gen,num,temp,pol => 
       (ip.s ! gen ! num ! Ack) ++ clslash.cl.s ! (sentencestress2clausestress stress False) ! temp ! pol };
      
    CompNP np   = dummyCompTable ** {np = {isFilled = True; value = np}};
 
    CompAP ap   = dummyCompTable ** {ap = {isFilled = True; value = ap}};
                                    
    CompAdv adv = dummyCompTable ** {adv = {isFilled = True; value = adv.s}};
    
    CompCN cn   = dummyCompTable ** {cn =  {isFilled = True; value = cn};
                                     s  = (cn.s ! Nom ! NounFirst ! Sg).s;
                                     hasAdj = cn.hasAdj};
                                     
    UseComp comp = 
              {
              v     = mkVBe;
              compl = dummyVPTable ** 
                         {np = comp.np; ap = comp.ap; adv = comp.adv; cn = comp.cn};
              s =  "esse" 
              };
           
    UseCl tmp pol cl = {
      s = \\stress => cl.s ! (sentencestress2clausestress stress False) ! tmp ! pol} ;
      
    UseQCl tmp pol qcl = {
     s = \\stress,gen,num => qcl.cl ! stress ! gen ! num ! tmp ! pol
    };
      
        
    AdvS adv s = 
     {s = \\stress => case stress.advstress of 
       { AdvFirst => adv.s ++ s.s ! stress;
         AdvLast  => s.s ! stress;
         AdvMid   => nonExist };      
     };
     
     
    BaseAdv adv1 adv2 = {first = adv1.s; second = adv2.s};
    
    BaseAP ap1 ap2    = {s = \\cas,num,gen => 
                               {first = (ap1.s ! cas ! num ! gen).s;
                                second = (ap2.s ! cas ! num ! gen).s}};
                       
                       
      
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
                          s    = lnp.first ++ conj.s ++ lnp.second}; a = Agr Masc Pl Per3; typ = NPList };
                          --TODO: change gender to Fem when all female
                          
    ConjS conj lists = {s = \\stress => (lists.s!stress).first ++ conj.s ++ (lists.s!stress).second};
    
    SubjS subj s = {s = subj.s ++ s.s ! {stress = VPFirst; npstress = NounFirst; vpstress = ObjFirst; advstress = AdvFirst}};
   
    SSubjS  s1 subj s2 = {s = \\stress => s1.s!stress ++ subj.s ++ s2.s!stress};
    -- : S -> Subj -> S -> S ; 
    -- "i go home if she comes"
  
    SlashV2a v2 = {v = v2; compl = dummyVPTable; s = v2.inf};
    
    ComplSlash vps np = vps ** {compl = vps.compl ** {np = {isFilled = True; value = np}}};
                         

    QuestVP ip vp = {cl = \\stress,gen,num,temp,pol =>    --TODO add polarity to VP ?
                            ip.s ! gen ! num ! Nom ++ (lin_vp vp (Agr gen num Per3) (stress**{q  = True}) temp VTempus).s};
                            
    QuestIAdv iadv cl = {cl = \\stress,gen,num,temp,pol => 
     case <gen,num> of {
      <Fem,Sg> => 
      iadv.s ++ cl.s ! (sentencestress2clausestress stress False) ! temp ! pol;
      _ => nonExist}};
                            
    QuestCl cl = {cl = \\stress,gen,num,temp,pol => 
    case <gen,num> of -- gender and number have no meaning here
     {  <Fem,Sg> => 
      cl.s ! (sentencestress2clausestress stress True) ! temp ! pol;
      _       => nonExist} 
    };
    
    
    UttAP   ap = {s = (ap.s ! Ack ! Neut ! Sg).s};
    UttAdv adv = adv;
    UttCN cn   = {s = (cn.s ! Ack ! NounFirst ! Sg) . s};
    UttIAdv iadv = iadv;
    UttIP     ip = {s = ip.s ! Neut ! Sg ! Nom} ;
    UttImpPl pol imp = {s = case pol of {False => "nolite"  ++ imp.inf; _ => (imp.s ! Pl)}}; 
    UttImpSg pol imp = {s = case pol of {False => "noli"  ++ imp.inf; _ => (imp.s ! Sg)}}; 
    UttInterj i = i; 
    UttQS qs    = {s = qs.s ! dummySentenceStress !  Neut ! Sg};
    UttVP vp = {s = (lin_vp vp (Agr Neut Sg Per3) (sentencestress2clausestress dummySentenceStress False) Pres VInf).s};
    
  
 oper 
 
 lin_vp : VerbPhrase -> Agreement -> ClStress -> Tempus -> VForm ->  Tokens =
   \vp,agr,stress,t,vf -> 
  
     let exists : Bool =  -- weeds out duplicate table entries.
        case <vp.compl.vp.isFilled,stress.vpstress> of 
           { <False,ObjFirst> => False;
             _                => 
                case <vp.compl.s.isFilled,stress.stress> of {
               --    <False,NPFirst> => False; -- include all because clausestress is used when building the clause (np + vp)
                   _               => 
                      case <vp.compl.np.isFilled, stress.npstress> of {
                          <False,NounFirst> => False;
                          _                 => 
                            case <vp.compl.adv.isFilled,stress.advstress> of {
                               <False,AdvFirst | AdvMid > => False;
                               _                => 
                                 case <vp.compl.cn.isFilled, vp.compl.cn.value.hasAdj,stress.npstress> of {
                                     <True,False,NounFirst> => False;
                                     <False,_,NounFirst>    => False;
                                     _                      => True
                        
                                 }}}}}
      in case exists of {False => {firsttok = nonExist; rest = nonExist; s = nonExist};
                         _ => let
    
            linv      =  case agr of 
                          {Agr _ n p => case vf of 
                                       {VImp => {firsttok = vp.v.imp ! n; 
                                                 rest = ""; s = vp.v.imp ! n }; 
                                        VTempus => vp.v.s ! Ind ! t !  n ! p;
                                        VInf    => {firsttok = vp.v.inf; rest = ""; s = vp.v.inf}}};       
            vpcompl   =  case agr of {Agr g n p =>  vp.compl.vp.value.s ! Ind ! t ! n ! p};    -- same tempus as verb...
            scompl    =  vp.compl.s.value.s ! (clausestress2sentencestress stress); -- Str
            npcompl   =  (vp.compl.np.value.s ! Ack ! stress.npstress); --tokens
            advcompl  =  vp.compl.adv.value ; --str
            cncompl   =  case agr of {Agr g n p => 
                         (vp.compl.cn.value.s ! Nom ! stress.npstress ! n)} ;  --tokens
            apcompl   = case agr of {Agr g n p => (vp.compl.ap.value.s ! Nom ! g ! n)} ;  -- tokens
            
            filled    = <vp.compl.vp.isFilled,vp.compl.s.isFilled, vp.compl.np.isFilled,
                         vp.compl.cn.isFilled>;
                             
            vps : {firsttok : Str; rest : Str; s : Str} = 
                     let fr = firstAndRest filled vpcompl.s scompl npcompl.s cncompl.s apcompl.s  in
                     case <stress.advstress,vp.compl.adv.isFilled>  of 
                             
                      {
                      <_,False>       => {firsttok = fr.first; rest = fr.rest; s = fr.first ++ fr.rest};
                      <AdvFirst,True> => {firsttok = advcompl;
                                           rest     = fr.first ++ fr.rest; 
                                           s        = advcompl ++ fr.first ++ fr.rest   };
                       
                       <AdvMid,True>   => {firsttok = fr.first;
                                           rest     = advcompl ++ fr.rest;
                                           s        = fr.first ++ advcompl ++ fr.rest};
                       <AdvLast,True>  => {firsttok = fr.first;
                                           rest     = fr.rest ++ advcompl;
                                           s        = fr.first ++ fr.rest ++ advcompl}
                        } 
        in  case stress.vpstress of 
                     {VerbFirst => {firsttok = linv.s; 
                                    rest = vps.s; 
                                    s = linv.s ++ vps.s}; 
                                    
                      ObjFirst  => {firsttok = vps.firsttok;     
                                    rest = vps.rest ++ linv.s; 
                                    s= vps.s ++ linv.s}}};  
 
 
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
   dummyCN       : CNoun = {s = \\_,_,_ => dummyTokens; g = Fem; hasAdj = False};
   dummySentence : Sentence =   {s = \\_ => ""}; 
   dummyNP       : NounPhrase            =   {s = \\_,_ => dummyTokens; a = dummyAgr; typ = NPNoun};
   dummyTokens   : Tokens = {s = ""; firsttok = ""; rest = ""};
   dummyVerb     : Verb = {inf = ""; imp = \\_=>""; s = \\_,_,_,_ => dummyTokens};
   dummyAP       : AdjectivePhrase = {s = \\_,_,_ => dummyTokens};

     
   firstAndRest : {p1:Bool;p2:Bool;p3:Bool;p4:Bool} -> Str -> Str -> Str -> Str -> Str -> {first : Str; rest : Str} = 
     \filled,s1,s2,s3,s4,s5 -> case filled.p1 of 
         {False => case filled.p2 of 
             {False => case filled.p3 of 
                   {False => case filled.p4 of 
                        {False => {first = s5; rest = ""};
                         _  => {first = s4; rest =  s5}};
                     _  => {first = s3; rest = s4 ++ s5}};
               _  => {first = s2; rest =  s3 ++ s4 ++ s5}};
           _  => {first = s1; rest = s2 ++ s3 ++ s4 ++ s5}};                         
   
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
