resource MiniResLat = open Prelude,Predef in {


param

  Number = Sg | Pl ;
  Case = Nom | Gen | Dat | Ack | Abl | Voc ;
  Person = Per1 | Per2 | Per3 ;  
  Gender = Fem | Masc | Neut ;
  Declension = First | Second | Third | Fourth;
  
  PNType = Place | Name ; 
  
  ConcatType = Pre | Post;
  
  ComplType = CVP | CS | CAdv |  CNP | CAP | None; 
  
  NPType = NPPN PNType | NPPron | NPNoun ; 
  
--  VPType = VT | VST | VVT ; 
  
  VForm = VInf | Vf Number Person Tempus Mood ;  
  Tempus = Pres | Imperf  | Perf | PluPerf ; 
  
  Tense = TPr | TPa;    
  Ante  = Sim | Anter ; 
  Mood = Ind | Sub ; -- | Imp ; 
  
  NPStress     = NounFirst | AdjFirst ;    --equus magnus, magnus equus
  VPStress     = ObjFirst | VerbFirst ;    --
  
  AdvStress = AdvFirst | AdvLast ; 
  
  ClauseStress = NPFirst | VPFirst ; 
  

  Agreement = Agr Gender Number Person ; -- | Empty ;
  
oper
 
  caseVariants   = variants {Nom;Gen;Dat;Ack;Abl;Voc};
  personVariants = variants {Per1;Per2;Per3};
  genderVariants = variants {Fem;Masc;Neut};
  tempusVariants = variants {Pres;Imperf;Perf;PluPerf};
  moodVariants   = variants {Ind;Sub};
  numberVariants = variants {Sg;Pl};
  
  
  npstressVariants     = variants {NounFirst;AdjFirst};
  vpstressVariants     = variants {ObjFirst;VerbFirst};
  clausestressVariants = variants {NPFirst;VPFirst};
  
 SentenceStress : Type = {stress : ClauseStress; npstress : NPStress; vpstress : VPStress; advstress : AdvStress};
 ClStress       : Type = SentenceStress ** {q : Bool};
 NounPhrase     : Type = {s : Case => NPStress => Tokens; a : Agreement; typ : NPType} ;
 Sentence       : Type = {s : SentenceStress => Str};
 QSentence      : Type = {s : {stress : ClauseStress; npstress : NPStress} => Gender => Number => Str};
 AdjectivePhrase : Type = {s : Case => Gender => Number => Tokens};
 CNoun : Type = {s : Case => NPStress => Number => {s : Str; firsttok : Str; rest : Str}; g : Gender};
 
 IPron : Type = {s : Gender => Number => Case => Str}; 
 
 VerbPhrase : Type = {            
        v     : Verb; -- {inf : Str;  imp : Number => Str; s :  Mood => Tempus => Number => Person => Str};        
        compl : {vp  : {isFilled : Bool; value : Verb};
                          
                 s   : {isFilled : Bool; value : Sentence};
                 np  : {isFilled : Bool; value : NounPhrase};
                 adv : {isFilled : Bool; value : Str};   
                 cn  : {isFilled : Bool; value : CNoun};
                 ap  : {isFilled : Bool; value : AdjectivePhrase}};
              
     --   imp : Number => Str; 
         s : Str -- Mood => Tempus => Number => Person => Str
       };

 
 
 
  Subj : Type = {s : Str; m : Mood};

  Noun : Type = {s : Number => Case => Str; g : Gender};
  
  Preposition = {s : Str; c : Case; ctype : ConcatType}; 
  
  Adjective : Type = {s : Gender => Number => Case => Str};
  
  Verb : Type  = {inf : Str;  imp : Number => Str; s :  Mood => Tempus => Number => Person => Tokens}; 
  
  Verb2 : Type = {inf : Str;  imp : Number => Str; s :  Mood => Tempus => Number => Person => Tokens}; 
  
  Quantifier : Type = {s : Number => Case => Gender => Str; empty : Bool};
  
  SComplVerb : Type = {v : Verb; conj : Sentence};
  
  Adverb : Type = {s : Str};
  AdjA   : Type = {s : Str};
  IAdv   : Type = {s : Str};
  
  Interjection : Type = {s : Str};
      
  StemInfo : Type = {stem : Str; 
                     extraLetters : Number -> Case -> Str; 
                     changeSuffix : Number -> Case  -> Str -> Str
                    };
  
  VerbInfo : Type = {stem : Tempus => Str; 
                     mid : Str; 
                     d : Declension
                     };
                     
  Tokens : Type = {s : Str;firsttok : Str;rest : Str};
  
  Funtype  : Type = Number -> Case -> Str;
  ProperName : Type = {s : Case => Str; 
                       g : Gender; 
                       typ : PNType
                       };
  
  agrV : Verb -> Agreement ->  Mood -> Tempus -> Str = \v,a,m,t -> case a of {
    Agr _ n p  => (v.s ! m ! t ! n ! p ) . s
    } ;
    
 
  mkInterj : Str -> Interjection = \i -> {s = i};
  mkAdv : Str -> Adverb = \s -> {s = s} ;  
 -- mkAdA : Str -> Adverb = \s -> {s = s};  
  mkSubj : Str -> Mood -> Subj = \i,mood -> {s = i; m = mood};
  
  mkAdjA : Str -> AdjA = \s -> {s = s};
  
  mkIAdv : Str -> IAdv = \s -> {s = s};
  
  -- IP = {s : Gender => Number => Case => Str};
  --makeCaseTable : Str -> Str -> Str -> Str -> Str -> Str -> (Case => Str) = 
 --    \nom,gen,dat,ack,abl,voc -> 
  mkIPWho : IPron = 
    {s = \\gen,num =>
             case <gen,num> of 
                {<Neut,Sg> => makeCaseTable "quid" "cuius" "cui" "quid" "quo" nonExist;
                 <Neut,Pl> => makeCaseTable "quae" "quorum" "quibus" "quae" "quibus" nonExist;
                 <_,Sg>    => makeCaseTable "quis" "cuius" "cui" "quem" "quo" nonExist;
                 <Masc,Pl> => makeCaseTable "qui" "quorum" "quibus" "quos" "quibus" nonExist;
                 <Fem,Pl>  => makeCaseTable "quae" "quarum" "quibus" "quas" "quibus" nonExist}};
                 


  mkVBe : Verb = 
      let vinfo = 
           {stem : Tempus => Str =
                \\t => case t of {Pres => "e"; Imperf => "er";_ => "fu"};
                mid  = "s";
                d    = First}; 
          v     = mkVerb "esse" vinfo in
    {
    s = \\mood,temp,num,pers => 
            let conjendings = (pickEndings Sub Pres) ! num ! pers ;
                normal      = v.s ! mood ! temp ! num ! pers in
            let vb = 
            case <temp,mood> of {            
                    <Pres,Ind> => case <pers,num> of {
                                    <Per1,Sg> => "sum";
                                    <Per2,Sg> => "es";
                                    <Per1,Pl> => "sumus";
                                    <Per3,Pl> => "sunt";
                                    _         => normal.s};
                     <Pres,Sub> => "si" + conjendings;
                     <Imperf,Ind>  => vinfo.stem!temp + "a" +  conjendings;
                     <Imperf,Sub> => "esse" + conjendings;                     
                    _ => normal.s} in
             {firsttok = vb; rest = ""; s = vb};
    inf  = "esse";
    imp = table {Sg => "es"; Pl => "este"};
    };
   
  mkVWant : Verb =
        let vinfo = 
         {stem : Tempus => Str =
            \\t => case t of {Perf | PluPerf => "volu"; _ => "vol" }; 
            mid = "e";
            d = Third};
        v = mkVerb "velle" vinfo in
        {
      s = \\mood,temp,num,pers => 
              let subendings = (pickEndings Sub Pres) ! num ! pers ;
                  normal      = v.s ! mood ! temp ! num ! pers in
              let vb = case <temp,mood> of {            
                      <Pres,Ind> => case <pers,num> of {
                                      <Per2,Sg> => "vis";
                                      <Per3,Sg> => "vult";
                                      <Per1,Pl> => "volumus";
                                      <Per2,Pl> => "vultis";
                                      _         => normal.s};
                      <Pres,Sub>   => "veli" + subendings;
                      <Imperf,Sub> => "velle" + subendings;                     
                      _ => normal.s} in
               {firsttok = vb; rest = ""; s = vb};
      inf  = "volle";
      imp = \\num => nonExist;
      };  
      
  mkVCan : Verb = 
      let 
          beVerb = mkVBe.s;
          vinfo = 
               {stem : Tempus => Str =
                    \\t => case t of {Pres => "poss"; Imperf => "pot";_ => "potu"};
                    mid  = "";
                    d    = First}; 
          v     = mkVerb "posse" vinfo 
      in { 
       s = \\mood,temp,num,pers =>
          let beEndings =  (beVerb!mood!temp!num!pers) . s   ;
              vb   =
           case temp of 
            {Perf | PluPerf => (v.s ! mood ! temp ! num ! pers) .s ; 
             Pres => 
               case <pers,num,mood> of 
                  {<Per1,_,_> | <Per3,Pl,_> => "pos"; 
                   <_,_,Ind> => "pot"; 
                    _        => "pos"} + beEndings;      
             Imperf  => case mood of 
                  {Ind => "pot" +  beEndings; 
                   _   => "po" + drop 1 beEndings}} 
           in 
                                      {firsttok = vb; rest = ""; s = vb};
       inf = "posse";
       imp = \\num => nonExist;
      };
            
     
  mkV = overload 
   { mkV : Str -> Verb = \s -> 
       let vinfo = getVerbInfo s in mkVerb s vinfo;
     mkV : Str -> Declension -> Verb = \s,decl -> 
      let vinfo = getVerbInfo s decl in
        mkVerb s vinfo;
     mkV : Str -> Str -> Declension -> Verb = \inf,pstem,decl -> 
      let vinfo = getVerbInfo inf pstem decl in
        mkVerb inf vinfo};
        
                                                                 
  mkV2 = overload {
    mkV2 : Str -> Declension -> Verb2 = 
      \s,d -> mkV s d ;
    mkV2 : Str -> Str -> Declension -> Verb2 = 
      \s,p,d ->  mkV s p d ;
    mkV2 : Str -> Verb2 = 
      \s   -> mkV s 
  }; 
    
  mkVS = overload {
    mkVS : Str -> Str -> SComplVerb = 
      \s,c -> {v = (mkV s);conj = {s = \\stress => c}};
    mkVS : Str -> Str -> Str -> Declension -> SComplVerb =  
      \s,ps,c,decl ->{v =  (mkV s ps decl);conj = {s = \\stress => c}}
  }; 
  
  getVerbInfo = overload {
  getVerbInfo : Str -> Str -> Declension -> VerbInfo = getVerbInfo3;
  getVerbInfo : Str -> Declension -> VerbInfo = getVerbInfo2;
  getVerbInfo : Str -> VerbInfo = getVerbInfo1;
  };
    
  getVerbInfo3 : Str -> Str -> Declension -> VerbInfo = \s,pst,decl -> 
     let cstem = cutStem s decl in
         {stem = \\t => case t of {Perf | PluPerf => pst; _ => cstem.stem};
          mid = cstem.mid;
          d   = decl};
          
  getVerbInfo2 : Str -> Declension -> VerbInfo = \s,decl -> 
     let cstem = cutStem s decl in
        {stem = \\t => cstem.stem;
         mid = cstem.mid;
         d   = decl};
                                                   
  getVerbInfo1 : Str -> VerbInfo = \s -> 
    let cstem = cutStem s in
       {stem = \\t => case t of { Pres | Imperf => cstem.stem;
                                  _             => cstem.stem + cstem.perfmid};
        mid = cstem.mid;
        d   =  cstem.d};

  cutStem = overload {
    cutStem : Str -> Declension -> {stem:Str;mid:Str;d : Declension} = cutStem2;
    cutStem : Str -> {stem:Str;mid:Str;perfmid : Str;d : Declension} = cutStem1};
  
  cutStem2 : Str -> Declension -> {stem:Str;mid:Str;d : Declension} = \s,decl ->   
    case s of {
      lud + "ere" => 
         case decl of 
           {Third => {stem=lud;mid="i";perfmid=""; d = Third}; 
            _     => cutStem1 s};
      ven + "ire" => case decl of 
           {Third => {stem=ven;mid="i";perfmid=""; d = Third};
            _     => cutStem1 s}};
    
  cutStem1 : Str -> {stem:Str;mid:Str;perfmid : Str;d : Declension} = \s ->
    case s of {
      aud  + "ire"  =>  {stem=aud; mid="i"; perfmid = "iv";d = Fourth};
      terr + "ere"  =>  {stem=terr;mid="e"; perfmid = "u" ;d = Second};
      voc  + "are"  =>  {stem=voc; mid="a"; perfmid = "av";d = First}};
      
 

  -- irregular: dic/duc/fac/fer    
   
  presendings : Mood -> Number => Person => Str = \mood -> 
           table {Sg => table {Per1 => case mood of {Ind => "o"; Sub => "m"}; 
                               Per2 => "s"; 
                               Per3 => "t" };
                  Pl => table {Per1 => "mus"; 
                               Per2 => "tis"; 
                               Per3 => "nt"} };
                                                                     
  impendings  : Mood -> Number => Person => Str =  \mood ->
             \\n,p     => case mood of {Ind  => "ba";
                                        Sub => "re"} + (presendings Sub)!n!p;                                             
  pluperfendings  : Mood -> Number => Person => Str =  
    \mood -> \\n,p => 
       case mood of { Ind => "era"; Sub => "isse"} + (presendings Sub)!n!p;
            
  perfendings : Mood -> Number => Person => Str = \mood -> 
          case mood of {Sub => \\n,p => "eri" + (presendings mood)!n!p ;
                        Ind  =>
                          table {Sg => table {Per1 => "i"; 
                                              Per2 => "isti"; 
                                              Per3 => "it" };
                                 Pl => table {Per1 => "imus"; 
                                              Per2 => "istis"; 
                                              Per3 => "erunt"} }};
       
  pickEndings :  Mood -> Tempus -> Number => Person => Str = 
      \m,t -> case t of {Pres => presendings m;Imperf => impendings m; 
                         Perf => perfendings m; PluPerf => pluperfendings m};

      
  mkVerb : Str  -> VerbInfo  -> Verb = \inf,verbinfo -> 
  let                                              
           mid  = verbinfo.mid;   
         
         
           istem : Bool = case inf of {viv+"ere" => True; _ => False};                                            
           extraletters :  Tempus -> Number -> Person -> Mood -> Str = 
            \t,n,p,mood -> 
              let mid' = case <mid,verbinfo.d,mood,inf>  of {
                        --  <"e", Third,Sub>          => "a" ;
                          <"e", Third, Sub>           => "e";
                          <"i", Third, Sub> => if_then_Str istem "a" "ia";
                          <"i",Fourth, Sub> => "ia";
                          <"a",First,Sub>           => "e";
                          <"e",Second,Sub>          => "ea";
                        
                          _                          => mid} in
               case <t,n,p,verbinfo.d,mood> of 
                               { <Pres,Sg,Per1,First,Ind>          => "";
                                 <Pres,_,_,_,Sub>                 => mid';
                                 <Imperf,_,_,First,Ind>            => "a";
                                 <Imperf,_,_,Second | Third,Ind>   => "e";
                                 <Imperf,_,_,_,Ind>            => mid' + "e";
                                 <Imperf,_,_,_,Sub>           => if_then_Str istem "e" mid;
                                <Pres,Sg,Per1,Third,Ind>       => "";
                                <Pres,Pl,Per3,Third,Ind>       => "u";
                                <Pres,Pl,Per3,Fourth,Ind>      => "iu"; 
                                <Perf,_,_,_,_>               => "";
                                 <PluPerf,_,_,_,_>           => "";
                                _                          => mid}  ;
        
      in  
  
  {
    inf = inf;
    decl = verbinfo.d;
    stem = verbinfo.stem!Pres;
    imp = \\num => 
      verbinfo.stem ! Pres + (imperativeEndings verbinfo.d num);
    s = \\mood,temp,num,pers =>
     let vb = (verbinfo.stem!temp) + extraletters temp num pers mood  + 
      ((pickEndings mood temp) ! num ! pers)   in {firsttok = vb; rest = ""; s = vb}   
  };
    
  imperativeEndings : Declension -> Number -> Str = \decl,num ->
    case <decl,num> of {
      <First,Sg>  => "a";
      <First,Pl>  => "ate";
      <Second,Sg> => "e";
      <Second,Pl> => "ete";
      <Third,Sg> => "e";
      <Third,Pl> => "ite";
      <Fourth,Sg> => "i";
      <Fourth,Pl> => "ite"}; 
      
  mkA = overload {
    mkA : Str -> Declension -> Adjective = mkAdj ;
    mkA : (mf, neut : Str) -> Declension -> Adjective = mkAdj2 ;
    mkA : (m,f,n : Str) -> Declension ->  Adjective = mkAdj3 ; 
    } ;
  
    mkAdj : Str -> Declension -> Adjective = 
      \adj,d -> mkAdj3 adj adj adj d;
    mkAdj2 : Str -> Str -> Declension -> Adjective = 
      \adj1,adj2,d ->  mkAdj3 adj1 adj1 adj2 d;
       
    mkAdj3 : Str -> Str -> Str ->  Declension -> Adjective = \adj,adj2,adj3,d ->  
      let
        genTable : Gender -> Number => Case => Str = \gender -> 
          let     
            theadj   = case gender of {Masc => adj; Fem => adj2; Neut => adj3};
            adjstem  = findStem theadj d gender;
              
            adjEndings : Number -> Case -> Str -> Str = \num,cas,s ->
              case <d,gender,num,cas> of {
          
                <Second,Masc,Sg,Voc> => s;
                <Third,Fem,Sg,Voc>  => adj;
                <Third,Neut,Sg,Voc> => adj3;
                <_,_,_,Voc>            => adjstem.stem + 
                     
                     nounEndings (case <gender,d> of {
                                     <Fem,Second> => First;
                                     _            => d}) gender num ! Voc; 
                              
                              
                <Second,Neut,Sg,Nom>   => adjstem.stem + "um"; -- for "niger" etc. -> nigrum
                <Second,Fem,Sg,Nom>    => adjstem.stem + "a";     
                <Third,_,Sg,Abl>       => adjstem.stem + "i";
                <Third,_,Pl,Gen>       => adjstem.stem + "ium";
                <Third,Neut,Pl,c>      => if_then_else Str (isAckNomOrVoc cas) (adjstem.stem + "ia") s;
                _              => s
                };           
                
            newSuffix : Number -> Case -> Str -> Str = \n,c,s -> 
               case gender of
                  {  Masc => adjstem.changeSuffix n c (adjEndings n c s);
                    
                   _    => adjEndings n c (adjstem.changeSuffix n c s)}; 
            newStem  =  {stem = adjstem.stem; extraLetters = adjstem.extraLetters;
                        changeSuffix = newSuffix} 
              
          in
            case d of {
             Third => case gender of { 
                      Masc => mkNounTable {s = adj;  steminfo = newStem;  decl = d; gen = gender};
                      Fem  => mkNounTable {s = adj2; steminfo = newStem; decl = d; gen = gender};
                      Neut => mkNounTable {s = adj3; steminfo = newStem; decl = d; gen = gender}};
             _ =>
               case gender of {
                      Fem => mkNounTable {s = adj; steminfo = newStem; decl = First; gen = gender};
                      _   => mkNounTable {s = adj; steminfo = newStem; decl = Second; gen = gender}                           
                      }  
            }                     
      in {
         s = table {gender => genTable gender}
      };
      
 isAckNomOrVoc : Case -> Bool = \cas -> case cas of {
    Voc => True;
    Ack => True;
    Nom => True;
    _   => False
    };
            
  mkPN : Str -> Declension -> Gender -> PNType -> ProperName  = \pn,d,g,pt -> 
  let pnparams = {s =  pn; steminfo = findStem pn d g ; decl = d; gen = g};
      ntable = mkNounTable pnparams in 
  {
      s = ntable!Sg;
      g = g;
      typ = pt
      };
      
  
  NParams  =  {s : Str; steminfo : StemInfo; decl : Declension; gen : Gender};
    
  mkNoun : Str -> Declension -> Gender -> Noun  = \n,d,g -> 
  let nparams = {s =  n; steminfo = findStem n d g ; decl = d; gen = g};
  s' = mkNounTable nparams in {
  s = s';
  g = g
  };
  
    
  nounEndings : Declension -> Gender -> Number -> Case => Str = \d,g,n ->  

    case d of {
    
      First   => 
          case n of { 
             Sg => makeCaseTable "a" "ae" "ae" "am" "a" "a"; 
             Pl => makeCaseTable "ae" "arum" "is" "as" "is" "ae"};
      Second  => 
          case n of { 
             Sg => 
              makeCaseTable 
                (case g of {Neut => "um"; _ => "us"}) "i" "o" "um" "o" (case g of {Neut => "um"; _ => "e"});
             Pl => case g of {                    
                      Neut =>  makeCaseTable "a" "orum" "is" "a" "is" "a";
                      _    =>  makeCaseTable "i" "orum" "is" "os" "is" "i"}
                    };
                    
      Third   =>  
           case n of {
              Sg =>  makeCaseTable "" "is" "i" "em" "e" "";
              Pl => case g of {
                      Neut =>  makeCaseTable "a" "um" "ibus" "a" "ibus" "a"; 
                      _    =>  makeCaseTable "es" "um" "ibus" "es" "ibus" "es"}
                    };                 
       Fourth  => 
            case g of {
               Neut => 
                 case n of {
                     Sg => makeCaseTable "u" "u" "ui" "u" "u" "";
                     Pl => makeCaseTable "ua" "uum" "ibus" "ua" "ibus" "ua"};
               _    => 
                  case n of {
                     Sg => makeCaseTable "us" "us" "ui" "um" "u" "us";
                     Pl => makeCaseTable "us" "uum" "ibus" "us" "ibus" "us"}
                    }};
                    
  makeCaseTable : Str -> Str -> Str -> Str -> Str -> Str -> (Case => Str) = 
     \nom,gen,dat,ack,abl,voc -> 
         table {Nom => nom;Gen => gen; Dat => dat; Ack => ack; Abl => abl; Voc => voc};
  
  mkNounTable : NParams -> Number => Case => Str = \np -> 
  
    let st         = (np.steminfo).stem;
        addfun     = (np.steminfo).extraLetters; 
        changesuff = (np.steminfo).changeSuffix; 
        -- removefun = (np.steminfo).removeLetters; 
        suffixes  = nounEndings np.decl np.gen in
  
         table { num => 
          table {cas => 
             changesuff num cas (st + addfun num cas + (suffixes num)!cas)}};
             
                      
                                         
  findStem : Str -> Declension -> Gender -> StemInfo = \s,d,g  ->    
    let 

      normal     : Funtype  = \_,_ -> "";
      normalsuff : Number -> Case -> Str -> Str  = \_,_,s -> s;
          
      change2NomForm : Number -> Case -> Str -> Str = \n,c,ns -> 
         case <n,c> of {
              <Sg,Nom> => s;
              <Sg,Voc> => s;
              <Sg,Ack> => case g of 
                             {Neut => s;
                                 _  => ns
                             };                           
              <Sg,_> => ns;
              _      => ns} ;
      
          
      um2ium : Funtype    =  \n,c -> case <n,c> of {
                             <Pl,Gen> => case g of {
                                            Neut => "";
                                            _    => "i"};
                             _        =>  ""};
                             
      i_stem : Funtype = \n,c -> case <n,c,g> of {
                                     <Sg,Abl,Neut> =>  "i";
                                     <Pl,Nom,Neut> => "i";
                                     <Pl,Gen,_> => "i";
                                     <Pl,Ack,Neut> => "i";
                                     <Pl,Voc,Neut> => "i";
                                     _             => ""  
                              };
      

      normalstem : Str -> StemInfo   = \st -> 
           {stem = st; extraLetters  = normal; changeSuffix = normalsuff};
      iumstem    : Str -> StemInfo   = \st -> 
           {stem = st; extraLetters = um2ium;  changeSuffix = normalsuff};

      thirdDeclstem : Str -> StemInfo = \st ->
           {stem = st; extraLetters = normal; changeSuffix = change2NomForm};
           
      thirdDecl_i_stem : Str -> StemInfo = \st ->
          {stem = st; extraLetters = i_stem; changeSuffix = change2NomForm};
           
      greek_i_stem  : Str -> StemInfo   = \st -> 
           {stem = st; extraLetters = normal;  
             changeSuffix = \n,c,s -> change2NomForm n c (
              case <n,c> of 
              {
                   <Sg,Ack> => case s of {
                                  s' + "em" => s' + "a";
                                  _         => s};
                  <Sg,Voc> => case s of {
                                  s' + "s" => s';
                                  _        => s };
                  _       => s
              })
            };
            
           
    in
    
    case d of {
      First   => case s of {
        puell + "a" => normalstem puell};
      Second  => case s of {
        serv + "us" => normalstem serv;
        lib  + "er" => {stem = (if_then_Str (isConsonant (last lib)) (lib + "r") (lib + "er"));
                        extraLetters = normal; changeSuffix = change2NomForm};
        pom  + "um" => normalstem pom
      } ;
      Third   => case s of { 
        
        --exceptions:
        "canis"      => thirdDeclstem "can";
        "panis"      => thirdDeclstem "pan";  
        "Paris"      => greek_i_stem "Parid";
        -- paris paridis paridi parida paride pari/s
    
        fel  + "es"  => thirdDecl_i_stem fel; 
        infa + "ns"  => thirdDecl_i_stem (infa + "nt"); 
        sang + "uis" => thirdDeclstem  (sang + "uin");
        fl   + "os"  => thirdDeclstem (fl + "or");
        av   + "is"  => thirdDecl_i_stem av; 
        urb  + "s"   => thirdDecl_i_stem "urb"; 
        sen  + "ex"  => thirdDecl_i_stem sen; 
        re   + "x"   => thirdDecl_i_stem (re + "g"); 
        nom  + "en"  => thirdDeclstem (nom + "in");
        hom  + "o"   => thirdDeclstem (hom + "in"); 
        la   + "c"   => thirdDeclstem (la + "ct"); 
        mar  + "e"   => thirdDecl_i_stem mar; 
        _            => normalstem s
       };
      Fourth   =>  case s of {
        man + "us"  => normalstem man;
        gen + "u"   => normalstem gen
      }
      
      };
    
  
  isVowel : Str -> Bool = \a -> case a of
    {"a" | "o" | "u" | "e" | "i" => True;
     _                           => False};
     
  isConsonant : Str -> Bool = \a -> case isVowel a of
    {True => False;
     False => True};


}
