resource MiniResLat = open Prelude,Predef in {


param

  Number = Sg | Pl ;
  Case = Nom | Gen | Dat | Ack | Abl | Voc ;
  Person = Per1 | Per2 | Per3 ;  
  Gender = Fem | Masc | Neut ;
  Declension = First | Second | Third | Fourth;
  
  PNType = Place | Name ; 
  
  ConcatType = Pre | Post;
  
  NPType = NPPN PNType | NPPron | NPNoun ; 
  
  VForm = VInf | Vf Number Person Tempus Mood ;  
  Tempus = Pres | Imperf  | Perf | PluPerf ; 
  
  Tense = TPr | TPa;    
  Ante  = Sim | Anter ; 
  Mood = Ind | Conj ; 
  
  NPStress     = NounFirst | AdjFirst ; 
  VPStress     = ObjFirst | VerbFirst ;
  
  
  
  -- NPStress ;
  
  -- VerbFirst | ObjFirst IndirObjFirst;
  

  ClauseStress = NPFirst | VPFirst ;
  
  -- NPStress VPStress | VPFirst NPStress VPStress;
  
  
  Agreement = Agr Gender Number Person ;
 
oper

  Subj : Type = {s : Str; m : Mood};

  Noun : Type = {s : Number => Case => Str; g : Gender};
  
  Preposition = {s : Str; c : Case; ctype : ConcatType}; -- concatfun : NPType -> Str -> Str} ;    
  
  Adjective : Type = {s : Gender => Number => Case => Str};
  
  Verb : Type = {inf : Str; stem : Str; decl : Declension; s :  Mood => Tempus => Number => Person => Str}; --{s:Str;firsttok: Str}};
  
  Verb2 : Type = Verb ** {c : Str} ;
  
  SComplVerb : Type = Verb ** {conj : Str};
  
  Adverb : Type = {s : Str} ;
  AdjA : Type = {s : Str};
  IAdv : Type = {s : Str};
  
  Interjection : Type = {s : Str};
  

    
  GVerb : Type = {
    s   : VForm => Str ;
    imp : Number => Str ;
    cas : Case;
    isAux : Bool
   } ;




be_GVerb : GVerb = verb2gverb mkVBe;

  verb2gverb : Verb -> GVerb = \v -> {s =
    table {
      VInf       => v.inf;
      Vf n p t m => (v.s ! m ! t  ! n ! p) 
      } ;
    imp   = let imps = imperativeEndings v.inf v.decl in                
               table {Sg   => v.stem ++ BIND ++ imps.s;
                      Pl   => v.stem ++ BIND ++ imps.pl};
    cas   = Ack;
    isAux = False
    } ;
    
    
  StemInfo : Type = {stem : Str; extraLetters : Number -> Case -> Str; changeSuffix : Number -> Case  -> Str -> Str};
  
  VerbInfo : Type = {stem : Tempus => Str; mid : Str; d : Declension};
  
  Funtype  : Type = Number -> Case -> Str;
  ProperName : Type = {s : Case => Str; g : Gender; typ : PNType} ;
  
  agrV : GVerb -> Agreement ->  Mood -> Tempus -> Str = \v,a,m,t -> case a of {
    Agr _ n p  => v.s ! Vf n p t m
    } ;
    
 
  mkInterj : Str -> Interjection = \i -> {s = i};
  mkAdv : Str -> Adverb = \s -> {s = s} ;  
 -- mkAdA : Str -> Adverb = \s -> {s = s};  
  mkSubj : Str -> Mood -> Subj = \i,mood -> {s = i; m = mood};
  
  mkAdjA : Str -> AdjA = \s -> {s = s};
  
  mkIAdv : Str -> IAdv = \s -> {s = s};
  
  
  mkVBe : Verb = 
    let vinfo = getVerbInfoBe ;
        v     = mkVerb "esse" vinfo in
    {
    s = \\mood,temp,num,pers => 
            let conjendings = (pickEndings Conj Pres) ! num ! pers ;
                normal      = v.s ! mood ! temp ! num ! pers in
            case <temp,mood> of {            
                    <Pres,Ind> => case <pers,num> of {
                                    <Per1,Sg> => "sum";
                                    <Per2,Sg> => "es";
                                    <Per1,Pl> => "sumus";
                                    <Per3,Pl> => "sunt";
                                    _         => normal};
                     <Pres,Conj> => "si" + conjendings;
                     <Imperf,Ind>  => vinfo.stem!temp + "a" +  conjendings;
                     <Imperf,Conj> => "esse" + conjendings;                     
                    _ => normal};
    inf  = "esse";
    stem = v.stem;
    decl = v.decl    
    };
    

  
  mkV = overload 
   { mkV : Str -> Verb = \s -> 
       let vinfo = getVerbInfo s in mkVerb s vinfo;
     mkV : Str -> Declension -> Verb = \s,decl -> let vinfo = getVerbInfo s in
        mkVerb s vinfo**{d=decl};
     mkV : Str -> Str -> Declension -> Verb = \inf,pstem,decl -> let vinfo = getVerbInfo inf pstem decl in
        mkVerb inf vinfo**{d=decl}};
        
     
        
                                                                    
  mkV2 = overload {
    mkV2 : Str -> Declension -> Verb2 = \s,d -> mkV s d ** {c = []};
    mkV2 : Str -> Str -> Declension -> Verb2 = \s,p,d ->  mkV s p d ** {c = []} ;
    mkV2 : Str         -> Verb2 = \s   -> mkV s ** {c = []}} ;
 --   mkV2 : Str  -> Str -> Verb2 = \s,p -> mkV s ** {c = p}} ;
    
  mkVS = overload {
    mkVS : Str -> Str -> SComplVerb = \s,c -> ((mkV s) ** {conj = c});
    mkVS : Str -> Str -> Str -> Declension -> SComplVerb =  \s,ps,c,decl -> ((mkV s ps decl) ** {conj = c})}; 
  
  getVerbInfo = overload {
  getVerbInfo : Str -> Str -> Declension -> VerbInfo = getVerbInfo3;
  getVerbInfo : Str -> VerbInfo = getVerbInfo1;
  };
  
  getVerbInfoBe : VerbInfo = 
     {stem = \\t => case t of {Pres => "e"; Imperf => "er";_ => "fu"};
      mid  = "s";
      d    = First};
  
  getVerbInfo3 : Str -> Str -> Declension -> VerbInfo = \s,pst,decl -> 
     let cstem = cutStem s decl in
         {stem = \\t => case t of {Perf | PluPerf => pst; _ => cstem.stem};
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
      aud  + "ire"  =>  {stem=aud;mid="i";   perfmid = "iv";d = Fourth};
      terr + "ere"  =>  {stem=terr;mid="e"; perfmid = "u" ;d = Second};
      voc  + "are"  =>  {stem=voc;mid="a";  perfmid = "av";d = First}};
      
      
 
      
    
  imperativeEndings : Str -> Declension -> {s : Str;pl : Str} = \st,decl ->
    case decl of {
      First  => {s = "a"; pl = "ate"};
      Second => {s = "e"; pl = "ete"}; 
      Third  => {s = "e"; pl = "ite"};
      Fourth => {s = "i"; pl = "ite"}};
  -- irregular: dic/duc/fac/fer    
   
  presendings : Mood -> Number => Person => Str = \mood -> 
           table {Sg => table {Per1 => case mood of {Ind => "o"; Conj => "m"}; 
                               Per2 => "s"; 
                               Per3 => "t" };
                  Pl => table {Per1 => "mus"; 
                               Per2 => "tis"; 
                               Per3 => "nt"} };
                                                                     
  impendings  : Mood -> Number => Person => Str =  \mood ->
             \\n,p     => case mood of {Ind  => "ba";
                                        Conj => "re"} + (presendings Conj)!n!p;                                             
  pluperfendings  : Mood -> Number => Person => Str =  \mood ->
            \\n,p => case mood of { Ind => "era"; Conj => "isse"} + (presendings Conj)!n!p;
            
  perfendings : Mood -> Number => Person => Str = \mood -> 
          case mood of {Conj => \\n,p => "eri" + (presendings mood)!n!p ;
                        Ind  =>
                          table {Sg => table {Per1 => "i"; 
                                              Per2 => "isti"; 
                                              Per3 => "it" };
                                 Pl => table {Per1 => "imus"; 
                                              Per2 => "istis"; 
                                              Per3 => "erunt"} }};
       
  pickEndings :  Mood -> Tempus -> Number => Person => Str = 
      \m,t -> case t of {Pres => presendings m;Imperf => impendings m; Perf => perfendings m; PluPerf => pluperfendings m};

      
  mkVerb : Str  -> VerbInfo  -> Verb = \inf,verbinfo -> {
    inf = inf;
    decl = verbinfo.d;
    stem = verbinfo.stem!Pres;
    s = let                                              
         mid  = verbinfo.mid;   
         
         
         istem : Bool = case inf of {viv+"ere" => True; _ => False};                                            
         extraletters :  Tempus -> Number -> Person -> Mood -> Str = \t,n,p,mood -> 
           let mid' = case <mid,verbinfo.d,mood,inf>  of {
                      --  <"e", Third,Conj>          => "a" ;
                        <"e", Third, Conj>           => "e";
                        <"i", Third, Conj> => if_then_Str istem "a" "ia";
                        <"i",Fourth, Conj> => "ia";
                        <"a",First,Conj>           => "e";
                        <"e",Second,Conj>          => "ea";
                        
                        _                          => mid} in
         case <t,n,p,verbinfo.d,mood> of 
                             { <Pres,Sg,Per1,First,Ind>          => "";
                               <Pres,_,_,_,Conj>                 => mid';
                               <Imperf,_,_,First,Ind>            => "a";
                               <Imperf,_,_,Second | Third,Ind>   => "e";
                               <Imperf,_,_,_,Ind>            => mid' + "e";
                               <Imperf,_,_,_,Conj>           => if_then_Str istem "e" mid;
                              <Pres,Sg,Per1,Third,Ind>       => "";
                              <Pres,Pl,Per3,Third,Ind>       => "u";
                              <Pres,Pl,Per3,Fourth,Ind>      => "iu"; 
                              <Perf,_,_,_,_>               => "";
                               <PluPerf,_,_,_,_>           => "";
                              _                          => mid}  ;
        
    in  
    \\mood,temp,num,pers =>
    (verbinfo.stem!temp) + extraletters temp num pers mood  + ((pickEndings mood temp) ! num ! pers)       
  };
    
  
  mkA = overload {
    mkA : Str -> Declension -> Adjective = mkAdj ;
    mkA : (mf, neut : Str) -> Declension -> Adjective = mkAdj2 ;
    mkA : (m,f,n : Str) -> Declension ->  Adjective = mkAdj3 ; 
    } ;
  
    mkAdj : Str -> Declension -> Adjective = \adj,d -> mkAdj3 adj adj adj d;
    mkAdj2 : Str -> Str -> Declension -> Adjective = \adj1,adj2,d ->  mkAdj3 adj1 adj1 adj2 d;
       
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
    
      First   => case n of { 
                    Sg => table {Nom => "a" ; Gen => "ae"; Dat => "ae"; Ack =>"am"; Abl => "a"; Voc => "a"};
                    Pl => table {Nom => "ae" ; Gen => "arum"; Dat => "is"; Ack =>"as"; Abl => "is"; Voc => "ae"}};
      Second  => case n of { 
                    Sg => table {Nom => case g of {Neut => "um"; _ => "us"}; Gen => "i"; Dat =>  "o"; Ack => "um"; Abl  => "o"; Voc => case g of {Neut => "um"; _ => "e"}};
                    Pl => case g of {                    
                      Neut =>  table {Nom => "a"; Gen => "orum"; Dat => "is"; Ack =>"a";  Abl => "is";Voc => "a"};
                      _    =>  table {Nom => "i"; Gen => "orum"; Dat => "is"; Ack =>"os"; Abl =>  "is";Voc => "i"}
                    }};
                    
      Third   =>  case n of {
                    Sg => table {Nom => ""; Gen =>  "is"; Dat =>  "i"; Ack => "em"; Abl =>  "e";Voc => ""};
                    --case g of {Neut => "en"; _ => "em"}
                    Pl => case g of {
                     
                      Neut    =>  table {Nom => "a"; Gen => "um"; Dat => "ibus"; Ack => "a"; Abl => "ibus" ;Voc => "a"}; 
                      _       =>  table {Nom => "es"; Gen => "um"; Dat => "ibus"; Ack =>"es"; Abl => "ibus" ; Voc => "es"}
                    }};                 
       Fourth  => case g of {
                    Neut => case n of {
                              Sg => table {Nom => "u"; Gen =>  "u"; Dat =>  "ui"; Ack =>"u"; Abl =>  "u"; Voc => ""};
                              Pl => table {Nom => "ua"; Gen =>  "uum"; Dat =>  "ibus"; Ack =>"ua"; Abl =>  "ibus";Voc => "ua"}};
                    _    => case n of {
                              Sg => table {Nom => "us"; Gen =>  "us"; Dat =>  "ui"; Ack =>"um"; Abl =>  "u";Voc => "us"};
                              Pl => table {Nom => "us"; Gen =>  "uum"; Dat =>  "ibus"; Ack =>"us"; Abl =>  "ibus";Voc => "us"}}
                    }};
  
  
  mkNounTable : NParams -> Number => Case => Str = \np -> 
  
    let st         = (np.steminfo).stem;
        addfun     = (np.steminfo).extraLetters; 
        changesuff = (np.steminfo).changeSuffix; -- Num -> Cas -> Str -> Str
        -- removefun = (np.steminfo).removeLetters; 
        suffixes  = nounEndings np.decl np.gen in
  
         table { num => 
          table {cas => --{s = ""; firsttok = 
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

--  chooseStressNP : NPStress -> Str -> Str -> {s : Str; firsttok : Str; rest : Str} = 
  --   \stress,s1,s2 -> {s = "";firsttok="";rest=""};


}
