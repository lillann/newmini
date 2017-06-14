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
  
  VForm = VInf | Vf Number Person  Temp ;  -- Add Past, Future
  
  Temp = Pres | Imperf  | Perf | PluPerf ; 
  
  Ten = TPres | TPast;
    
  Ante  = Sim | Anter ; 


  Agreement = Agr Gender Number Person;
 
oper

  Noun : Type = {s : Number => Case => Str; g : Gender};
  
  Preposition = {s : Str; c : Case; ctype : ConcatType}; -- concatfun : NPType -> Str -> Str} ;    
  
  Adjective : Type = {s : Gender => Number => Case => Str};
  
  Verb : Type = {inf : Str; s :  Temp => Number => Person => Str};
  
  Verb2 : Type = Verb ** {c : Str} ;
  
  SComplVerb : Type = Verb ** {conj : Str};
  
  Adverb : Type = {s : Str} ;
  
  Interjection : Type = {s : Str};
    
  GVerb : Type = {
    s : VForm => Str ;
    cas : Case;
    isAux : Bool
   } ;

  be_GVerb : GVerb = {
      s = table {
        VInf       => "esse" ;
        Vf n p t  => ((mkV "sum" "es" "est" "sumus" "estis" "sunt" "esse").s)!t!n!p
        } ;
      cas = Nom;
      isAux = True
      } ;
      
  verb2gverb : Verb -> GVerb = \v -> {s =
    table {
      VInf       => v.inf;
      Vf n p t => v.s ! t  ! n ! p  
      } ;
    cas   = Ack;
    isAux = False
    } ;
    
    
  StemInfo : Type = {stem : Str; extraLetters : Number -> Case -> Str; changeSuffix : Number -> Case  -> Str -> Str};
  
  Funtype  : Type = Number -> Case -> Str;
  ProperName : Type = {s : Case => Str; g : Gender; typ : PNType} ;
  
  agrV : GVerb -> Agreement ->  Temp -> Str = \v,a,t -> case a of {
    Agr _ n p  => v.s ! Vf n p t 
    } ;
  
  mkInterj : Str -> Interjection = \i -> {s = i};
  
  
  
  mkV = overload 
   { mkV : Str -> Verb = regVerb;
                   mkV : Str -> Str -> Verb = \inf,ps -> case getVerbInfo inf of {
                                                         <st,mid,_,decl> => mkRegVerb inf st mid ps decl};
                   
                                                            
                   mkV : Str -> Declension -> Verb = \inf,decl -> case getVerbInfo inf decl of {
                                                           <st,mid,ps,_> => mkRegVerb inf st mid ps decl};
                   mkV : Str -> Str -> Declension -> Verb = \inf,ps,decl -> case getVerbInfo inf decl of {
                                                         <st,mid,_,_> => mkRegVerb inf st mid ps decl};
          --         mkV : Str -> Declension -> Verb = \s,d -> 
          --                      case <d,s> of {
                                             --  <Third,mitt+ "ere">  => mkRegVerb s mitt "i" Third;
          --                                     <Third,aud + "ire">  => mkRegVerb s aud "i" (aud + "iv") Fourth};
                   mkV : (_,_,_,_,_,_,_ : Str) -> Verb =  
                     \sum,es,est,sumus,estis,sunt,esse -> {
    s = table {tmp => table {Sg => table {Per1 => sum; 
                                            Per2 => es; 
                                            Per3 => est };
                               Pl => table {Per1 => sumus; 
                                            Per2 => estis; 
                                            Per3 => sunt} }};
    inf = esse  
    } 
 }; 
                
  mkAdv : Str -> Adverb = \s -> {s = s} ;
  
  mkAda : Str -> Adverb = \s -> {s = s};
                
                                                        
  mkV2 = overload {
    mkV2 : Str -> Declension -> Verb2 = \s,d -> mkV s d ** {c = []};
    mkV2 : Str -> Str -> Declension -> Verb2 = \s,p,d ->  mkV s p d ** {c = []} ;
    mkV2 : Str         -> Verb2 = \s   -> mkV s ** {c = []}} ;
 --   mkV2 : Str  -> Str -> Verb2 = \s,p -> mkV s ** {c = p}} ;
    
  mkVS = overload {
    mkVS : Str -> Str -> SComplVerb = \s,c -> ((mkV s) ** {conj = c});
    mkVS : Str -> Str -> Str -> Declension -> SComplVerb =  \s,ps,c,decl -> ((mkV s ps decl) ** {conj = c})}; 
  
  
  
  getVerbInfo = overload {
  getVerbInfo : Str -> {p1:Str;p2:Str;p3:Str;p4:Declension} = \s -> case s of {
                                voc + "are"  => <voc,"a",voc + "av",First>;
                                terr + "ere" => <terr,"e",terr + "u",Second>;
                                aud + "ire"  => <aud,"i",aud + "iv",Fourth>
                                };
  getVerbInfo : Str -> Declension -> {p1:Str;p2:Str;p3:Str;p4:Declension} = 
      \s,d -> case <s,d> of {
                           --   <vid + e + "re",_> => <vid,e,vid,d>}
                              
                              <em  + "ere",Third>   =>  <em,"i", em,Third>; -- TODO   ems -> emis, men emo, ej emio
                              <ven + "ire", Fourth> =>  <ven,"i", ven,Fourth>;
                              <vid + "ere", Second> => <vid,"e",vid,Second>} -- venio ok
  };
  
  regVerb : Str -> Verb = \s -> 
    case getVerbInfo s of {
      <st,mid,perfst,decl> => 
      mkRegVerb s st mid (perfst) decl}; 
  

    
    
  mkRegVerb : Str -> Str -> Str -> Str -> Declension -> Verb = \inf,stem,mid,perfstem,decl -> {
    inf = inf;
    s = let 
         
        presendings = 
           table {Sg => table {Per1 => "o"; 
                               Per2 => "s"; 
                               Per3 => "t" };
                  Pl => table {Per1 => "mus"; 
                               Per2 => "tis"; 
                               Per3 => "nt"} };
                               
         impendings  : Number => Person => Str =  
            \\n,p     => "ba"  + case <n,p> of { <Sg,Per1> => "m"; _ => presendings!n!p};
         
     pluperfendings  : Number => Person => Str =  
            \\n,p => "era" + case <n,p> of { <Sg,Per1> => "m"; _ => presendings!n!p};

         perfendings : Number => Person => Str = 
             table {Sg => table {Per1 => "i"; 
                                 Per2 => "isti"; 
                                 Per3 => "it" };
                  Pl => table {  Per1 => "imus"; 
                                 Per2 => "istis"; 
                                 Per3 => "erunt"} };

{-         perfendings : Number => Person => Str =   \\n,p => let 
                                                              parts =  case <n,p> of {
                                                                <Sg,Per2>   => <"i", "ti">;
                                                                <Pl,Per3>   => <"eru","">;
                                                                <Pl,Per2>   => <"is","">;
                                                                <_,_>       => <"i","">}
                                                             in
                                                                parts.p1 + case <n,p> of 
                                                                       {<Sg,Per1> => ""; _ => presendings!n!p} + parts.p2;
-}
                                                      
         pickStem :  Temp -> Number => Person => Str = \t -> \\n,p => case t of {Pres => stem; Imperf => stem; Perf => perfstem; PluPerf => perfstem};
         pickEndings :  Temp -> Number => Person => Str = 
             \t -> case t of {Pres => presendings;Imperf => impendings; Perf => perfendings; PluPerf => pluperfendings};
                                                             
         extraletters :  Temp -> Number -> Person  -> Str = \t,n,p -> case <t,n,p,decl> of 
                             { <Pres,Sg,Per1,First>  => "";
                               <Imperf,_,_,First>        => "a";
                               <Imperf,_,_,Second | Third>       => "e";
                               <Imperf,_,_,_>            => mid + "e";
                              <Pres,Sg,Per1,Third>  => "";
                              <Pres,Pl,Per3,Third>  => "u";
                              <Pres,Pl,Per3,Fourth> => "iu"; 
                              --<Perf,_,_,Third>  => "e";
                              --<Perf,_,_,Fourth> => "ie";
                              <Perf,_,_,_>      => "";
                               <PluPerf,_,_,_>    => "";
                              _                 => mid}                                   
        in
    
    table { temp =>     
    table { num  => 
    table { pers => (pickStem temp)!num!pers + extraletters temp num pers  + ((pickEndings temp) ! num ! pers)}}
          
  }};
    
  
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
