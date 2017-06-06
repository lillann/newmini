concrete MiniLexiconLat of MiniLexicon = ExtMiniGrammarLat ** open MiniResLat in {

lin animal_N   = mkNoun "bestia" First Fem;
lin apple_N    = mkNoun "pomum" Second Neut;
lin baby_N     = mkNoun "infans" Third Masc;
lin beer_N     = mkNoun "cervisia" First Fem ;
lin bike_N     = mkNoun "birota" First Fem;
lin bird_N     = mkNoun "avis" Third Fem;
lin blood_N    = mkNoun "sanguis" Third Masc ;
lin ship_N     = mkNoun "navis" Third Fem ;
lin book_N     = mkNoun "liber" Second Masc ;
lin boy_N      = mkNoun "puer" Second Masc ;
lin bread_N    = mkNoun "panis" Third Masc ;
lin car_N      = mkNoun "currus" Fourth Masc;
lin cat_N      = mkNoun "feles" Third Fem ;
lin child_N    = mkNoun "infans" Third Masc ;
lin city_N     = mkNoun "urbs" Third Fem ;
lin cloud_N    = mkNoun "nebula" First Fem ;
lin computer_N = mkNoun "computator" Third Masc ;
lin dog_N      = mkNoun "canis" Third Masc ;
lin cow_N      = mkNoun "vacca" First Fem ;
lin fire_N     = mkNoun "ignis"  Third Masc;
lin fish_N     = mkNoun "piscis" Third Masc ;
lin flower_N   = mkNoun "flos" Third Masc ;
lin friend_N   = mkNoun "amicus" Second Masc ;
lin girl_N     = mkNoun "puella" First Fem ;
lin grammar_N  = mkNoun "grammatica" First Fem ;
lin horse_N    = mkNoun "equus" Second Masc ;
lin house_N    = mkNoun "domus" Fourth Masc ;
lin language_N = mkNoun "lingua" First Fem ;
lin man_N      = mkNoun "homo" Third Masc ;
lin milk_N     = mkNoun "lac" Third Neut ;
lin music_N    = mkNoun "musica" First Fem ;
lin river_N    = mkNoun "flumen" Third Neut ;
lin sea_N      = mkNoun "mare" Third Neut;
lin boat_N     = mkNoun "navicula" First Fem ;
lin star_N     = mkNoun "stella" First Fem ;
lin train_N    = mkNoun "agmen" Third Neut ;
lin tree_N     = mkNoun "arbor" Third Fem ;
lin water_N    = mkNoun "aqua" First Fem ;
lin wine_N     = mkNoun "vinum" Second Neut ;
lin woman_N    = mkNoun "femina" First Fem ;

lin john_PN       = mkPN "Ioannes" Third Masc Name ;
lin paris_PN       = mkPN "Paris" Third Masc Place;

-- Adjectives
lin bad_A      = mkA "malus" Second;
lin warm_A     = mkA "calidus" Second ;
lin white_A    = mkA "albus" Second ;
lin yellow_A   = mkA "flavus" Second ;
lin young_A    = mkA "iuvenis" Third ;
lin big_A      = mkA "magnus" Second ;
lin black_A    = mkA "niger" Second ;
lin blue_A     = mkA "venetus" Second  ;
lin clean_A    = mkA "purus" Second;
lin clever_A   = mkA "intelligens" Third ;
lin cold_A     = mkA "frigidus" Second ;
lin good_A     = mkA "bonus" Second ;
lin dirty_A    = mkA "sordidus" Second ;
lin new_A      = mkA "novus" Second ;
lin small_A    = mkA "parvus" Second ;
lin red_A      = mkA "ruber" Second ;
lin ready_A    = mkA "paratus" Second ;
lin old_A      = mkA "senex" Third ;
lin old_man_N  = mkNoun "senex" Third Masc ; 
lin hot_A      = mkA "caldus" Second ;
lin green_A    = mkA "viridis" "viride" Third ;
lin heavy_A    = mkA "gravis" "grave" Third ;

-- VERBS
lin jump_V = mkV "salire";
lin come_V = mkV "venire";
lin play_V = mkV "ludere" Third;
lin run_V  = mkV "currere" Third;
lin go_V   = mkV "eo" "is" "it" "imus" "itis" "eunt" "ire"; 
lin walk_V = mkV "ambulare" ;
lin live_V = mkV "vivere" Third ;
lin sleep_V = mkV "dormire" ;
lin swim_V = mkV "natare" ;
lin travel_V = mkV "viare" ;
lin drink_V2 = mkV2 "bibere" Third ;

lin already_Adv = mkAdv "iam" ;
lin now_Adv = mkAdv "nunc" ;

lin love_V2 = mkV2 "amare";
lin buy_V2   = mkV2 "emere" Third;

lin eat_V2 = mkV2 "manducare" ;
lin find_V2 = mkV2 "invenire" ;


lin kill_V2 = mkV2 "necare" ;
lin read_V2 = mkV2 "legere" Third;
lin see_V2 = mkV2 "videre" ;

lin teach_V2 = mkV2 "docere" ;
lin break_V2 = mkV2 "frangere" Third;

lin understand_V2 = mkV2 "comprehendere"  Third;
lin wait_V2 = mkV2 "expectare" ;

-- lin alas_Interj = mkInterj "eheu";


}
