module DN_Prop ( F(L,B,N,(:&),(:|),(:>)) , Thm , 
                                            hyp,
                                            bot_E,
                                            i_neg,
                                            e_neg,
                                            intro_Y,
                                            e_YI,
                                            e_YD,
                                            intro_Im,
                                            e_Im,
                                            raa ,
                                            i_OD,
                                            i_OI ,
                                            e_o)
                                            where 
type V = String
data F = L V
        |B
        |N F
        |F :& F 
        |F :| F 
        |F :> F

    deriving (Eq,Show)
data Thm = Thm [F] F
    deriving Show
    --Alumno : Joaquin Ruiz 
    -- Nro estudiandte : 206164 
itsThere :: [F] -> F -> Bool
itsThere = \l -> \f -> case l of {
            [] -> False;
            x:xs -> case x == f of {
                     True -> True;
                     False -> itsThere xs f;
            };
}
removeDoubles :: [F] -> [F]
removeDoubles = \l  -> case l of {
         [] -> [];
         x:xs -> case itsThere xs x of {
                   True -> removeDoubles xs ;
                   False -> x : removeDoubles xs ; 
         };
}
removeFromList :: [F] -> F ->[F]
removeFromList = \l -> \f -> case l of {
            [] -> [];
            x:xs -> case x /= f of{
                     True -> x : removeFromList xs f;
                     False -> removeFromList xs f;
            };
}



-- Pre :  /hyp a) : none .
-- Post :  (hyp ) : alfa |- alfa.
hyp :: F -> Thm
hyp  a = Thm [a] a
--- pre (bot_E a t) .
-- post (bot_E a t ): hipst |- a .
bot_E :: F -> Thm -> Thm
bot_E alfa ( Thm hs B ) = Thm hs alfa
bot_E _  ( Thm  random  random2) = error "incorrecto , no se puede aplicar la eliminacion del bottom en esta instancia , verifique." 
-- pre : (i_neg a t) : concl t == bottom.
-- post : (i_neg a t) : hips t - a |- N a .
i_neg :: F -> Thm -> Thm
i_neg alfa ( Thm hps B ) = Thm (  (removeFromList hps alfa) ) ( N alfa );
i_neg _ (Thm  _  random) = error "Incorrecto , no se puede aplicar la introduccion de la negacion , verifique."

--Pre : (e_neg t1 t2) : concl t2 = N(concl t1).
--Pos : (e_neg t1 t2) : hipstt1 + hipstt2 |- B.
e_neg :: Thm ->Thm -> Thm
e_neg ( Thm hps alfa ) ( Thm hps2 ( N beta ) )
                        | ( alfa == beta ) = Thm (  ( hps ++ hps2 ) ) B
                        | otherwise = error "Incorrecto , los negados no son iguales , no se puede aplicar la eliminacion de la negacion , verifique." 

-- Pre : pre (intro_Y ) : ninguna.
-- Pos : ( intro_Y t1 t2 ) : ( hips t1 + hips t2 ) |- ( concl t1 :& concl t2 ).
intro_Y :: Thm -> Thm -> Thm
intro_Y (Thm hps alfa) (Thm hps2 beta) = Thm ( (hps ) ++ (hps2 )) (alfa :& beta); 
-- Pre : ( e_YI ) : concl t == a :& b.
-- Pos : ( e_YI ) : hips t |- a.
e_YI:: Thm -> Thm
e_YI  (Thm hps ( alfa :& beta ) ) = Thm hps alfa;
e_YI ( Thm _ random ) = error "Incorrecto , no se puede aplicar la eliminacion del Y por izquierda."
-- Pre : ( e_YD ) : concl t == a :& b.
-- Pos : ( e_YD ) : ( hips t ) |- b.
e_YD:: Thm -> Thm
e_YD (Thm hps (alfa :& beta)) = Thm hps beta;
e_YD ( Thm _ random ) = error "Incorrecto , no se puede aplicar la eliminacion del Y por derecha." 
-- Pre : none.
-- Pos : ( intro_Im a t ) : ( hips t - a ) |- ( a :> concl t ).
intro_Im ::F -> Thm -> Thm
intro_Im alfa ( Thm hps beta ) = Thm ( removeFromList hps alfa ) ( alfa:>beta );
-- Pre : ( e_Im t1 t2 ) : ++ t1 == a :> b && ++ t2 == a.
-- Pos : ( e_Im t1 t2 ) : hips t1 + hips t2 |- b.
e_Im :: Thm  -> Thm -> Thm
e_Im (Thm hps (alfa :> beta)) (Thm (hps2) gama)
            | (alfa == gama)  = Thm  ((hps++hps2)) beta
            | otherwise = error "No se puede aplicar la eliminacion del implica en esta instancia , verifique."
e_Im (Thm random random2 ) (Thm ( random3 ) random4) = error "No se puede aplicar la eliminacion del implica en esta instancia , verifique."            
-- Pre : ( raa a t ) : cond == bottom.
-- Pos : ( raa a t ) : hip t - N a |- a.
raa :: F -> Thm -> Thm 
raa alfa ( Thm hps B ) = Thm (removeFromList hps (N alfa)) alfa;
raa alfa ( Thm _ random ) = error " Incorrecto no se pude aplicar el raa , verifique.";
-- Pre : ( i_OD b t ) : none.
-- Pos : ( i_OD b t ) : hips concl t :| b |- t.
i_OD :: F -> Thm-> Thm
i_OD alfa ( Thm hps beta ) = Thm hps ( alfa :| beta );
-- Pre : ( i_OI b t ) : none.
-- Pos : ( i_OD b t ) : hips t |- concl t :| b .
i_OI :: F -> Thm-> Thm
i_OI beta (Thm hps alfa ) = Thm hps ( alfa :| beta );
-- Pre : ( e_o t1 t2 t3 ) cond t1 == a :| b , cond t2 == cond t3 .
-- Pos : ( e_o t1 t2 t3 ) hips t1 + hips t2 - a + hips t3 - b |- cond t2.
e_o :: Thm -> Thm -> Thm -> Thm 
e_o (Thm hps alfa) (Thm hps2 beta) (Thm hps3 ( f1 :| f2 ))
                                        | (alfa == beta) = Thm ((removeFromList hps f1 ) ++ (removeFromList hps2 f2) ++ hps3) alfa
                                        | otherwise = error "Incorrecto , no se puede aplicar la eliminacion del V. "
e_o (Thm hps alfa) (Thm hps2 beta) ( Thm hps3 ( random ) ) = error " La eliminacion del V no puede ser aplicada , posiblemente la ocnectiva no es correcta."
