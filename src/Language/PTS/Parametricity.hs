{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | External parametricity
module Language.PTS.Parametricity where

import Language.PTS.Bound
import Language.PTS.Term
import Language.PTS.Smart
import Language.PTS.Sym
import Language.PTS.Specification

relationInf
    :: forall s a b. ReflectiveSpecification s
    => (a -> (b, b, b)) -- ^ translation of variables
    -> TermInf s a
    -> TermInf s b
relationInf ctx term = case term of
    Var a  -> Var (trdOf3 (ctx a))
    Sort s -> Ann
        (Lam "A1" $ toScopeH $ Lam "A2" $ toScopeH $ Var (F (B "A1")) ~> Var (B "A2") ~> Sort (relationSort s))
        (Sort s ~> Sort s ~> Sort s')
      where
        s' = axiom' (relationSort s)

    Ann x t -> Ann (relationChk ctx x) (relationInf ctx t)
    App f x -> relationInf ctx f @@ x1 @@ x2 @@ relationChk ctx x
      where
        x1 = fmap (fstOf3 . ctx) x
        x2 = fmap (sndOf3 . ctx) x

    Pi n a b -> Ann
        ( Lam "f1" $ toScopeH $ Lam "f2" $ toScopeH
        $ Inf $ Pi n a1 $ toScopeH $ Pi n a2 $ toScopeH
        $ Pi "R" aR
        $ toScopeH $ fmap (F . F) bb' @@ f1x1 @@ f2x2
        )
        (term1 ~> term2 ~> Sort typeSortSort)
      where
        bb = fromScopeH b
        bb' = relationInf addContext3 bb

        f1x1 :: TermChk s (Var IrrSym (Var IrrSym (Var IrrSym (Var IrrSym (Var IrrSym b)))))
        f2x2 :: TermChk s (Var IrrSym (Var IrrSym (Var IrrSym (Var IrrSym (Var IrrSym b)))))
        f1x1 = Var (F (F (F (F (B "f1"))))) @@ Inf (Var (F (F (B n))))
        f2x2 = Var (F (F (F (B "f1"))))     @@ Inf (Var (F (B n)))

        addContext3 :: Var IrrSym a ->
            ( Var IrrSym (Var IrrSym (Var IrrSym b))
            , Var IrrSym (Var IrrSym (Var IrrSym b))
            , Var IrrSym (Var IrrSym (Var IrrSym b))
            )
        addContext3 (F a0) = 
            let (x, y, z) = ctx a0
                f3 = F . F . F
            in (f3 x, f3 y, f3 z)
        addContext3 (B nn) =
            (F (F (B nn)), F (B nn), B "R")

        term1 = fmap (fstOf3 . ctx) term
        term2 = fmap (sndOf3 . ctx) term

        a1 = fmap (F . F . fstOf3 . ctx) a
        a2 = fmap (F . F . F . sndOf3 . ctx) a

        aR = fmap (F . F) (fmap (F . F) (relationInf ctx a) @@ Inf (Var (F (B n))) @@ Inf (Var (B n)))

relationChk
    :: ReflectiveSpecification s
    => (a -> (b, b, b)) -- ^ translation of variables
    -> TermChk s a
    -> TermChk s b
relationChk ctx term = error "todo" ctx term

fstOf3 :: (a,b,c) -> a
fstOf3 (a,_,_) = a

sndOf3 :: (a,b,c) -> b
sndOf3 (_,b,_) = b

trdOf3 :: (a,b,c) -> c
trdOf3 (_,_,c) = c
