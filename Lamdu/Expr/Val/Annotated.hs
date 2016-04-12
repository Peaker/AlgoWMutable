-- | Annotated vals
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Lamdu.Expr.Val.Annotated
    ( AV(..)
    , annotation
    , val

    , lam, lambda, lambdaRecord
    , absurd, case_, cases
    , litNum, hole
    , ($$), ($$:), ($=), ($.), (.$), ($+), ($-)
    , recVal, var, infixApp
    , fromNom, toNom
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Binary.Utils (encodeS)
import           Lamdu.Expr.Identifier (Tag(..), NominalId)
import           Lamdu.Expr.Val (Body(..))
import qualified Lamdu.Expr.Val as V
import           Pretty.Map ()
import           Text.PrettyPrint (isEmpty, (<>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

data AV a = AV
    { _annotation :: a
    , _val :: Body (AV a)
    } deriving (Show, Functor, Foldable, Traversable)
instance Pretty a => Pretty (AV a) where
    pPrintPrec level prec (AV ann v)
        | isEmpty annDoc = pPrintPrec level prec v
        | -- HACK:
          pPrint () == annDoc = pPrintPrec level prec v
        | otherwise =
        "PL{" <> annDoc <> "}" <>
        pPrintPrec level 10 v
        where
            annDoc = pPrint ann
instance NFData a => NFData (AV a) where
    rnf (AV ann val) = rnf ann `seq` rnf val

Lens.makeLenses ''AV


fromNom :: Monoid a => NominalId -> AV a -> AV a
fromNom nomId = AV mempty . V.BFromNom . V.Nom nomId

toNom :: Monoid a => NominalId -> AV a -> AV a
toNom nomId = AV mempty . V.BToNom . V.Nom nomId

lam :: Monoid a => V.Var -> AV a -> AV a
lam name body = AV mempty $ V.BLam $ V.Lam name body

lambda :: Monoid a => V.Var -> (AV a -> AV a) -> AV a
lambda name body = lam name $ body $ var name

lambdaRecord :: Monoid a => V.Var -> [Tag] -> ([AV a] -> AV a) -> AV a
lambdaRecord name fields body = lambda name $ \v -> body $ map (v $.) fields

absurd :: Monoid a => AV a
absurd = AV mempty $ V.BLeaf V.LAbsurd

case_ :: Monoid a => Tag -> AV a -> AV a -> AV a
case_ name handler restHandlers = AV mempty $ V.BCase $ V.Case name handler restHandlers

cases :: Monoid a => [(Tag, AV a)] -> AV a
cases = foldr (uncurry case_) absurd

litNum :: Monoid a => Double -> AV a
litNum = AV mempty . V.BLeaf . V.LLiteral . V.PrimVal "Num" . encodeS

hole :: Monoid a => AV a
hole = AV mempty $ V.BLeaf V.LHole

infixl 4 $$
($$) :: Monoid a => AV a -> AV a -> AV a
($$) f a = AV mempty $ V.BApp $ V.Apply f a

($$:) :: Monoid a => AV a -> [(Tag, AV a)] -> AV a
func $$: fields = func $$ recVal fields

recVal :: Monoid a => [(Tag, AV a)] -> AV a
recVal = foldr extend empty
    where
        extend (name, v) = AV mempty . V.BRecExtend . V.RecExtend name v
        empty = AV mempty $ V.BLeaf V.LEmptyRecord

($=) :: Monoid a => Tag -> AV a -> AV a -> AV a
(x $= y) z = AV mempty $ V.BRecExtend $ V.RecExtend x y z

($.) :: Monoid a => AV a -> Tag -> AV a
x $. y = AV mempty $ V.BGetField $ V.GetField x y

(.$) :: Monoid a => Tag -> AV a -> AV a
x .$ y = AV mempty $ V.BInject $ V.Inject x y

var :: Monoid a => V.Var -> AV a
var = AV mempty . V.BLeaf . V.LVar

infixApp :: Monoid a => V.Var -> AV a -> AV a -> AV a
infixApp name x y = var name $$: [("l", x), ("r", y)]

($+) :: Monoid a => AV a -> AV a -> AV a
($+) = infixApp "+"

($-) :: Monoid a => AV a -> AV a -> AV a
($-) = infixApp "-"
