{-# LANGUAGE NoImplicitPrelude, DataKinds, OverloadedStrings #-}

module TestVals
    -- ( env
    -- , list
    -- , factorialVal, euler1Val, solveDepressedQuarticVal
    -- , factorsVal
    -- , lambda, lambdaRecord, whereItem, recordType
    -- , eLet
    -- , listTypePair, boolTypePair, polyIdTypePair, unsafeCoerceTypePair
    -- , ignoredParamTypePair
    -- , xGetterPair, xGetterPairConstrained
    -- )
    where

import           Control.Lens.Operators
import qualified Data.IntMap as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Lamdu.Expr.Identifier (NominalId, Tag)
import           Lamdu.Expr.Type (AST(..))
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Nominal
    ( Nominal(..), NominalType(..), NominalScheme(..), ParameterizedType(..) )
import           Lamdu.Expr.Type.Pure (T, (~>))
import qualified Lamdu.Expr.Type.Pure as T
import qualified Lamdu.Expr.Type.Scheme as Scheme
import           Lamdu.Expr.Type.Tag (ASTTag(..), IsCompositeTag(..))
import qualified Lamdu.Expr.Val as Val
import           Lamdu.Expr.Val.Annotated (AV, ($$), ($$:))
import qualified Lamdu.Expr.Val.Annotated as V
import           Lamdu.Infer.Scope (Scope)
import qualified Lamdu.Infer.Scope as Scope

import           Prelude.Compat

type V = AV ()
type TType = T 'TypeT

infixType :: T 'TypeT -> T 'TypeT -> T 'TypeT -> T 'TypeT
infixType a b c = T.recordType [("l", a), ("r", b)] ~> c

eLet :: Val.Var -> V -> (V -> V) -> V
eLet name val mkBody = V.lam name body $$ val
    where
        body = mkBody $ V.var name

whereItem :: Val.Var -> V -> (V -> V) -> V
whereItem name val mkBody = V.lambda name mkBody $$ val

-- openRecordType :: Text -> [(Text, TType)] -> TType
-- openRecordType tv = TRecord . foldr (uncurry RecExtend) (CVar tv)

p :: AST tag ParameterizedType -> ParameterizedType tag
p = ParameterizedType

pComposite :: IsCompositeTag c => [(Tag, ParameterizedType 'TypeT)] -> ParameterizedType ('CompositeT c)
pComposite = foldr ((p .) . uncurry TCompositeExtend) (p TEmptyComposite)

pRecord :: [(Tag, ParameterizedType 'TypeT)] -> ParameterizedType 'TypeT
pRecord = p . TRecord . pComposite

pSum :: [(Tag, ParameterizedType 'TypeT)] -> ParameterizedType 'TypeT
pSum = p . TSum . pComposite

boolTypePair :: (NominalId, Nominal)
boolTypePair =
    ( "Bool"
    , Nominal
      { nParams = mempty
      , nType =
        pSum
        [ ("True", pRecord [])
        , ("False", pRecord [])
        ]
        & NominalScheme mempty
        & NominalType
      }
    )

numTypePair :: (NominalId, Nominal)
numTypePair =
    ( "Num"
    , Nominal
      { nParams = mempty
      , nType = OpaqueNominal
      }
    )

listTypePair :: (NominalId, Nominal)
listTypePair =
    ( "List"
    , Nominal
      { nParams = Set.singleton "elem"
      , nType =
        pSum
        [ ("Empty", pRecord [])
        , ("NonEmpty" , pRecord [("head", tv), ("tail", p (TInst "List" (Map.singleton "elem" tv)))])
        ]
        & NominalScheme mempty
        & NominalType
      }
    )
    where
        tv = ParamRef "elem"

listOf :: TType -> TType
listOf = T.tInst "List" . Map.singleton "elem"

stTypePair :: (NominalId, Nominal)
stTypePair =
    ( "ST"
    , Nominal
      { nParams = Set.fromList ["s", "elem"]
      , nType = OpaqueNominal
      }
    )

closedStTypePair :: (NominalId, Nominal)
closedStTypePair =
    ( "ClosedST"
    , Nominal
      { nParams = Set.singleton "elem"
      , nType =
        Map.fromList [("s", (p (TSkolem (Type.TVarName s)))), ("elem", ParamRef "elem")]
        & TInst "St" & p
        & NominalScheme mempty
          { Scheme.schemeTypeBinders =
            IntMap.singleton s mempty
          }
        & NominalType
      }
    )
    where
        s = 0


closedStOf :: TType -> TType
closedStOf = T.tInst "ClosedST" . Map.singleton "elem"

-- boolTypePair :: (Id, Nominal)
-- boolTypePair =
--     ( "Bool"
--     , Nominal
--         { nParams = Map.empty
--         , nScheme =
--             CEmpty
--             & CExtend "True" (recordType [])
--             & CExtend "False" (recordType [])
--             & TSum
--             & Scheme.mono
--         }
--     )

-- polyIdTypePair :: (Id, Nominal)
-- polyIdTypePair =
--     ( "PolyIdentity"
--     , Nominal
--         { nParams = Map.empty
--         , nScheme =
--             Scheme (TV.singleton tvA) mempty $
--             a ~> a
--         }
--     )
--     where
--         a = TV.lift tvA
--         tvA :: TypeVar
--         tvA = "a"

-- unsafeCoerceTypePair :: (Id, Nominal)
-- unsafeCoerceTypePair =
--     ( "UnsafeCoerce"
--     , Nominal
--         { nParams = Map.empty
--         , nScheme =
--             Scheme (TV.singleton tvA <> TV.singleton tvB) mempty $
--             a ~> b
--         }
--     )
--     where
--         a = TV.lift tvA
--         b = TV.lift tvB
--         tvA, tvB :: TypeVar
--         tvA = "a"
--         tvB = "b"

-- ignoredParamTypePair :: (Id, Nominal)
-- ignoredParamTypePair =
--     ( "IgnoredParam"
--     , Nominal
--         { nParams = Map.singleton "res" tvB
--         , nScheme =
--             Scheme (TV.singleton tvA) mempty $
--             a ~> b
--         }
--     )
--     where
--         a = TV.lift tvA
--         b = TV.lift tvB
--         tvA, tvB :: TypeVar
--         tvA = "a"
--         tvB = "b"

-- xGetter :: (Text -> Constraints) -> Nominal
-- xGetter constraints =
--     Nominal
--     { nParams = Map.empty
--     , nScheme =
--         Scheme (TV.singleton tvA <> TV.singleton tvRest) (constraints tvRest) $
--         openRecordType tvRest [("x", a)] ~> a
--     }
--     where
--         tvRest :: Text
--         tvRest = "rest"
--         a = TV.lift tvA
--         tvA :: TypeVar
--         tvA = "a"

-- xGetterPair :: (Id, Nominal)
-- xGetterPair =
--     ( "XGetter"
--     , xGetter mempty
--     )

-- xGetterPairConstrained :: (Id, Nominal)
-- xGetterPairConstrained =
--     ( "XGetterConstrained"
--     , xGetter $
--       \tvRest ->
--           mempty
--           { productVarConstraints =
--               CompositeVarConstraints $ Map.singleton tvRest $
--               Set.fromList ["x", "y"]
--           }

--     )

-- maybeOf :: TType -> TType
-- maybeOf t =
--     TSum $
--     CExtend "Nothing" (recordType []) $
--     CExtend "Just" t $
--     CEmpty

infixArgs :: V -> V -> V
infixArgs l r = V.recVal [("l", l), ("r", r)]

numType :: T 'TypeT
numType = T.tInst (fst numTypePair) mempty

boolType :: T 'TypeT
boolType = T.tInst (fst boolTypePair) mempty

env :: Scope
env = Scope.newScope nominals globals
    where
        nominals =
            Map.fromList
            [ listTypePair
            , stTypePair
            , closedStTypePair
            -- , boolTypePair
            -- , polyIdTypePair
            -- , unsafeCoerceTypePair
            -- , ignoredParamTypePair
            -- , xGetterPair
            -- , xGetterPairConstrained
            ]
        globals = Map.fromList
            [ ("fix",    Scheme.forAll 1 0 0 $ \ [a] [] [] -> (a ~> a) ~> a)
            , ("if",     Scheme.forAll 1 0 0 $ \ [a] [] [] -> T.recordType [("condition", boolType), ("then", a), ("else", a)] ~> a)
            , ("==",     Scheme.forAll 1 0 0 $ \ [a] [] [] -> infixType a a boolType)
            , (">",      Scheme.forAll 1 0 0 $ \ [a] [] [] -> infixType a a boolType)
            , ("%",      Scheme.forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
            , ("*",      Scheme.forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
            , ("-",      Scheme.forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
            , ("+",      Scheme.forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
            , ("/",      Scheme.forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)

            , ("bool'",  Scheme.forAll 1 0 0 $ \ [a] [] [] -> boolType ~> a ~> a ~> a)
            , ("eq",     Scheme.forAll 1 0 0 $ \ [a] [] [] -> a ~> a ~> boolType)
            , ("mul",    Scheme.forAll 1 0 0 $ \ [a] [] [] -> a ~> a ~> a)
            , ("sub",    Scheme.forAll 1 0 0 $ \ [a] [] [] -> a ~> a ~> a)

            , ("//",     Scheme.forAll 0 0 0 $ \ []  [] [] -> infixType numType numType numType)
            -- , ("sum",    Scheme.forAll 1 0 0 $ \ [a] [] [] -> listOf a ~> a)
            -- , ("filter", Scheme.forAll 1 0 0 $ \ [a] [] [] -> recordType [("from", listOf a), ("predicate", a ~> boolType)] ~> listOf a)
            , (":",      Scheme.forAll 1 0 0 $ \ [a] [] [] -> T.recordType [("head", a), ("tail", listOf a)] ~> listOf a)
            , ("[]",     Scheme.forAll 1 0 0 $ \ [a] [] [] -> listOf a)
            , ("concat", Scheme.forAll 1 0 0 $ \ [a] [] [] -> listOf (listOf a) ~> listOf a)
            , ("map",    Scheme.forAll 2 0 0 $ \ [a, b] [] [] -> T.recordType [("list", listOf a), ("mapping", a ~> b)] ~> listOf b)
            -- , ("..",     Scheme.forAll 0 0 0 $ \ [] [] [] -> infixType intType intType (listOf intType))
            , ("||",     Scheme.forAll 0 0 0 $ \ [] [] [] -> infixType boolType boolType boolType)
            , ("head",   Scheme.forAll 1 0 0 $ \ [a] [] [] -> listOf a ~> a)
            , ("negate", Scheme.forAll 1 0 0 $ \ [a] [] [] -> a ~> a)
            , ("sqrt",   Scheme.forAll 1 0 0 $ \ [a] [] [] -> a ~> a)
            , ("id",     Scheme.forAll 1 0 0 $ \ [a] [] [] -> a ~> a)
            -- , ("zipWith",Scheme.forAll ["a","b","c"] $ \ [a,b,c] [] [] ->
                                      -- (a ~> b ~> c) ~> listOf a ~> listOf b ~> listOf c )
            -- , ("Just",   Scheme.forAll 1 0 0 $ \ [a] [] [] -> a ~> maybeOf a)
            -- , ("Nothing",Scheme.forAll 1 0 0 $ \ [a] [] [] -> maybeOf a)
            -- , ("maybe",  Scheme.forAll ["a", "b"] $ \ [a, b] [] [] -> b ~> (a ~> b) ~> maybeOf a ~> b)
            , ("plus1",  Scheme.forAll 0 0 0 $ \ [] [] [] -> numType ~> numType)
            -- , ("True",   Scheme.forAll 0 0 0 $ \ [] [] [] -> boolType)
            -- , ("False",  Scheme.forAll 0 0 0 $ \ [] [] [] -> boolType)

            , ("runST",  Scheme.forAll 1 0 0 $ \ [a] [] [] -> closedStOf a ~> a)
            ]

list :: [V] -> V
list = foldr cons (V.var "[]")

cons :: V -> V -> V
cons h t = V.var ":" $$: [("head", h), ("tail", t)]

factorialVal :: V
factorialVal =
    V.var "fix" $$
    V.lambda "loop"
    ( \loop ->
        V.lambda "x" $ \x ->
        V.var "if" $$:
        [ ( "condition", V.var "==" $$
                infixArgs x (V.litNum 0) )
        , ( "then", V.litNum 1 )
        , ( "else", V.var "*" $$
                infixArgs x (loop $$ (V.var "-" $$ infixArgs x (V.litNum 1)))
            )
        ]
    )

factorialValNoRecords :: V
factorialValNoRecords =
    V.var "fix" $$
    V.lambda "loop"
    ( \loop ->
        V.lambda "x" $ \x ->
        V.var "bool'" $$
        (V.var "eq" $$ x $$ V.litNum 0) $$
        V.litNum 1 $$
        (V.var "mul" $$ x $$
         (loop $$ (V.var "sub" $$ x $$ V.litNum 1)))
    )

euler1Val :: V
euler1Val =
    V.var "sum" $$
    ( V.var "filter" $$:
        [ ( "from"
          , V.var ".." $$
            infixArgs (V.litNum 1) (V.litNum 1000)
          )
        , ( "predicate",
            V.lambda "x" $ \x ->
            V.var "||" $$ infixArgs
            ( V.var "==" $$ infixArgs
              (V.litNum 0) (V.var "%" $$ infixArgs x (V.litNum 3)) )
            ( V.var "==" $$ infixArgs
              (V.litNum 0) (V.var "%" $$ infixArgs x (V.litNum 5)) )
          )
        ]
    )

solveDepressedQuarticVal :: V
solveDepressedQuarticVal =
    V.lambdaRecord "params" ["e", "d", "c"] $ \[e, d, c] ->
    whereItem "solvePoly" (V.var "id")
    $ \solvePoly ->
    whereItem "sqrts"
    ( V.lambda "x" $ \x ->
        whereItem "r"
        ( V.var "sqrt" $$ x
        ) $ \r ->
        list [r, V.var "negate" $$ r]
    )
    $ \sqrts ->
    V.var "if" $$:
    [ ("condition", V.var "==" $$ infixArgs d (V.litNum 0))
    , ( "then"
      , V.var "concat" $$
        ( V.var "map" $$:
          [ ("list", solvePoly $$ list [e, c, V.litNum 1])
          , ("mapping", sqrts)
          ]
        )
      )
    , ( "else",
        V.var "concat" $$
        ( V.var "map" $$:
          [ ( "list"
            , sqrts $$
              ( V.var "head" $$
                ( solvePoly $$ list
                  [ V.var "negate" $$ (d %* d)
                  , (c %* c) %- (V.litNum 4 %* e)
                  , V.litNum 2 %* c
                  , V.litNum 1
                  ]
                )
              )
            )
          , ( "mapping"
            , V.lambda "x" $ \x ->
              solvePoly $$ list
              [ (c %+ (x %* x)) %- (d %/ x)
              , V.litNum 2 %* x
              , V.litNum 2
              ]
            )
          ]
        )
      )
    ]
    where
        (%+) = inf "+"
        (%-) = inf "-"
        (%*) = inf "*"
        (%/) = inf "/"

inf :: Val.Var -> V -> V -> V
inf str x y = V.var str $$ infixArgs x y

-- factorsVal :: V
-- factorsVal =
--     fix_ $ \loop ->
--     lambdaRecord ["n", "min"] $ \ [n, m] ->
--     if_ ((m %* m) %> n) (list [n]) $
--     if_ ((n %% m) %== litInt 0)
--     (cons m $ loop $$: [("n", n %// m), ("min", m)]) $
--     loop $$: [ ("n", n), ("min", m %+ litInt 1) ]
--     where
--         fix_ f = global "fix" $$ lambda "loop" f
--         if_ b t f =
--             ( nullaryCase "False" f $
--               nullaryCase "True" t $
--               absurd
--             ) $$ fromNom "Bool" b
--         nullaryCase tag handler = _case tag (defer handler)
--         defer = lambda "_" . const
--         (%>) = inf ">"
--         (%%) = inf "%"
--         (%*) = inf "*"
--         (%+) = inf "+"
--         (%//) = inf "//"
--         (%==) = inf "=="
