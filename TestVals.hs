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

-- -- import           Control.Lens.Operators
import qualified Data.Map as Map
-- -- import           Data.Monoid (Monoid(..), (<>))
-- -- import qualified Data.Set as Set
import           Type (T, (~>), ASTTag(..))
import qualified Type
import qualified Val
import qualified Val.Pure as V
import           Val.Pure (V, ($$), ($$:))

import           Prelude.Compat

type TType = T 'Type.TypeT

infixType :: T 'TypeT -> T 'TypeT -> T 'TypeT -> T 'TypeT
infixType a b c = Type.recordType [("l", a), ("r", b)] ~> c

-- TODO: $$ to be type-classed for TApp vs BApp
-- TODO: TCon "->" instead of TFun

eLet :: Val.Var -> V -> (V -> V) -> V
eLet name val mkBody = V.lam name body $$ val
    where
        body = mkBody $ V.var name

whereItem :: Val.Var -> V -> (V -> V) -> V
whereItem name val mkBody = V.lambda name mkBody $$ val

-- openRecordType :: Text -> [(Text, TType)] -> TType
-- openRecordType tv = TRecord . foldr (uncurry RecExtend) (CVar tv)

-- listTypePair :: (Id, Nominal)
-- listTypePair =
--     ( "List"
--     , Nominal
--         { nParams = Map.singleton "elem" tvName
--         , nScheme =
--             CEmpty
--             & CExtend "[]" (recordType [])
--             & CExtend ":" (recordType [("head", tv), ("tail", listOf tv)])
--             & TSum
--             & Scheme.mono
--         }
--     )
--     where
--         tvName = "a"
--         tv = TVar tvName

listOf :: TType -> TType
listOf = Type.tInst "List" . Map.singleton "elem"

-- boolType :: TType
-- boolType = TInst (fst boolTypePair) Map.empty

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

-- env :: Loaded
env :: Type.Scope
env = Type.newScope $
    -- Loaded
    -- { loadedGlobalTypes =
        Map.fromList
        [ ("fix",    Type.forAll 1 0 0 $ \ [a] [] [] -> (a ~> a) ~> a)
        , ("if",     Type.forAll 1 0 0 $ \ [a] [] [] -> Type.recordType [("condition", Type.boolType), ("then", a), ("else", a)] ~> a)
        , ("==",     Type.forAll 1 0 0 $ \ [a] [] [] -> infixType a a Type.boolType)
        , (">",      Type.forAll 1 0 0 $ \ [a] [] [] -> infixType a a Type.boolType)
        , ("%",      Type.forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
        , ("*",      Type.forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
        , ("-",      Type.forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
        , ("+",      Type.forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
        , ("/",      Type.forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)

        , ("bool'",  Type.forAll 1 0 0 $ \ [a] [] [] -> Type.boolType ~> a ~> a ~> a)
        , ("eq",     Type.forAll 1 0 0 $ \ [a] [] [] -> a ~> a ~> Type.boolType)
        , ("mul",    Type.forAll 1 0 0 $ \ [a] [] [] -> a ~> a ~> a)
        , ("sub",    Type.forAll 1 0 0 $ \ [a] [] [] -> a ~> a ~> a)

        , ("//",     Type.forAll 0 0 0 $ \ []  [] [] -> infixType Type.intType Type.intType Type.intType)
        -- , ("sum",    Type.forAll 1 0 0 $ \ [a] [] [] -> listOf a ~> a)
        -- , ("filter", Type.forAll 1 0 0 $ \ [a] [] [] -> recordType [("from", listOf a), ("predicate", a ~> boolType)] ~> listOf a)
        , (":",      Type.forAll 1 0 0 $ \ [a] [] [] -> Type.recordType [("head", a), ("tail", listOf a)] ~> listOf a)
        , ("[]",     Type.forAll 1 0 0 $ \ [a] [] [] -> listOf a)
        , ("concat", Type.forAll 1 0 0 $ \ [a] [] [] -> listOf (listOf a) ~> listOf a)
        , ("map",    Type.forAll 2 0 0 $ \ [a, b] [] [] -> Type.recordType [("list", listOf a), ("mapping", a ~> b)] ~> listOf b)
        -- , ("..",     Type.forAll 0 0 0 $ \ [] [] [] -> infixType intType intType (listOf intType))
        , ("||",     Type.forAll 0 0 0 $ \ [] [] [] -> infixType Type.boolType Type.boolType Type.boolType)
        , ("head",   Type.forAll 1 0 0 $ \ [a] [] [] -> listOf a ~> a)
        , ("negate", Type.forAll 1 0 0 $ \ [a] [] [] -> a ~> a)
        , ("sqrt",   Type.forAll 1 0 0 $ \ [a] [] [] -> a ~> a)
        , ("id",     Type.forAll 1 0 0 $ \ [a] [] [] -> a ~> a)
        -- , ("zipWith",Type.forAll ["a","b","c"] $ \ [a,b,c] [] [] ->
                                  -- (a ~> b ~> c) ~> listOf a ~> listOf b ~> listOf c )
        -- , ("Just",   Type.forAll 1 0 0 $ \ [a] [] [] -> a ~> maybeOf a)
        -- , ("Nothing",Type.forAll 1 0 0 $ \ [a] [] [] -> maybeOf a)
        -- , ("maybe",  Type.forAll ["a", "b"] $ \ [a, b] [] [] -> b ~> (a ~> b) ~> maybeOf a ~> b)
        , ("plus1",  Type.forAll 0 0 0 $ \ [] [] [] -> Type.intType ~> Type.intType)
        -- , ("True",   Type.forAll 0 0 0 $ \ [] [] [] -> boolType)
        -- , ("False",  Type.forAll 0 0 0 $ \ [] [] [] -> boolType)
        ]
    -- , loadedNominals =
    --     Map.fromList
    --     [ listTypePair
    --     , boolTypePair
    --     , polyIdTypePair
    --     , unsafeCoerceTypePair
    --     , ignoredParamTypePair
    --     , xGetterPair
    --     , xGetterPairConstrained
    --     ]
    -- }

list :: [V] -> V
list = foldr cons (V.global "[]")

cons :: V -> V -> V
cons h t = V.global ":" $$: [("head", h), ("tail", t)]

factorialVal :: V
factorialVal =
    V.global "fix" $$
    V.lambda "loop"
    ( \loop ->
        V.lambda "x" $ \x ->
        V.global "if" $$:
        [ ( "condition", V.global "==" $$
                infixArgs x (V.litInt 0) )
        , ( "then", V.litInt 1 )
        , ( "else", V.global "*" $$
                infixArgs x (loop $$ (V.global "-" $$ infixArgs x (V.litInt 1)))
            )
        ]
    )

factorialValNoRecords :: V
factorialValNoRecords =
    V.global "fix" $$
    V.lambda "loop"
    ( \loop ->
        V.lambda "x" $ \x ->
        V.global "bool'" $$
        (V.global "eq" $$ x $$ V.litInt 0) $$
        V.litInt 1 $$
        (V.global "mul" $$ x $$
         (loop $$ (V.global "sub" $$ x $$ V.litInt 1)))
    )

euler1Val :: V
euler1Val =
    V.global "sum" $$
    ( V.global "filter" $$:
        [ ( "from"
          , V.global ".." $$
            infixArgs (V.litInt 1) (V.litInt 1000)
          )
        , ( "predicate",
            V.lambda "x" $ \x ->
            V.global "||" $$ infixArgs
            ( V.global "==" $$ infixArgs
              (V.litInt 0) (V.global "%" $$ infixArgs x (V.litInt 3)) )
            ( V.global "==" $$ infixArgs
              (V.litInt 0) (V.global "%" $$ infixArgs x (V.litInt 5)) )
          )
        ]
    )

solveDepressedQuarticVal :: V
solveDepressedQuarticVal =
    V.lambdaRecord "params" ["e", "d", "c"] $ \[e, d, c] ->
    whereItem "solvePoly" (V.global "id")
    $ \solvePoly ->
    whereItem "sqrts"
    ( V.lambda "x" $ \x ->
        whereItem "r"
        ( V.global "sqrt" $$ x
        ) $ \r ->
        list [r, V.global "negate" $$ r]
    )
    $ \sqrts ->
    V.global "if" $$:
    [ ("condition", V.global "==" $$ infixArgs d (V.litInt 0))
    , ( "then"
      , V.global "concat" $$
        ( V.global "map" $$:
          [ ("list", solvePoly $$ list [e, c, V.litInt 1])
          , ("mapping", sqrts)
          ]
        )
      )
    , ( "else",
        V.global "concat" $$
        ( V.global "map" $$:
          [ ( "list"
            , sqrts $$
              ( V.global "head" $$
                ( solvePoly $$ list
                  [ V.global "negate" $$ (d %* d)
                  , (c %* c) %- (V.litInt 4 %* e)
                  , V.litInt 2 %* c
                  , V.litInt 1
                  ]
                )
              )
            )
          , ( "mapping"
            , V.lambda "x" $ \x ->
              solvePoly $$ list
              [ (c %+ (x %* x)) %- (d %/ x)
              , V.litInt 2 %* x
              , V.litInt 2
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

inf :: Val.GlobalId -> V -> V -> V
inf str x y = V.global str $$ infixArgs x y

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
