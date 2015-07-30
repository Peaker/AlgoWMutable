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

import           Prelude.Compat

import           Data.Text (Text)
-- -- import           Control.Lens.Operators
import qualified Data.Map as Map
-- -- import           Data.Monoid (Monoid(..), (<>))
-- -- import qualified Data.Set as Set
import           Type

type TType = T 'TypeT

-- TODO: $$ to be type-classed for TApp vs BApp
-- TODO: TCon "->" instead of TFun

eLet :: Text -> V -> (V -> V) -> V
eLet name val mkBody = lam name body $$ val
    where
        body = mkBody $ var name

whereItem :: Text -> V -> (V -> V) -> V
whereItem name val mkBody = lambda name mkBody $$ val

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
listOf = tInst "List" . Map.singleton "elem"

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

infixType :: TType -> TType -> TType -> TType
infixType a b c = recordType [("l", a), ("r", b)] ~> c

infixArgs :: V -> V -> V
infixArgs l r = recVal [("l", l), ("r", r)]

-- env :: Loaded
env :: Scope s
env = newScope $
    -- Loaded
    -- { loadedGlobalTypes =
        Map.fromList
        [ ("fix",    forAll 1 0 0 $ \ [a] [] [] -> (a ~> a) ~> a)
        , ("if",     forAll 1 0 0 $ \ [a] [] [] -> recordType [("condition", boolType), ("then", a), ("else", a)] ~> a)
        , ("==",     forAll 1 0 0 $ \ [a] [] [] -> infixType a a boolType)
        , (">",      forAll 1 0 0 $ \ [a] [] [] -> infixType a a boolType)
        , ("%",      forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
        , ("*",      forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
        , ("-",      forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
        , ("+",      forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)
        , ("/",      forAll 1 0 0 $ \ [a] [] [] -> infixType a a a)

        , ("bool'",  forAll 1 0 0 $ \ [a] [] [] -> boolType ~> a ~> a ~> a)
        , ("eq",     forAll 1 0 0 $ \ [a] [] [] -> a ~> a ~> boolType)
        , ("mul",    forAll 1 0 0 $ \ [a] [] [] -> a ~> a ~> a)
        , ("sub",    forAll 1 0 0 $ \ [a] [] [] -> a ~> a ~> a)

        , ("//",     forAll 0 0 0 $ \ []  [] [] -> infixType intType intType intType)
        -- , ("sum",    forAll 1 0 0 $ \ [a] [] [] -> listOf a ~> a)
        -- , ("filter", forAll 1 0 0 $ \ [a] [] [] -> recordType [("from", listOf a), ("predicate", a ~> boolType)] ~> listOf a)
        , (":",      forAll 1 0 0 $ \ [a] [] [] -> recordType [("head", a), ("tail", listOf a)] ~> listOf a)
        , ("[]",     forAll 1 0 0 $ \ [a] [] [] -> listOf a)
        , ("concat", forAll 1 0 0 $ \ [a] [] [] -> listOf (listOf a) ~> listOf a)
        , ("map",    forAll 2 0 0 $ \ [a, b] [] [] -> recordType [("list", listOf a), ("mapping", a ~> b)] ~> listOf b)
        -- , ("..",     forAll 0 0 0 $ \ [] [] [] -> infixType intType intType (listOf intType))
        , ("||",     forAll 0 0 0 $ \ [] [] [] -> infixType boolType boolType boolType)
        , ("head",   forAll 1 0 0 $ \ [a] [] [] -> listOf a ~> a)
        , ("negate", forAll 1 0 0 $ \ [a] [] [] -> a ~> a)
        , ("sqrt",   forAll 1 0 0 $ \ [a] [] [] -> a ~> a)
        , ("id",     forAll 1 0 0 $ \ [a] [] [] -> a ~> a)
        -- , ("zipWith",forAll ["a","b","c"] $ \ [a,b,c] [] [] ->
                                  -- (a ~> b ~> c) ~> listOf a ~> listOf b ~> listOf c )
        -- , ("Just",   forAll 1 0 0 $ \ [a] [] [] -> a ~> maybeOf a)
        -- , ("Nothing",forAll 1 0 0 $ \ [a] [] [] -> maybeOf a)
        -- , ("maybe",  forAll ["a", "b"] $ \ [a, b] [] [] -> b ~> (a ~> b) ~> maybeOf a ~> b)
        , ("plus1",  forAll 0 0 0 $ \ [] [] [] -> intType ~> intType)
        -- , ("True",   forAll 0 0 0 $ \ [] [] [] -> boolType)
        -- , ("False",  forAll 0 0 0 $ \ [] [] [] -> boolType)
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
list = foldr cons (global "[]")

cons :: V -> V -> V
cons h t = global ":" $$: [("head", h), ("tail", t)]

factorialVal :: V
factorialVal =
    global "fix" $$
    lambda "loop"
    ( \loop ->
        lambda "x" $ \x ->
        global "if" $$:
        [ ( "condition", global "==" $$
                infixArgs x (litInt 0) )
        , ( "then", litInt 1 )
        , ( "else", global "*" $$
                infixArgs x (loop $$ (global "-" $$ infixArgs x (litInt 1)))
            )
        ]
    )

factorialValNoRecords :: V
factorialValNoRecords =
    global "fix" $$
    lambda "loop"
    ( \loop ->
        lambda "x" $ \x ->
        global "bool'" $$
        (global "eq" $$ x $$ (litInt 0)) $$
        litInt 1 $$
        (global "mul" $$ x $$
         (loop $$ (global "sub" $$ x $$ litInt 1)))
    )

euler1Val :: V
euler1Val =
    global "sum" $$
    ( global "filter" $$:
        [ ("from", global ".." $$ infixArgs (litInt 1) (litInt 1000))
        , ( "predicate",
                lambda "x" $ \x ->
                global "||" $$ infixArgs
                ( global "==" $$ infixArgs
                    (litInt 0) (global "%" $$ infixArgs x (litInt 3)) )
                ( global "==" $$ infixArgs
                    (litInt 0) (global "%" $$ infixArgs x (litInt 5)) )
            )
        ]
    )

solveDepressedQuarticVal :: V
solveDepressedQuarticVal =
    lambdaRecord "params" ["e", "d", "c"] $ \[e, d, c] ->
    whereItem "solvePoly" (global "id")
    $ \solvePoly ->
    whereItem "sqrts"
    ( lambda "x" $ \x ->
        whereItem "r"
        ( global "sqrt" $$ x
        ) $ \r ->
        list [r, global "negate" $$ r]
    )
    $ \sqrts ->
    global "if" $$:
    [ ("condition", global "==" $$ infixArgs d (litInt 0))
    , ( "then",
            global "concat" $$
            ( global "map" $$:
                [ ("list", solvePoly $$ list [e, c, litInt 1])
                , ("mapping", sqrts)
                ]
            )
        )
    , ( "else",
            global "concat" $$
            ( global "map" $$:
                [ ( "list", sqrts $$ (global "head" $$ (solvePoly $$ list
                        [ global "negate" $$ (d %* d)
                        , (c %* c) %- (litInt 4 %* e)
                        , litInt 2 %* c
                        , litInt 1
                        ]))
                    )
                , ( "mapping",
                        lambda "x" $ \x ->
                        solvePoly $$ list
                        [ (c %+ (x %* x)) %- (d %/ x)
                        , litInt 2 %* x
                        , litInt 2
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

inf :: Text -> V -> V -> V
inf str x y = global str $$ infixArgs x y

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
