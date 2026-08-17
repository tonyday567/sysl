{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

-- | System L with polynomial types and @These@ covariable boundaries.
--
-- This module rebuilds the original hand-rolled @Loop (,) (->)@ interpreter
-- as a @circuits@ client:
--
-- * User-facing types are promoted to 'Circuit.Poly' polynomials via 'SysLTy'.
-- * Command results are expressed with 'Data.These' boundaries, matching the
--   inclusive tensor in "Circuit.Channel".
-- * The syntactic target is the free SMC @Sym (->)@; boundaries use 'These'
--   at the value level.
-- * A streaming reading is provided via 'Circuit.Process'.
--
-- The original four regression tests are preserved as 'testId', 'testThen',
-- 'testIdLoop' and 'testThenLoop'.
module SysL
  ( -- * Types
    Ty (..),
    SysLTy,
    Domain,

    -- * Values and boundaries
    Val (..),
    Output,
    Result,
    Env,

    -- * Syntax
    Command (..),
    Value (..),
    Term (..),
    Coterm (..),

    -- * Direct evaluator
    evalCommand,
    evalValue,
    evalTerm,
    evalCoterm,
    lookupEnv,

    -- * Polynomial view
    PolyVal (..),

    -- * Sym SMC compiler
    SMCThese,
    commandToSym,
    termToSym,
    cotermToSym,

    -- * Process interpreter
    evalProcess,

    -- * Then as optic
    thenLens,
    applyThen,

    -- * Regression tests
    testId,
    testThen,
    testIdLoop,
    testThenLoop,
  )
where

import Circuit.Layer (run)
import Circuit.Net (Sym (..))
import Circuit.Poly
  ( Eval (..),
    Mono,
    Morphism (..),
    Poly (..),
    applyLens,
    lens,
  )
import Circuit.Process (Process (..))
import Data.Kind (Type)
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Types as polynomials
-- ---------------------------------------------------------------------------

-- | User-facing SysL type syntax.
data Ty
  = One
  | Times Ty Ty
  | Zero
  | Plus Ty Ty
  | Hom Ty Ty
  | GradedHom Ty [Ty]
  | Then Ty Ty
  deriving (Show, Eq)

-- | Promoted polynomial encoding of a SysL type.
--
-- 'Hom', 'Then' and the graded variant are represented as monomial
-- lenses / dependent optics, which is the natural polynomial reading of
-- functions with a backward map.
type family SysLTy (t :: Ty) :: Poly where
  SysLTy 'One = 'Const ()
  SysLTy ('Times a b) = 'Prod (SysLTy a) (SysLTy b)
  SysLTy 'Zero = 'Const Void
  SysLTy ('Plus a b) = 'Sum (SysLTy a) (SysLTy b)
  SysLTy ('Hom a b) = Mono (Domain a) (Domain b)
  SysLTy ('Then a b) = Mono (Domain a) (Domain b)
  SysLTy ('GradedHom a bs) = GradedPoly a bs

-- | Closed value domain for a SysL type.
type family Domain (t :: Ty) :: Type where
  Domain 'One = ()
  Domain ('Times a b) = (Domain a, Domain b)
  Domain 'Zero = Void
  Domain ('Plus a b) = Either (Domain a) (Domain b)
  Domain ('Hom a b) = Domain a -> Domain b
  Domain ('Then a b) = Domain a -> Domain b
  Domain ('GradedHom a bs) = Domain a -> GradedResult bs

-- | Result type for a graded list of return types.
type family GradedResult (bs :: [Ty]) :: Type where
  GradedResult '[] = Void
  GradedResult (b ': bs) = Either (Domain b) (GradedResult bs)

-- | Polynomial for a graded homomorphism: a sum of monomial lenses.
type family GradedPoly (a :: Ty) (bs :: [Ty]) :: Poly where
  GradedPoly _ '[] = 'Const Void
  GradedPoly a (b ': bs) = 'Sum (Mono (Domain a) (Domain b)) (GradedPoly a bs)

-- ---------------------------------------------------------------------------
-- Values and boundaries
-- ---------------------------------------------------------------------------

-- | A result is now a covariable boundary using the inclusive @These@ tensor.
--
-- * 'This' carries a residual output (slot >= 1).
-- * 'That' carries a focus output (slot 0).
-- * 'These' carries both residual and focus.
--
-- This follows the convention in "Circuit.Channel": 'This' is the
-- feedback / residual branch and 'That' is the payload / focus branch.
type Result v = These (Output v) (Output v)

-- | An output is a slot together with a value.
type Output v = (Int, Val v)

-- | Runtime values, parametric in the opaque domain type @v@.
data Val v
  = VUnit
  | VPair (Val v) (Val v)
  | VLeft (Val v)
  | VRight (Val v)
  | VFun (Val v -> Result v)
  | VGradedFun (Val v -> Result v)
  | VThen (Val v) (Val v -> Result v)
  | VEmbed v

instance (Eq v) => Eq (Val v) where
  VUnit == VUnit = True
  VPair a b == VPair c d = a == c && b == d
  VLeft a == VLeft b = a == b
  VRight a == VRight b = a == b
  VEmbed x == VEmbed y = x == y
  _ == _ = False

instance (Show v) => Show (Val v) where
  show VUnit = "VUnit"
  show (VPair a b) = "VPair (" <> show a <> ") (" <> show b <> ")"
  show (VLeft a) = "VLeft (" <> show a <> ")"
  show (VRight b) = "VRight (" <> show b <> ")"
  show (VFun _) = "VFun <fn>"
  show (VGradedFun _) = "VGradedFun <fn>"
  show (VThen a _) = "VThen (" <> show a <> ") <fn>"
  show (VEmbed v) = "VEmbed (" <> show v <> ")"

-- | Input environment: de Bruijn indexed list of values.
type Env v = [Val v]

lookupEnv :: Int -> Env v -> Val v
lookupEnv 0 (x : _) = x
lookupEnv n (_ : xs) = lookupEnv (n - 1) xs
lookupEnv _ [] = error "lookupEnv: index out of range"

-- ---------------------------------------------------------------------------
-- Syntax
-- ---------------------------------------------------------------------------

data Command v = Cut (Term v) (Coterm v)
  deriving (Show)

data Value v
  = Var Int
  | TensorIntro (Value v) (Value v)
  | PlusIntroL (Value v)
  | PlusIntroR (Value v)
  | HomComatch (Command v)
  | GradedHomComatch (Command v)
  | Lit (Val v)
  deriving (Show)

data Term v
  = Embed (Value v)
  | Mu (Command v)
  | ThenComatch (Command v)
  deriving (Show)

data Coterm v
  = Covar Int
  | Comu (Command v)
  | TensorMatch (Command v)
  | PlusMatch (Command v) (Command v)
  | HomCointro (Term v) (Coterm v)
  | GradedHomCointro (Term v) [Coterm v]
  | ThenCointro (Coterm v) (Coterm v)
  deriving (Show)

-- ---------------------------------------------------------------------------
-- Polynomial value view
-- ---------------------------------------------------------------------------

-- | Convert between the runtime 'Val' representation and the polynomial
-- 'Eval' representation for a closed SysL type.
class PolyVal (t :: Ty) where
  valToEval :: Val v -> Eval (SysLTy t) v
  evalToVal :: Eval (SysLTy t) v -> Val v

instance PolyVal 'One where
  valToEval VUnit = EK ()
  valToEval v = error $ "valToEval One: " <> show' v
  evalToVal (EK ()) = VUnit

instance (PolyVal a, PolyVal b) => PolyVal ('Times a b) where
  valToEval (VPair x y) = EP (valToEval @a x, valToEval @b y)
  valToEval v = error $ "valToEval Times: " <> show' v
  evalToVal (EP (x, y)) = VPair (evalToVal @a x) (evalToVal @b y)

instance PolyVal 'Zero where
  valToEval v = error $ "valToEval Zero: " <> show' v
  evalToVal (EK v) = absurd v

instance (PolyVal a, PolyVal b) => PolyVal ('Plus a b) where
  valToEval (VLeft x) = ES (Left (valToEval @a x))
  valToEval (VRight y) = ES (Right (valToEval @b y))
  valToEval v = error $ "valToEval Plus: " <> show' v
  evalToVal (ES (Left x)) = VLeft (evalToVal @a x)
  evalToVal (ES (Right y)) = VRight (evalToVal @b y)

-- ---------------------------------------------------------------------------
-- Direct evaluator with These boundaries
-- ---------------------------------------------------------------------------

evalCommand :: Command v -> Env v -> Result v
evalCommand (Cut t k) env =
  case evalTerm t env of
    This out -> This out
    That val -> evalCoterm k env val
    These res val -> combine res (evalCoterm k env val)
  where
    combine res (This res') = These res res'
    combine res (That foc) = These res foc
    combine res (These res' foc) = These (merge res res') foc
    merge (i, _) (j, _) = (max i j, VUnit) -- residual merge keeps largest slot

evalValue :: Value v -> Env v -> Val v
evalValue (Var i) env = lookupEnv i env
evalValue (TensorIntro v1 v2) env = VPair (evalValue v1 env) (evalValue v2 env)
evalValue (PlusIntroL v) env = VLeft (evalValue v env)
evalValue (PlusIntroR v) env = VRight (evalValue v env)
evalValue (HomComatch cmd) env =
  VFun $ \x ->
    evalCommand cmd (x : env)
evalValue (GradedHomComatch cmd) env =
  VGradedFun $ \x ->
    evalCommand cmd (x : env)
evalValue (Lit v) _ = v

evalTerm :: Term v -> Env v -> These (Output v) (Val v)
evalTerm (Embed v) env = That (evalValue v env)
evalTerm (Mu cmd) env =
  case evalCommand cmd env of
    This out -> This out
    That (0, val) -> That val
    That out -> This out
    These res (0, val) -> These res val
    These res foc -> These res (snd foc)
evalTerm (ThenComatch cmd) env =
  let fwdA = case evalCommand cmd env of
        That (1, v) -> v
        These _ (1, v) -> v
        _ -> error "ThenComatch: expected slot 1 for fwd a"
      bwCont bwA = evalCommand cmd (bwA : env)
   in That (VThen fwdA bwCont)

evalCoterm :: Coterm v -> Env v -> Val v -> Result v
evalCoterm (Covar i) _env val =
  if i == 0 then That (0, val) else This (i, val)
evalCoterm (Comu cmd) env val = evalCommand cmd (val : env)
evalCoterm (TensorMatch cmd) env (VPair x y) = evalCommand cmd (x : y : env)
evalCoterm (TensorMatch _) _ v = error $ "TensorMatch: not a pair: " <> show' v
evalCoterm (PlusMatch c1 _) env (VLeft x) = evalCommand c1 (x : env)
evalCoterm (PlusMatch _ c2) env (VRight y) = evalCommand c2 (y : env)
evalCoterm (PlusMatch _ _) _ v = error $ "PlusMatch: not a sum: " <> show' v
evalCoterm (HomCointro t k) env f =
  case evalTerm t env of
    This out -> This out
    That arg -> case f of
      VFun g -> case g arg of
        This out -> This out
        That (_, v) -> evalCoterm k env v
        These out (_, v) -> combine out (evalCoterm k env v)
      _ -> error "HomCointro: not a function"
    These res arg -> case f of
      VFun g -> case g arg of
        This out -> These res out
        That (_, v) -> combine res (evalCoterm k env v)
        These out (_, v) -> combine (merge res out) (evalCoterm k env v)
      _ -> error "HomCointro: not a function"
  where
    combine res (This res') = These res res'
    combine res (That foc) = These res foc
    combine res (These res' foc) = These (merge res res') foc
    merge (i, _) (j, _) = (max i j, VUnit)
evalCoterm (GradedHomCointro t coterms) env f =
  case evalTerm t env of
    This out -> This out
    That arg -> case f of
      VGradedFun g -> case g arg of
        This out -> This out
        That (slot, v) -> evalCoterm (coterms !! slot) env v
        These out (slot, v) -> combine out (evalCoterm (coterms !! slot) env v)
      _ -> error "GradedHomCointro: not a graded function"
    These res arg -> case f of
      VGradedFun g -> case g arg of
        This out -> These res out
        That (slot, v) -> combine res (evalCoterm (coterms !! slot) env v)
        These out (slot, v) -> combine (merge res out) (evalCoterm (coterms !! slot) env v)
      _ -> error "GradedHomCointro: not a graded function"
  where
    combine res (This res') = These res res'
    combine res (That foc) = These res foc
    combine res (These res' foc) = These (merge res res') foc
    merge (i, _) (j, _) = (max i j, VUnit)
evalCoterm (ThenCointro k1 k2) env val =
  case val of
    VThen fwdA cont ->
      case evalCoterm k1 env fwdA of
        This (_, residual) ->
          case cont residual of
            This out -> This out
            That (_, fwdB) -> evalCoterm k2 env fwdB
            These out (_, fwdB) -> combine out (evalCoterm k2 env fwdB)
        That (_, residual) ->
          case cont residual of
            This out -> This out
            That (_, fwdB) -> evalCoterm k2 env fwdB
            These out (_, fwdB) -> combine out (evalCoterm k2 env fwdB)
        These _ (_, residual) ->
          case cont residual of
            This out -> This out
            That (_, fwdB) -> evalCoterm k2 env fwdB
            These out (_, fwdB) -> combine out (evalCoterm k2 env fwdB)
    _ -> error "ThenCointro: expected VThen"
  where
    combine res (This res') = These res res'
    combine res (That foc) = These res foc
    combine res (These res' foc) = These (merge res res') foc
    merge (i, _) (j, _) = (max i j, VUnit)

show' :: Val v -> String
show' VUnit = "VUnit"
show' (VPair _ _) = "VPair"
show' (VLeft _) = "VLeft"
show' (VRight _) = "VRight"
show' (VFun _) = "VFun"
show' (VGradedFun _) = "VGradedFun"
show' (VThen _ _) = "VThen"
show' (VEmbed _) = "VEmbed"

-- ---------------------------------------------------------------------------
-- Sym SMC compiler
-- ---------------------------------------------------------------------------

-- | Type synonym for the free symmetric monoidal target.
--
-- @Sym (->)@ is the free SMC over plain functions.  Boundaries are still
-- expressed with 'These' at the value level, but the free category itself
-- uses the cartesian @(,)@ tensor for 'SymPar' wiring rather than the
-- inclusive 'These' tensor.  This avoids the impossibility of a 'Traced'
-- instance for 'These'.
type SMCThese = Sym (->)

-- ---------------------------------------------------------------------------

commandToSym :: Command v -> SMCThese (Env v) (Result v)
commandToSym (Cut t k) = SymLift $ \env ->
  case run (termToSym t) env of
    This out -> This out
    That val -> run (cotermToSym k) (env, val)
    These res val -> combine res (run (cotermToSym k) (env, val))
  where
    combine res (This res') = These res res'
    combine res (That foc) = These res foc
    combine res (These res' foc) = These (merge res res') foc
    merge (i, _) (j, _) = (max i j, VUnit)

termToSym :: Term v -> SMCThese (Env v) (These (Output v) (Val v))
termToSym (Embed v) = SymLift $ \env -> That (evalValue v env)
termToSym (Mu cmd) = SymLift $ \env ->
  case run (commandToSym cmd) env of
    This out -> This out
    That (0, val) -> That val
    That out -> This out
    These res (0, val) -> These res val
    These res foc -> These res (snd foc)
termToSym (ThenComatch cmd) = SymLift $ \env ->
  let fwdA = case run (commandToSym cmd) env of
        That (1, v) -> v
        These _ (1, v) -> v
        _ -> error "ThenComatch: expected slot 1 for fwd a"
      bwCont bwA = run (commandToSym cmd) (bwA : env)
   in That (VThen fwdA bwCont)

cotermToSym :: Coterm v -> SMCThese (Env v, Val v) (Result v)
cotermToSym (Covar i) = SymLift $ \(_, val) ->
  if i == 0 then That (0, val) else This (i, val)
cotermToSym (Comu cmd) = SymLift $ \(env, val) ->
  run (commandToSym cmd) (val : env)
cotermToSym (TensorMatch cmd) = SymLift $ \(env, val) ->
  case val of
    VPair x y -> run (commandToSym cmd) (x : y : env)
    _ -> error $ "TensorMatch: not a pair: " <> show' val
cotermToSym (PlusMatch c1 c2) = SymLift $ \(env, val) ->
  case val of
    VLeft x -> run (commandToSym c1) (x : env)
    VRight y -> run (commandToSym c2) (y : env)
    _ -> error $ "PlusMatch: not a sum: " <> show' val
cotermToSym (HomCointro t k) = SymLift $ \(env, val) ->
  case run (termToSym t) env of
    This out -> This out
    That arg -> case val of
      VFun f -> case f arg of
        This out -> This out
        That (_, v) -> run (cotermToSym k) (env, v)
        These out (_, v) -> combine out (run (cotermToSym k) (env, v))
      _ -> error "HomCointro: not a function"
    These res arg -> case val of
      VFun f -> case f arg of
        This out -> These res out
        That (_, v) -> combine res (run (cotermToSym k) (env, v))
        These out (_, v) -> combine (merge res out) (run (cotermToSym k) (env, v))
      _ -> error "HomCointro: not a function"
  where
    combine res (This res') = These res res'
    combine res (That foc) = These res foc
    combine res (These res' foc) = These (merge res res') foc
    merge (i, _) (j, _) = (max i j, VUnit)
cotermToSym (GradedHomCointro t coterms) = SymLift $ \(env, val) ->
  case run (termToSym t) env of
    This out -> This out
    That arg -> case val of
      VGradedFun f -> case f arg of
        This out -> This out
        That (slot, v) -> run (cotermToSym (coterms !! slot)) (env, v)
        These out (slot, v) -> combine out (run (cotermToSym (coterms !! slot)) (env, v))
      _ -> error "GradedHomCointro: not a graded function"
    These res arg -> case val of
      VGradedFun f -> case f arg of
        This out -> These res out
        That (slot, v) -> combine res (run (cotermToSym (coterms !! slot)) (env, v))
        These out (slot, v) -> combine (merge res out) (run (cotermToSym (coterms !! slot)) (env, v))
      _ -> error "GradedHomCointro: not a graded function"
  where
    combine res (This res') = These res res'
    combine res (That foc) = These res foc
    combine res (These res' foc) = These (merge res res') foc
    merge (i, _) (j, _) = (max i j, VUnit)
cotermToSym (ThenCointro k1 k2) = SymLift $ \(env, val) ->
  case val of
    VThen fwdA cont ->
      case run (cotermToSym k1) (env, fwdA) of
        This (_, residual) -> dispatch residual
        That (_, residual) -> dispatch residual
        These _ (_, residual) -> dispatch residual
      where
        dispatch residual =
          case cont residual of
            This out -> This out
            That (_, fwdB) -> run (cotermToSym k2) (env, fwdB)
            These out (_, fwdB) -> combine out (run (cotermToSym k2) (env, fwdB))
        combine res (This res') = These res res'
        combine res (That foc) = These res foc
        combine res (These res' foc) = These (merge res res') foc
        merge (i, _) (j, _) = (max i j, VUnit)
    _ -> error "ThenCointro: expected VThen"

-- ---------------------------------------------------------------------------
-- Process interpreter
-- ---------------------------------------------------------------------------

-- | Streaming interpreter: each input is a fresh environment, each output is
-- the focus value of the term.  Residual escape is a run-time error, which is
-- the expected behaviour for a closed term consumed by a process.
evalProcess :: Term v -> Process (Env v) (Val v)
evalProcess t = Process inject step extract
  where
    inject env = env
    step _ env = env
    extract env =
      case evalTerm t env of
        That val -> val
        _ -> error "evalProcess: term escaped to a covariable"

-- ---------------------------------------------------------------------------
-- Then as polynomial optic
-- ---------------------------------------------------------------------------

-- | Build a 'Then'-style lens from explicit forward and backward maps.
--
-- The forward map @a -> b@ and backward map @a -> b -> a@ form a dependent
-- lens @Mono a a -> Mono b b@ in 'Circuit.Poly'.
thenLens ::
  (Val v -> Val v) ->
  (Val v -> Val v -> Val v) ->
  Morphism (Mono (Val v) (Val v)) (Mono (Val v) (Val v))
thenLens f g = lens f (\a db -> g a db)

-- | Apply a 'Then' lens to an input value, returning the forward output and
-- the backward continuation.
applyThen ::
  Morphism (Mono (Val v) (Val v)) (Mono (Val v) (Val v)) ->
  Val v ->
  (Val v, Val v -> Val v)
applyThen m a = applyLens m a

-- ---------------------------------------------------------------------------
-- Regression tests
-- ---------------------------------------------------------------------------

-- | Identity via Hom: @(\x -> x) VUnit@.
testId :: Result ()
testId =
  evalCommand
    ( Cut
        (Embed (HomComatch (Cut (Embed (Var 0)) (Covar 0))))
        (HomCointro (Embed (Var 0)) (Covar 0))
    )
    [VUnit]

-- | Thread a Double through Then.
testThen :: Result Double
testThen =
  let val = VThen (VEmbed 1.0) (\x -> That (0, x))
   in evalCommand
        ( Cut
            (Embed (Lit val))
            ( ThenCointro
                (Comu (Cut (Embed (Var 0)) (Covar 1)))
                (Comu (Cut (Embed (Var 0)) (Covar 0)))
            )
        )
        []

-- | Identity test compiled to Sym.
testIdLoop :: Result ()
testIdLoop =
  run
    ( commandToSym
        ( Cut
            (Embed (HomComatch (Cut (Embed (Var 0)) (Covar 0))))
            (HomCointro (Embed (Var 0)) (Covar 0))
        )
    )
    [VUnit]

-- | Then test compiled to Sym.
testThenLoop :: Result Double
testThenLoop =
  let val = VThen (VEmbed 1.0) (\x -> That (0, x))
   in run
        ( commandToSym
            ( Cut
                (Embed (Lit val))
                ( ThenCointro
                    (Comu (Cut (Embed (Var 0)) (Covar 1)))
                    (Comu (Cut (Embed (Var 0)) (Covar 0)))
                )
            )
        )
        [val]
