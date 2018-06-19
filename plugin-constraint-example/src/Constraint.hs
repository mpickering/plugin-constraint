{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
module Constraint where

import GhcPlugins hiding (unitExpr)
import TcRnTypes
import HsExpr
import HsBinds
import HsExtension
import TcRnMonad
import TcEnv
import Control.Arrow
import TcEvidence
import TcSMonad hiding (tcLookupId)
import TcSimplify
import Bag
import IfaceEnv
import HsUtils
import TcExpr
import TcHsSyn
import TcType
import RnExpr
import Convert
import RnEnv

-- Where some Names used by the compiler are defined.
import PrelNames

-- TH Stuff
import Language.Haskell.TH.Syntax (Q, runQ)

-- Installing the plugin
plugin :: Plugin
plugin = defaultPlugin  {
  typeCheckResultAction = install
  , pluginRecompile = impurePlugin
  }

-- The main plugin function.
install :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
install _ ms tc_gbl = do
  rn_expr <- mkNewExprRn
  tc_expr <- mkNewExprTc
  th_expr <- mkNewExprTh
  ps_expr <- mkNewExprPs

  -- Make the new bind
  new_bind_tc <- mkNewBind "tc" ms tc_expr
  new_bind_rn <- mkNewBind "rn" ms rn_expr
  new_bind_th <- mkNewBind "th" ms th_expr
  new_bind_ps <- mkNewBind "ps" ms ps_expr
  let new_binds = new_bind_tc `unionBags` new_bind_rn
                              `unionBags` new_bind_th
                              `unionBags` new_bind_ps


  -- Add our new binding to existing binds.
  let binds = tcg_binds tc_gbl
  return (tc_gbl {tcg_binds = binds `unionBags` new_binds  })

-- Generates the evidence for `Show ()`.
generateDictionary :: TcM (Var, TcEvBinds)
generateDictionary = do
  showTyCon <- tcLookupTyCon showClassName
  dictName <- newName (mkDictOcc (mkVarOcc "magic"))
  let dict_ty = (mkTyConApp showTyCon [ unitTy ])
      dict_var = mkVanillaGlobal dictName dict_ty
  ev <- getDictionaryBindings dict_var
  return (dict_var, ev)

-- Pass in a variable `x` which has type `Show ()` (for example) to generate
-- evidence for `Show ()` which will be bound to `x`.
getDictionaryBindings :: Var -> TcM TcEvBinds
getDictionaryBindings dict_var = do
    loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
    let nonC = mkNonCanonical CtWanted
            { ctev_pred = varType dict_var
            , ctev_nosh = WDeriv
            , ctev_dest = EvVarDest dict_var
            , ctev_loc = loc
            }
        wCs = mkSimpleWC [cc_ev nonC]
    (_, evBinds) <- second evBindMapBinds <$> runTcS (solveWanteds wCs)
    return (EvBinds evBinds)


-- Makes the new typechecked binding
--
-- myBinding = print ()
mkNewBind :: String -> ModSummary -> LHsExpr GhcTc -> TcM (LHsBinds GhcTc)
mkNewBind suffix ms rhs = do
  io_tycon <- tcLookupTyCon ioTyConName
  -- Make the `Id` for the new binding
  let var_name = "myBinding_" ++ suffix
  bind_name <- newGlobalBinder (ms_mod ms) (mkVarOcc var_name) (noSrcSpan)
  let
    bind_id = mkVanillaGlobal bind_name (mkTyConApp io_tycon [unitTy])
    bind = FunBind emptyNameSet (noLoc bind_id) mg idHsWrapper []

    mg = MG mg_tc (noLoc [match]) Generated
    mg_tc = MatchGroupTc [] (mkTyConApp io_tycon [unitTy])

    match = noLoc (Match noExt match_ctxt [] grhss)
    match_ctxt = FunRhs (noLoc bind_name) Prefix SrcLazy

    grhss = GRHSs noExt [(noLoc (GRHS noExt [] rhs))] (noLoc (EmptyLocalBinds noExt))
  return (unitBag (noLoc bind))


-- | Check that an expression has the expected type.
typecheckExpr :: Type -> LHsExpr GhcRn -> TcM (LHsExpr GhcTc)
typecheckExpr t e = do
  -- Typecheck the expression and capture generated constraints
  (unwrapped_expr, wanteds) <- captureConstraints (tcMonoExpr e (Check t))
  -- Create the wrapper
  wrapper <- mkWpLet . EvBinds . evBindMapBinds . snd
              <$> runTcS ( solveWanteds wanteds )
  -- Apply the wrapper
  let final_expr = mkLHsWrap wrapper unwrapped_expr
  -- Zonk to instantiate type variables
  zonkTopLExpr final_expr

renameExpr :: LHsExpr GhcPs -> TcM (LHsExpr GhcRn)
renameExpr e = do
  (e', _) <- rnLExpr e
  return e'

liftQ :: Q a -> TcM a
liftQ = liftIO . runQ

{-================== The Four Implementations ==================-}

-- Creates the already typechecked expression `print ()`
--
-- There is quite a lot of boilerplate and the compiler won't tell
-- you where you went wrong unless -dcore-lint is enabled.
mkNewExprTc :: TcM (LHsExpr GhcTc)
mkNewExprTc = do
  -- Get the `Id`s that we need, these ones helpfully are already defined
  -- in `PrelNames` and `TysWiredIn`.
  print_id    <- tcLookupId printName

  -- Generate the evidence for `Show ()` which we will pass to `print`
  (dict_var, showUnitEv) <- generateDictionary
  let
    rhs = nlHsApp (mkLHsWrap wrapper printExpr) unitExpr

    printExpr = nlHsVar print_id
    unitExpr = nlHsDataCon unitDataCon

    -- How we are going to apply the necessary type arguments
    wrapper = mkWpLet showUnitEv <.> mkWpEvVarApps [dict_var] <.> mkWpTyApps [unitTy]
  return rhs

-- Creates a `LHsExpr GhcRn` which we then typecheck to turn into
-- a `LHsExpr GhcTc`. The compiler will raise an error to the user if you
-- made a mistake in constructing the term.
mkNewExprRn :: TcM (LHsExpr GhcTc)
mkNewExprRn = do
  -- The names we want to use happen to already be in PrelNames so we use
  -- them directly.
  let print_occ = mkRdrUnqual (mkVarOcc "print")
  print_name <- lookupOccRn print_occ
  let raw_expr = nlHsApp (nlHsVar print_name) (nlHsVar (dataConName unitDataCon))
  io_tycon <- tcLookupTyCon ioTyConName
  let exp_type = mkTyConApp io_tycon [unitTy]
  typecheckExpr exp_type raw_expr

-- An example of how to construct a value from a `LHsExpr GhcPs`.
-- Making sure things are in the right namespace is sometimes a bit
-- awkward.
mkNewExprPs :: TcM (LHsExpr GhcTc)
mkNewExprPs  = do

  let
    print_occ = mkRdrUnqual (mkVarOcc "print")
    unit_occ = nameRdrName (dataConName unitDataCon)
    ps_expr = nlHsApp (nlHsVar print_occ)
                      (nlHsVar unit_occ)

  io_tycon <- tcLookupTyCon ioTyConName
  let exp_type = mkTyConApp io_tycon [unitTy]
  renameExpr ps_expr >>= typecheckExpr exp_type

-- Creates a `TH.Exp` using a quasiquoter before renaming
-- and typechecking to create an `LHsExpr`. This is convenient as you
-- don't have to write out the syntax.
mkNewExprTh :: TcM (LHsExpr GhcTc)
mkNewExprTh = do
  th_expr <- liftQ [| print () |]
  ps_expr <- case convertToHsExpr noSrcSpan th_expr of
    Left _err -> error "Bad expression"
    Right res -> return res

  io_tycon <- tcLookupTyCon ioTyConName
  let exp_type = mkTyConApp io_tycon [unitTy]
  renameExpr ps_expr >>= typecheckExpr exp_type



