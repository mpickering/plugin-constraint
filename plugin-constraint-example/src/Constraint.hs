{-# LANGUAGE FlexibleInstances #-}
module Constraint where

import GhcPlugins hiding (unitExpr)
import TcRnTypes
import HsExpr
import HsBinds
import HsExtension
import ConLike
import TcRnMonad
import TcEnv
import Control.Arrow
import TcEvidence
import TcSMonad hiding (tcLookupId)
import TcSimplify
import Bag
import IfaceEnv

-- Where some Names used by the compiler are defined.
import PrelNames

-- Installing the plugin
plugin :: Plugin
plugin = defaultPlugin  {
  typeCheckResultAction = install
  , pluginRecompile = impurePlugin
  }

-- The main plugin function.
install :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
install _ ms tc_gbl = do
  -- Get the `Id`s that we need, these ones helpfully are already defined
  -- in `PrelNames` and `TysWiredIn`.
  io_tycon <- tcLookupTyCon ioTyConName
  print_id    <- tcLookupId printName

  -- Generate the evidence for `Show ()` which we will pass to `print`
  (dict_var, showUnitEv) <- generateDictionary

  -- Make the `Id` for the new binding
  binding_name <- newGlobalBinder (ms_mod ms) (mkVarOcc "myBinding") (noSrcSpan)
  let binding_id = mkVanillaGlobal binding_name (mkTyConApp io_tycon [unitTy])

  -- Make the new bind
  let new_bind = mkNewBind io_tycon print_id binding_id dict_var showUnitEv

  -- Add our new binding to existing binds.
  let binds = tcg_binds tc_gbl
  return (tc_gbl {tcg_binds = binds `unionBags` new_bind })

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
--
-- There is quite a lot of boilerplate and the compiler won't tell
-- you where you went wrong unless -dcore-lint is enabled.
mkNewBind :: TyCon -> Id -> Id -> Id -> TcEvBinds -> LHsBinds GhcTc
mkNewBind io_tycon print_id bind_name dict_var ev = unitBag (noLoc bind)
  where
    bind = FunBind emptyNameSet (noLoc bind_name) mg idHsWrapper []

    mg = MG mg_tc (noLoc [match]) Generated
    mg_tc = MatchGroupTc [] (mkTyConApp io_tycon [unitTy])

    match = noLoc (Match noExt match_ctxt [] grhss)
    match_ctxt = FunRhs (noLoc (varName bind_name)) Prefix SrcLazy

    grhss = GRHSs noExt [(noLoc (GRHS noExt [] rhs))] (noLoc (EmptyLocalBinds noExt))
    rhs = noLoc (HsApp noExt (noLoc $ HsWrap noExt wrapper printExpr) unitExpr)

    printExpr = HsVar noExt (noLoc print_id)
    unitExpr = noLoc $ HsConLikeOut noExt (RealDataCon unitDataCon)

    -- How we are going to apply the necessary type arguments
    wrapper = mkWpLet ev <.> mkWpEvVarApps [dict_var] <.> mkWpTyApps [unitTy]





