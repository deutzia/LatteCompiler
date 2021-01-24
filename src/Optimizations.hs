{-# Options -Wall -Wname-shadowing #-}
module Optimizations where

import qualified Data.Graph as G
import qualified Data.Maybe as Maybe
import qualified Data.Set as S
import qualified Data.Map as M

import qualified Quadruples as Q

type Computation = (Q.Op, Q.Location, Q.Location)

type Env =
    (M.Map Q.Location Q.Location, -- substitutions, so new locations
        M.Map Computation Q.Location, -- derived from quadruples
        M.Map String Q.Location, -- derived from fetching variables
        M.Map (Q.Location, Q.Location) Q.Location -- derived from readptr
    )

optimizeQuads :: [([Q.Block], [String])] -> [([Q.Block], [String])]
optimizeQuads = map (\(blocks, args) ->
    let
        (_, blocks') =
            foldl
                (\(env, bs) b ->
                    let (env', b') = lcseSingleBlock env b in
                    (env', b' : bs))
                ((M.empty, M.empty, M.empty, M.empty), [])
                blocks
    in
--    let blocks' = blocks in
    (removeDeadBlocks (reverse blocks'), args))

lcseSingleBlock :: Env -> Q.Block -> (Env, Q.Block)
lcseSingleBlock (subs, qMap, vMap, _) (Q.Block label vars quads blockEnd) =
    let vMap' = foldr M.delete vMap vars in
    let env = (subs, qMap, vMap', M.empty) in
--    let env = (M.empty, M.empty, M.empty, M.empty) in
    let (resultEnv@(subs', _, _, _), quads') = lcseQuads env quads in
    let
        blockEnd' = case blockEnd of
            be@(Q.UnconditionalJump _) -> be
            (Q.ConditionalJump cond label0 label1) -> case cond of
                Q.Loc l -> let l' = Maybe.fromMaybe l (M.lookup l subs') in
                    case l' of
                        Q.Literal c ->
                            if c == 0
                                then (Q.UnconditionalJump label1)
                                else (Q.UnconditionalJump label0)
                        _ -> (Q.ConditionalJump (Q.Loc l') label0 label1)
                Q.Rel op l0 l1 ->
                    let l0' = Maybe.fromMaybe l0 (M.lookup l0 subs') in
                    let l1' = Maybe.fromMaybe l1 (M.lookup l1 subs') in
                    case (l0', l1') of
                        (Q.Literal v1, Q.Literal v2) ->
                            let helper opFun = if opFun v1 v2
                                then (Q.UnconditionalJump label0)
                                else (Q.UnconditionalJump label1)
                            in case op of
                                Q.Lth -> helper (<)
                                Q.Le -> helper (<=)
                                Q.Gth -> helper (>)
                                Q.Ge -> helper (>=)
                                Q.Equ -> helper (==)
                                Q.Neq -> helper (/=)
                        _ -> (Q.ConditionalJump
                                (Q.Rel op l0' l1')
                                label0
                                label1)
            be@(Q.Return Nothing) -> be
            be@(Q.Return (Just loc)) -> case M.lookup loc subs' of
                Nothing -> be
                Just loc' -> (Q.Return (Just loc'))
    in (resultEnv, Q.Block label vars (reverse quads') blockEnd')

-- canonicalForm of a quad is a form that makes all the necessary substitutions
-- to eliminate unnecessary reading the same variable and performing the same
-- operations again
canonicalForm :: M.Map Q.Location Q.Location -> Q.Quadruple -> Q.Quadruple
canonicalForm subs (Q.Quadruple r op l0 l1) =
    let l0' = Maybe.fromMaybe l0 (M.lookup l0 subs) in
    let l1' = Maybe.fromMaybe l1 (M.lookup l1 subs) in
    let (l0'', l1'') = (min l0' l1', max l0' l1') in
    case op of
        Q.Add -> Q.Quadruple r op l0'' l1''
        Q.Sub -> Q.Quadruple r op l0' l1'
        Q.Mul -> Q.Quadruple r op l0'' l1''
        Q.Div -> Q.Quadruple r op l0' l1'
        Q.Mod -> Q.Quadruple r op l0' l1'
canonicalForm subs (Q.Call res fName args) =
    let args' = map (\arg -> Maybe.fromMaybe arg (M.lookup arg subs)) args in
    Q.Call res fName args'
canonicalForm subs (Q.CallLoc res (l0, ofs) args) =
    let args' = map (\arg -> Maybe.fromMaybe arg (M.lookup arg subs)) args in
    let l0' = Maybe.fromMaybe l0 (M.lookup l0 subs) in
    Q.CallLoc res (l0', ofs) args'
canonicalForm _ (Q.GetVar r ident) = Q.GetVar r ident
canonicalForm subs (Q.AssignVar vName l0) =
    let l0' = Maybe.fromMaybe l0 (M.lookup l0 subs) in
    Q.AssignVar vName l0'
canonicalForm subs (Q.ReadPtr r l0 l1) =
    let l0' = Maybe.fromMaybe l0 (M.lookup l0 subs) in
    let l1' = Maybe.fromMaybe l1 (M.lookup l1 subs) in
    Q.ReadPtr r l0' l1'
canonicalForm subs (Q.WritePtr l0 l1 l2) =
    let l0' = Maybe.fromMaybe l0 (M.lookup l0 subs) in
    let l1' = Maybe.fromMaybe l1 (M.lookup l1 subs) in
    let l2' = Maybe.fromMaybe l2 (M.lookup l2 subs) in
    Q.WritePtr l0' l1' l2'

foldConsts :: Computation -> Maybe Integer
foldConsts (op, Q.Literal n, Q.Literal m) =
    case op of
        Q.Add -> Just (n + m)
        Q.Sub -> Just (n - m)
        Q.Mul -> Just (n * m)
        Q.Div -> Just (n `div` m)
        Q.Mod -> Just (n `rem` m)
foldConsts _ = Nothing

lcseQuads :: Env -> [Q.Quadruple] -> (Env, [Q.Quadruple]) -- reversed result
lcseQuads env quads =
    foldl
        (\((subs, qMap, vMap, ptrMap), acc) quad ->
            let quad' = canonicalForm subs quad in
            case quad' of
                Q.Quadruple r op l0 l1 -> case M.lookup (op, l0, l1) qMap of
                    Just oldRes ->
                        ((M.insert r oldRes subs, qMap, vMap, ptrMap), acc)
                    Nothing -> case foldConsts (op, l0, l1) of
                        Nothing ->
                            ((subs,
                                M.insert (op, l0, l1) r qMap,
                                vMap,
                                ptrMap),
                                quad' : acc)
                        Just n ->
                            ((M.insert r (Q.Literal n) subs,
                                M.insert (op, l0, l1) (Q.Literal n) qMap,
                                vMap,
                                ptrMap),
                                acc)
                -- calls invalidate all memory reads, because there can be
                -- memory writes in the function
                Q.Call _ _ _ -> ((subs, qMap, vMap, M.empty), quad' : acc)
                Q.CallLoc _ _ _ -> ((subs, qMap, vMap, M.empty), quad' : acc)
                Q.GetVar r vName -> case M.lookup vName vMap of
                    Just oldRes ->
                        ((M.insert r oldRes subs, qMap, vMap, ptrMap), acc)
                    Nothing ->
                        ((subs, qMap, M.insert vName r vMap, ptrMap),
                            quad' : acc)
                Q.AssignVar vName r ->
                        ((subs, qMap, M.insert vName r vMap, ptrMap),
                            quad' : acc)
                Q.ReadPtr r l0 l1 -> case M.lookup (l0, l1) ptrMap of
                    Just oldRes ->
                        ((M.insert r oldRes subs, qMap, vMap, ptrMap), acc)
                    Nothing ->
                        ((subs,
                            qMap,
                            vMap,
                            M.insert (l0, l1) r ptrMap),
                            quad' : acc)
                Q.WritePtr _ _ _ -> ((subs, qMap, vMap, M.empty), quad' : acc)
        )
        (env, [])
        quads

removeDeadBlocks :: [Q.Block] -> [Q.Block]
removeDeadBlocks [] = []
removeDeadBlocks blocks@((Q.Block funEntry _ _ _) : _) =
    let
        (graph, _, keyToVertex) =
            G.graphFromEdges $ map (\block@(Q.Block blockName _ _ blockEnd) ->
                    case blockEnd of
                        Q.UnconditionalJump label -> (block, blockName, [label])
                        Q.ConditionalJump _ label0 label1 ->
                                (block, blockName, [label0, label1])
                        Q.Return _ -> (block, blockName, []))
                blocks
    in let
        reachables = G.reachable graph (Maybe.fromJust $ keyToVertex funEntry)
    in let
        reachableSet = S.fromList reachables
    in let
        undeadBlocks = filter
            (\(Q.Block blockName _ _ _) ->
                S.member
                    (Maybe.fromJust $ keyToVertex blockName)
                    reachableSet)
            blocks
    in
        undeadBlocks
