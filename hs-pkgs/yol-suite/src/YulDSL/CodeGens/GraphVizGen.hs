module YulDSL.CodeGens.GraphVizGen
  ( yulCatToGraphViz, yulCatToGraphVizVerbose, previewYulCat, previewYulCatVerbose
  ) where
-- base
import Data.Bool              (bool)
import Data.Function          ((&))
-- graphviz & fgl
import Data.Graph.Inductive   qualified as GI
import Data.GraphViz          qualified as GV
-- yul-dsl
import YulDSL.Core.YulBuiltIn
import YulDSL.Core.YulCat

------------------------------------------------------------------------------------------------------------------------
-- graphviz visualizer
--
-- Note:
-- - data GraphvizParams n nl el cl l
--   - node,             n  :: GI.Node
--   - node label,       nl :: ([ClasterLabel], String {- final node label -})
--   - edge label,       el :: String
--   - cluster label,    cl :: ClasterLabel :: (GI.Node, String)
--   - final node label, l  :: String
-- - clusterBy :: (n, nl) -> LNodeCluster cl l
------------------------------------------------------------------------------------------------------------------------

type Node = GI.Node
type ClasterLabel = GI.LNode String
type Cluster = GV.LNodeCluster ClasterLabel String
type NodeLabel = ([ClasterLabel], String)
type EdgeLabel = String
type Graph = ([GI.LNode NodeLabel], [GI.LEdge EdgeLabel])

data BuildingUnit
  = MkEdge EdgeLabel -- edge without a block
  | MkBlock (Node, EdgeLabel) {- in edge -} (Node, EdgeLabel) {- out edge -}

merge_els :: EdgeLabel -> EdgeLabel -> EdgeLabel
merge_els ac cb = if not (null ac) && not (null cb) then ac ++ "□" ++ cb else ac ++ cb

fuse_edges :: (Node, EdgeLabel) -> (Node, EdgeLabel) -> GI.LEdge EdgeLabel
fuse_edges (onid, oel) (inid, iel) = (onid, inid, merge_els oel iel)

data YulCatToGraphvizOptions = MkYulCatToGraphvizOptions
  { yulCatGraphvizIgnoreEdgeLabels :: Bool
  , yulCatGraphvizIgnoreCoercions  :: Bool
  }

-- | Turn a yul cat into a dot graph.
yulCatToGraphViz' :: YulCatToGraphvizOptions -> YulCat eff a b -> GV.DotGraph GI.Node
yulCatToGraphViz' opts cat_ =
  let ((nid, gr), bu) = go cat_ [] (0, ([], []))
      gr' = ( gr <>
              -- start/stop nodes
              ([(nid, ([], "◯")), (nid + 1, ([], "◉"))], []) <>
              -- connect start stop nodes
              case bu of
                MkEdge el           -> ([], [(nid, nid + 1, el)])
                MkBlock iedge oedge -> ([], [fuse_edges (nid, "") iedge, fuse_edges oedge (nid + 1, "")])
            )
            & uncurry GI.mkGraph
            & (if ignoreEls then GI.emap (const "") else id)
            :: GI.Gr NodeLabel EdgeLabel
  in GV.graphToDot (GV.blankParams { GV.isDirected = True
                                   , GV.globalAttributes = []
                                   , GV.clusterBy = clusterBy
                                   , GV.isDotCluster = const True
                                   , GV.clusterID = GV.Num . GV.Int . fst
                                   , GV.fmtCluster = fmtCluster
                                   , GV.fmtNode = fmtNode
                                   , GV.fmtEdge = fmtEdge
                                   })
     gr'
  -- in GV.graphToDot GV.nonClusteredParams gr
  where
    ignoreEls = yulCatGraphvizIgnoreEdgeLabels opts
    ignoreCoercions = yulCatGraphvizIgnoreCoercions opts
    fmtCluster (_, l) = [GV.GraphAttrs [GV.toLabel l]]
    fmtNode (_, l) = [GV.toLabel l]
    fmtEdge (_, _, el) = [GV.toLabel el]
    clusterBy :: (Node, NodeLabel) -> Cluster
    clusterBy (nid, ([], l))   = GV.N (nid, l)
    clusterBy (nid, (c:cs, l)) = GV.C c (clusterBy (nid, (cs, l)))
    addPath nid cl path = path <> [(nid, cl)]
    mk_simple_block path nid gr nl = ((nid + 1, gr <> ([(nid, (path, nl))], [])), MkBlock (nid, "") (nid, ""))
    go :: YulCat eff a b ->
          [ClasterLabel] -> -- cluster path
          (Node {- cur counter -}, Graph) ->
          ((Node {- new counter -}, Graph), BuildingUnit)
    go cat path state@(nid, gr) = case cat of
      -- type coercions
      YulReduceType -> (state, MkEdge (bool "Tr" "" ignoreCoercions))
      YulExtendType -> (state, MkEdge (bool "Te" "" ignoreCoercions))
      YulCoerceType -> (state, MkEdge (bool "Tc" "" ignoreCoercions))
      YulUnsafeCoerceEffect cat' ->
        if ignoreCoercions then go cat' path state
        else go cat' (addPath nid "ceff" path) (nid + 1, gr)

      -- categories
      YulId         -> (state, MkEdge "")

      YulComp cb_cat ac_cat ->
        let ((nid', gr'), ac_bu) = go ac_cat path (nid, gr)
            ((nid'', gr''), cb_bu) = go cb_cat path (nid', gr')
            (bu', sgr) = case (ac_bu, cb_bu) of
              -- --> ⊕ --> ; merge edge labels
              (MkEdge ac_el, MkEdge cb_el) ->
                (MkEdge (merge_els ac_el cb_el), mempty)
              -- --> ⊕ -->□--> ; merge the left edge labels
              (MkEdge ac_el, (cb_inid, cb_iel) `MkBlock` cb_oedge) ->
                ((cb_inid, merge_els ac_el cb_iel) `MkBlock` cb_oedge, mempty)
              --  -->□--> ⊕ --> ; merge the right edge labels
              (ac_iedge `MkBlock` (ac_onid, ac_oel), MkEdge cb_el) ->
                (ac_iedge `MkBlock` (ac_onid, merge_els ac_oel cb_el), mempty)
              --  -->□--> ⊕ -->□--> ; fuse the inner edges
              ((ac_inid, ac_iel) `MkBlock` ac_oedge, cb_iedge `MkBlock` (cb_onid, cb_oel)) ->
                ((ac_inid, ac_iel) `MkBlock` (cb_onid, cb_oel), ([], [fuse_edges ac_oedge cb_iedge]))
        in ((nid'', sgr <> gr''), bu')

      YulProd ab_cat cd_cat ->
        let inid = nid
            onid = nid + 1
            ((nid', gr'), ab_bu) = go ab_cat path (onid + 1, gr)
            ((nid'', gr''), cd_bu) = go cd_cat path (nid', gr')
            (bu', sgr) = case (ab_bu, cd_bu) of
              -- ab: --> × cd: -->
              (MkEdge ab_el, MkEdge cd_el) ->
                (MkEdge ("(" <> ab_el <> ")×(" <> cd_el <> ")") , mempty)
              -- ab: --> × cd: -->□-->
              (MkEdge ab_el, (cd_inid, cd_iel) `MkBlock` (cd_onid, cd_oel)) ->
                ((cd_inid, "(" <> merge_els ab_el cd_iel <> ")×(_)" ) `MkBlock` (cd_onid, cd_oel), mempty)
              -- ab: -->□--> × cd: -->
              ((ab_inid, ab_iel) `MkBlock` (ab_onid, ab_oel), MkEdge cd_el) ->
                ((ab_inid, ab_iel) `MkBlock` (ab_onid, "(_)×(" <> merge_els ab_oel cd_el <> ")"), mempty)
              -- ab: -->□--> × cd: -->□-->
              ((ab_inid, ab_iel) `MkBlock` (ab_onid, ab_oel), (cd_inid, cd_iel) `MkBlock` (cd_onid, cd_oel)) ->
                ( MkBlock (inid, "") (onid, "")
                , ( [(inid, (path, "×")), (onid, (path, "⊗"))]
                  , [ (inid, ab_inid, ab_iel)
                    , (ab_onid, onid, ab_oel)
                    , (inid, cd_inid, cd_iel)
                    , (cd_onid, onid, cd_oel)
                    ]))
        in ((nid'', sgr <> gr''), bu')

      YulSwap -> (state, MkEdge "σ")

      YulFork ab_cat ac_cat ->
        let inid = nid
            onid = nid + 1
            ((nid', gr'), ab_bu) = go ab_cat path (onid + 1, gr)
            ((nid'', gr''), ac_bu) = go ac_cat path (nid', gr')
            (bu', sgr) = case (ab_bu, ac_bu) of
              -- ab: --> ▵ ac: -->
              (MkEdge ab_el, MkEdge ac_el) ->
                (MkEdge ("(" <> ab_el <> ")▵(" <> ac_el <> ")") , mempty)
              -- ab: --> ▵ ac: -->□-->
              (MkEdge ab_el, (ac_inid, ac_iel) `MkBlock` (ac_onid, ac_oel)) ->
                ((ac_inid, "(" <> merge_els ab_el ac_iel <> ")▵(_)") `MkBlock` (ac_onid, ac_oel), mempty)
              -- ab: -->□--> ▵ ac: -->
              ((ab_inid, ab_iel) `MkBlock` (ab_onid, ab_oel), MkEdge ac_el) ->
                ((ab_inid, ab_iel) `MkBlock` (ab_onid, "(_)▵(" <> merge_els ab_oel ac_el <> ")"), mempty)
              -- [inid] (-> ab: -->□--> ▵ ac: -->□-->) [onid]
              ((ab_inid, ab_iel) `MkBlock` (ab_onid, ab_oel), (ac_inid, ac_iel) `MkBlock` (ac_onid, ac_oel)) ->
                ( MkBlock (inid, "") (onid, "")
                , ( [(inid, (path, "▵")), (onid, (path, "⊗"))]
                  , [ (inid, ab_inid, ab_iel)
                    , (ab_onid, onid, ab_oel)
                    , (inid, ac_inid, ac_iel)
                    , (ac_onid, onid, ac_oel)]))
        in ((nid'', sgr <> gr''), bu')

      YulExl -> (state, MkEdge "π₁")
      YulExr -> (state, MkEdge "π₂")

      YulDis -> (state, MkEdge "ε")

      YulDup -> (state, MkEdge "δ")

      YulApply -> error "YulApply"
      YulCurry _ -> error "YulCurry"

      YulEmb b -> mk_simple_block path nid gr ("{" ++ show b ++ "}")
      YulDyn _ -> error "YulDyn"

      YulSwitch cf_cat cs_cat cdef_cat -> mk_simple_block path nid gr "switch"
        -- let path' = addPath nid "switch" path
        --     cs_path = addPath (nid + 1) "cases" path'
        --     inid = nid + 2
        --     onid = nid + 3
        --     ((nid', cf_sgr), cf_bu) = go cf_cat path' (onid + 1, mempty)
        --     -- ((nid'', sgr2), cs_bu) = go (snd (cs_cat !! 0)) cs_path (nid', mempty)
        --     ((nid''', cdef_sgr), cdef_bu) = go cdef_cat cs_path (nid', mempty)
        --     switch_sgr = ([(inid, (path', "match")), (onid, (path', "case"))],
        --                   [ (inid, onid, "~")])
        -- in ( (nid''', cf_sgr <> cdef_sgr <> switch_sgr )
        --    , MkBlock (inid, "") (onid, "")
        --    )

      YulMapHask _ -> error "YulMapHask"

      YulJmpU (name, _) -> mk_simple_block path nid gr  ("jmp " <> name)
      YulJmpB b -> mk_simple_block path nid gr ("jmp " <> yulB_fname b)
      YulCall s -> mk_simple_block path nid gr ("call " <> show s)

      YulSGet -> mk_simple_block path nid gr "sget"
      YulSPut -> mk_simple_block path nid gr "sput"

yulCatToGraphViz :: YulCat eff a b -> GV.DotGraph GI.Node
yulCatToGraphViz = yulCatToGraphViz' MkYulCatToGraphvizOptions
                  { yulCatGraphvizIgnoreCoercions  = True
                  , yulCatGraphvizIgnoreEdgeLabels = True
                  }

yulCatToGraphVizVerbose :: YulCat eff a b -> GV.DotGraph GI.Node
yulCatToGraphVizVerbose = yulCatToGraphViz' MkYulCatToGraphvizOptions
                         { yulCatGraphvizIgnoreCoercions  = False
                         , yulCatGraphvizIgnoreEdgeLabels = False
                         }

-- | Preview a yul cat in a Xlib graphviz canvas.
previewYulCat :: YulCat eff a b ->  IO ()
previewYulCat = flip GV.runGraphvizCanvas' GV.Xlib . yulCatToGraphViz

-- | Preview a yul cat in a Xlib graphviz canvas, in verbose mode.
previewYulCatVerbose :: YulCat eff a b ->  IO ()
previewYulCatVerbose = flip GV.runGraphvizCanvas' GV.Xlib . yulCatToGraphVizVerbose
