/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Stochastic backpropagation.
-/
-- import .util .tensor .tvec .graph

import CertiGrad.Util
import CertiGrad.Tensor
import CertiGrad.Tvec
import CertiGrad.Graph

namespace certigrad
open List
-- open
open util_list

noncomputable
def sumCosts (m : Env) (costs : List ID) : TReal :=
  sumr (costs.map (λ cost => env.get (cost, []) m))

-- Note: we currently sum all costs in remaining nodes when we absorb at a PDF.
-- In sequential applications, it is crucial that only the costs that are topologogically downstream are summed.
-- Exercise for the reader: prove that such an optimization is sound, and update the implementation accordingly.

-- def sumDownstreamCosts (nodes : List node) (costs : List ID) (tgt : reference) (m : env) : ℝ :=
--   sum (map (λ cost, DMap.get cost [] env) (filter (λ cost, IsDownstream cost tgt nodes) costs))

noncomputable
def sumDownstreamCosts (nodes : List node) (costs : List ID) (tgt : reference) (m : Env) : TReal:=
  sumCosts m costs

noncomputable def computeGradSlow (costs : List ID) : (nodes : List Node) → (inputs : Env) → (tgt : Reference) → T tgt.2
| [], m, tgt =>
    sumr (costs.map (λ cost => if tgt = (cost, []) then 1 else 0))
| (⟨ref, parents, Operator.det op⟩ :: nodes), m, tgt =>
    computeGradSlow costs nodes m tgt
    +  sumr (
        (riota parents.length).filter (λ idx => tgt = dnth parents idx)
        |>.map (λ idx =>
          op.pb (env.getKs parents m)
                (env.get ref m)
                (computeGradSlow costs nodes m ref)
                idx
                tgt.2
        )
      )
| (⟨ref, parents, Operator.rand op⟩ :: nodes), m, tgt =>
    computeGradSlow costs nodes m tgt
    + sumr (
        (riota parents.length).filter (λ idx => tgt = dnth parents idx)
        |>.map (λ idx =>
          sumDownstreamCosts nodes costs ref m
          •  op.glogpdf (env.getKs parents m) (env.get ref m) idx tgt.2
        )
      )


-- smurd means "d + smur" (derivative plus smur)
noncomputable
def computeGradStep (costs : List ID) (callback : List Node → Π (tgt : Reference), T tgt.2) : Π (nodes : List Node) (inputs : Env) (tgt : Reference), T tgt.2
| [], m, tgt =>
    sumr (costs.map (λ cost => if tgt = (cost, []) then T.one else T.zero ))
| (⟨ref, parents, Operator.det op⟩ :: nodes), m, tgt =>
    (callback nodes tgt) +
    sumr
      (
       List.map (fun (idx : Nat) =>
            op.pb (env.getKs parents m)
                   (env.get ref m)
                   (callback nodes ref)
                   idx
                   tgt.2)
          (List.filter (fun idx => tgt = dnth parents idx) (riota parents.length))
      )

  |  (⟨ref, parents, Operator.rand op⟩ :: nodes), m, tgt =>

    (callback nodes tgt)+
    sumr (
      List.map (fun idx =>
        sumDownstreamCosts nodes costs ref m •
        op.glogpdf (env.getKs parents m) (env.get ref m) idx tgt.2
  )
  (List.filter (fun idx => tgt = dnth parents idx) (riota parents.length))
)
-- | (⟨ref, parents, Operator.rand op⟩ :: nodes), m, tgt =>
--     sumr
--         (
--           List.map (fun (idx : Nat) =>
--             sumDownstreamCosts nodes costs ref m • op.glogpdf
--               (env.get_ks parents m)
--               (env.get ref m)
--               idx
--               tgt.2
--           )
--           (List.filter (fun idx => tgt = dnth parents idx) (riota parents.length))
--         ).map (callback nodes tgt)

noncomputable def computeInitDict (costs : List ID) : (nodes : List Node) → (tgts : List Reference) → Env
| [], tgts =>
    tgts.foldr (λ tgt dict =>
      env.insert tgt
        (computeGradStep costs (λ _ _ => T.error "backprop-end") [] env.mk tgt)
        dict
    ) env.mk
| (n :: nodes), tgts =>
    computeInitDict costs nodes (n.ref :: tgts)

noncomputable def backpropCoreHelper (costs : List ID) (init_dict : Env) :
  (nodes : List Node) → (dict : Env) → (tgts : List Reference) → Env
| [], m, tgts => init_dict
| (n :: nodes), m, tgts =>
    let old_dict := backpropCoreHelper costs init_dict nodes m (n.ref :: tgts)
    tgts.foldr (λ tgt dict =>
      env.insert tgt
        (computeGradStep costs (λ nodes' tgt' => env.get tgt' old_dict) (n :: nodes) m tgt)
        dict
    ) env.mk

noncomputable def backpropCore (costs : List ID) (nodes : List Node) (dict : Env) (tgts : List Reference) : Env :=
  backpropCoreHelper costs (computeInitDict costs nodes tgts) nodes dict tgts

noncomputable
def backprop (costs : List ID) (nodes : List Node) (inputs : Env) (tgts : List Reference) : Dvec T tgts.p2 :=
  let dict := backpropCore costs nodes inputs tgts
  tvec.fromEnv tgts dict

noncomputable
def bprop (costs : List ID) (init_dict : Env) (nodes : List Node) (inputs : Env) (tgts : List Reference) : Dvec T tgts.p2 :=
  let dict := backpropCoreHelper costs init_dict nodes inputs tgts
  tvec.fromEnv tgts dict

end certigrad
