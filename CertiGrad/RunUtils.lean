/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Utilities for optimizing over stochastic computation graphs.
-/
import Init.System.IO
import CertiGrad.Tensor
import CertiGrad.Tvec
import CertiGrad.Optim
import CertiGrad.ComputeGrad
import CertiGrad.Graph

namespace certigrad

open IO

namespace T

@[extern "lean_read_mnist"]
opaque readMnist (dir : System.FilePath) : IO (T [60000, 784] × T [60000])

@[extern "lean_read_from_file"]
opaque readFromFile (shape : S) (path : System.FilePath) : IO (T shape)

@[extern "lean_write_to_file"]
opaque writeToFile {shape : S} (x : T shape) (path : System.FilePath) : IO Unit

@[extern "lean_set_num_threads"]
opaque setNumThreads (n : Nat) : IO Unit

end T

namespace tvec

def writeAllCore (pfix sfix : String) : (names : List ID) → (shapes : List S) → Dvec T shapes → IO Unit
| (name::names), (shape::shapes), (Dvec.dcons x xs) => do
  T.writeToFile x (pfix ++ toString name ++ sfix)
  writeAllCore pfix sfix names shapes xs
| _, _, _ => pure ()

def writeAll (dir pfix sfix : String) (refs : List Reference) (xs : Dvec T refs.p2) : IO Unit := do
  IO.FS.createDirAll dir
  writeAllCore (dir ++ "/" ++ pfix) sfix refs.p1 refs.p2 xs

end tvec

noncomputable def xavierInit : (shape : S) → StateT RNG Id (T shape)
| [] => pure 0
| shape =>
  let V_in := (shape.drop 1).foldl (· * ·) 1
  let V_out := shape.head!
  let scale := T.sqrt ((6: TReal) / (T.of_nat (V_in + V_out)))
  let low := -scale
  let high := scale
  T.sample_uniform shape low high

noncomputable def sampleInitialWeights : (refs : List Reference) → StateT RNG Id (Dvec T refs.p2)
| [] => pure Dvec.dnil
| (ref::refs) => do
  let ws ← sampleInitialWeights refs
  let w ← xavierInit ref.2
  pure (Dvec.dcons w ws)

namespace run
open optim

def getBatchStart (batchSize batchNum : Nat) : Nat := batchSize * batchNum

noncomputable def mkInitialEnv {n_in n_x : Nat} (x_all : T [n_in, n_x]) (batchSize batchNum : Nat) (targets : List Reference) (θ : Dvec T targets.p2) : Env :=
  env.insert (ID.str Label.x, [n_in, batchSize]) (T.get_col_range batchSize x_all (getBatchStart batchSize batchNum)) (tvec.toEnv targets θ)

noncomputable def computeCosts (g : Graph) (inputs : Env) : StateT RNG Id TReal := do
  let dist : sprog [[]] := graph.toDist (λ env₀ => Dvec.dcons (sumCosts env₀ g.costs) Dvec.dnil) inputs g.nodes
  let result ← dist.to_rngprog
  pure (Dvec.head result)

noncomputable def computeCostEpochCore (g : Graph) {n_in n_x : Nat} (x_all : T [n_in, n_x]) (batchSize : Nat) (θ : Dvec T g.targets.p2)
  : (batchesLeft : Nat) → (costsSoFar : TReal) → StateT RNG Id TReal
| 0, cs => pure cs
| (bl + 1), cs => do
  let inputs := mkInitialEnv x_all batchSize bl g.targets θ
  let c ← computeCosts g inputs
  computeCostEpochCore g x_all batchSize θ bl (cs + c)

noncomputable def computeCostEpoch (g : Graph) {n_in n_x : Nat} (x_all : T [n_in, n_x]) (batchSize : Nat) (θ : Dvec T g.targets.p2) (numBatches : Nat) : StateT RNG Id TReal := do
  let totalEcost ← computeCostEpochCore g x_all batchSize θ numBatches 0
  pure $ totalEcost / (T.of_nat (batchSize * numBatches))

noncomputable def optimizeStep (g : Graph) (inputs : Env) (astate : adam.State g.targets.p2) (θ : Dvec T g.targets.p2) (initDict : Env) (batchSize : Nat)
  : StateT RNG Id (Dvec T g.targets.p2 × adam.State g.targets.p2) := do
  let grads ← (graph.toDist (λ env => bprop g.costs initDict g.nodes env g.targets) inputs g.nodes).to_rngprog
  pure $ adam.step θ ((1 / T.of_nat batchSize) • grads) astate

noncomputable def optimizeEpochCore (g : Graph) {n_in n_x : Nat} (x_all : T [n_in, n_x]) (batchSize : Nat)
  : (batchesLeft : Nat) → (astate : adam.State g.targets.p2) → (θ : Dvec T g.targets.p2) → (initDict : Env) → StateT RNG Id (Dvec T g.targets.p2 × adam.State g.targets.p2)
| 0, astate, θ, _ => pure (θ, astate)
| (bl + 1), astate, θ, initDict => do
  let inputs := mkInitialEnv x_all batchSize bl g.targets θ
  let (θ_new, astate_new) ← optimizeStep g inputs astate θ initDict batchSize
  optimizeEpochCore g x_all batchSize bl astate_new θ_new initDict

noncomputable def optimizeEpoch (g : Graph) {n_in n_x : Nat} (x_all : T [n_in, n_x]) (batchSize : Nat) (astate : adam.State g.targets.p2) (θ : Dvec T g.targets.p2) (initDict : Env)
: StateT RNG Id (Dvec T g.targets.p2 × TReal × adam.State g.targets.p2) :=
  let numBatches : Nat := n_x / batchSize
  do
    let (θ_new, astate_new) ← optimizeEpochCore g x_all batchSize numBatches astate θ initDict
    let epochCost ← computeCostEpoch g x_all batchSize θ_new numBatches
    pure (θ_new, epochCost, astate_new)

noncomputable def runEpoch (g : Graph) {n_in n_x : Nat} (x_all : T [n_in, n_x]) (batchSize : Nat) (astate : adam.State g.targets.p2) (θ : Dvec T g.targets.p2) (rng : RNG) (initDict : Env)
  : IO (Dvec T g.targets.p2 × TReal × adam.State g.targets.p2 × RNG) := do
  let ((θ_new, epochCosts, astate_new), rng_new) := (optimizeEpoch g x_all batchSize astate θ initDict).run rng
  pure (θ_new, epochCosts, astate_new, rng_new)

noncomputable def runItersCore (dir : System.FilePath) (g : Graph) {n_in n_x : Nat} (x_all : T [n_in, n_x]) (batchSize : Nat) (initDict : Env)
  : (numIters : Nat) → (θ : Dvec T g.targets.p2) → (astate : adam.State g.targets.p2) → (rng : RNG) → IO (Dvec T g.targets.p2 × adam.State g.targets.p2 × RNG)
| 0, θ, astate, rng => pure (θ, astate, rng)
| (t+1), θ, astate, rng => do
  let tStart ← IO.monoMsNow
  let (θ', epoch_cost, astate', rng') ← runEpoch g x_all batchSize astate θ rng initDict
  let tEnd ← IO.monoMsNow
  IO.println s!"{epoch_cost}, {(tEnd - tStart).toFloat / 1000.0}"
  runItersCore dir g x_all batchSize initDict t θ' astate' rng'

noncomputable def runIters (dir : System.FilePath) (g : Graph) {n_x n_in : Nat} (x_all : T [n_in, n_x]) (batchSize : Nat)
  (numIters : Nat) (θ : Dvec T g.targets.p2) (astate : adam.State g.targets.p2) (rng : RNG)
  : IO (Dvec T g.targets.p2 × adam.State g.targets.p2 × RNG) := do
  let initDict := computeInitDict g.costs g.nodes g.targets
  let (epochCost, rng') := (computeCostEpoch g x_all batchSize θ (n_x / batchSize)).run rng
  IO.println s!"{epochCost}, 0"
  runItersCore dir g x_all batchSize initDict numIters θ astate rng'

end run
end certigrad
