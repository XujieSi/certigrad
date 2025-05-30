import CertiGrad.Tensor
import CertiGrad.Tfacts
import CertiGrad.Tactics
import CertiGrad.SimpAttr
import CertiGrad.Tgrads
import Init.Prelude

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Basic

import Lean
open Lean Elab Tactic Meta Simp


namespace certigrad
namespace T

open util_list


axiom grad_binary {shape : S} (k : T shape → T shape → TReal) (θ : T shape) :
  is_cdifferentiable (λ θ₀ => k θ₀ θ) θ → is_cdifferentiable (λ θ₀ => k θ θ₀) θ →
  ∇ (λ θ₀ => k θ₀ θ₀) θ = ∇ (λ θ₀ => k θ₀ θ) θ + ∇ (λ θ₀ => k θ θ₀) θ




axiom grad_tmulT {ishape oshape : S} : ∀ (f : T ishape → T oshape) (k : T oshape → TReal) (θ : T ishape),
  ∇ (λ θ₀ => k (f θ₀)) θ = tmulT (D (λ θ₀ => f θ₀) θ) (∇ k (f θ))



-- axiom grad_chain_rule : ∀ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (g : T shape₂ → TReal) (θ : T shape₁),
--   ∇ (λ (θ₀ : T shape₁) => g (f θ₀)) θ = tmulT (D f θ) (∇ g (f θ))

lemma grad_chain_rule : ∀ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (g : T shape₂ → TReal) (θ : T shape₁),
  ∇ (λ (θ₀ : T shape₁) => g (f θ₀)) θ = tmulT (D f θ) (∇ g (f θ)) := by exact grad_tmulT


-- See Lang (Page 340, Theorem 3.4)
-- f continuously differentiable
-- f and grad_2 f both uniformly integrable
axiom grad_integral : ∀ {ishape tshape : S} (f : T ishape → T tshape → TReal) (θ : T tshape),
  (∀ x, is_cdifferentiable (f x) θ) →
  is_uniformly_integrable_around (λ θ₀ x => f x θ₀) θ →
  is_uniformly_integrable_around (λ θ₀ x => ∇ (λ θ₁ => f x θ₁) θ₀) θ →
  ∇ (λ θ₀ => ∫ (λ x => f x θ₀)) θ = ∫ (λ x => ∇ (λ θ₀ => f x θ₀) θ)

lemma grad_congr {shape : S} {f g : T shape → TReal} {x : T shape} (H : ∀ x, f x = g x) : ∇ f x = ∇ g x := by
  rw [funext H]

axiom grad_const : ∀ {ishape : S} (θ : T ishape) (x : TReal), ∇ (λ (θ₀ : T ishape) => x) θ = 0
axiom grad_id : ∀ (θ : TReal), ∇ (λ θ => θ) θ = (1 : TReal)

axiom grad_id_D : ∀ (θ : TReal), D (λ θ => θ) θ = (1 : TReal)

axiom TReal_one : ∀ (θ : TReal), θ • 1 = θ

-- Unary
axiom grad_exp {shape : S} (k : T shape → TReal) (θ : T shape) :
  ∇ (λ θ => k (exp θ)) θ = ∇ k (exp θ) * exp θ



axiom grad_log {shape : S} (k : T shape → TReal) (θ : T shape) : θ > 0 →
  ∇ (λ θ => k (log θ)) θ = ∇ k (log θ) / θ


axiom grad_sqrt {shape : S} (k : T shape → TReal) (θ : T shape) : θ > 0 →
  ∇ (λ θ => k (sqrt θ)) θ = ∇ k (sqrt θ) / (2 * sqrt θ)


axiom grad_scale {shape : S} (k : T shape → TReal) (α : TReal) (x : T shape) :
  ∇ (λ x => k (α • x)) x = α • ∇ k (α • x)

axiom grad_neg {shape : S} (k : T shape → TReal)(θ : T shape) :
  ∇ (λ θ => k (- θ)) θ = - (∇ k (- θ))



-- Binary
axiom grad_add₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₁ => k (x₁ + x₂)) x₁ = ∇ k (x₁ + x₂)

axiom grad_add₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₂ => k (x₁ + x₂)) x₂ = ∇ k (x₁ + x₂)

axiom grad_sub₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₁ => k (x₁ - x₂)) x₁ = ∇ k (x₁ - x₂)

axiom grad_sub₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₂ => k (x₁ - x₂)) x₂ = - ∇ k (x₁ - x₂)

axiom grad_mul₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₁ => k (x₁ * x₂)) x₁ = ∇ k (x₁ * x₂) * x₂

axiom grad_mul₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₂ => k (x₁ * x₂)) x₂ = ∇ k (x₁ * x₂) * x₁

-- Note: can be proved from grad_binary and grad_mul*, but resulting theorem
-- would have `is_cdifferentiable k` as a pre-condition.
-- It is safe to avoid that here because of the symmetry of the function.
axiom grad_square {shape : S} (k : T shape → TReal) (x : T shape) :
  ∇ (λ x => k (square x)) x = ∇ k (square x) * 2 * x

axiom grad_div₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) : square x₂ > 0 →
  ∇ (λ x₁ => k (x₁ / x₂)) x₁ = ∇ k (x₁ / x₂) / x₂

axiom grad_div₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) : square x₂ > 0 →
  ∇ (λ x₂ => k (x₁ / x₂)) x₂ = - (∇ k (x₁ / x₂) * x₁) / (square x₂)

-- Tensors
axiom grad_sum (k : TReal → TReal) (shape : S) (x : T shape) :
  ∇ (λ x => k (sum x)) x = ∇ k (sum x) • 1

axiom grad_dot₁ {shape : S} (x₁ x₂ : T shape) : ∇ (λ x₁ => dot x₁ x₂) x₁ = x₂
axiom grad_dot₂ {shape : S} (x₁ x₂ : T shape) : ∇ (λ x₂ => dot x₁ x₂) x₂ = x₁

axiom grad_gemm₁ {m p : ℕ} (k : T [m, p] → TReal) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
∇ (λ M => k (gemm M N)) M = gemm (∇ k (gemm M N)) (transpose N)

axiom grad_gemm₂ {m p : ℕ} (k : T [m, p] → TReal) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
∇ (λ N => k (gemm M N)) N = gemm (transpose M) (∇ k (gemm M N))

-- Congruences
axiom grad_congr_pos {shape : S} (f g : T shape → TReal) (θ : T shape) :
  θ > 0 → (∀ (θ₀ : T shape), θ₀ > 0 → f θ₀ = g θ₀) → ∇ f θ = ∇ g θ

-- Compound
lemma grad_softplus {shape : S} (k : T shape → TReal) (θ : T shape) :
  ∇ (λ θ => k (softplus θ)) θ = ∇ k (softplus θ) / (1 + exp (- θ)) := by
  have H : (exp θ) / (exp θ + 1) = 1 / (1 + exp (- θ)) :=
    calc (exp θ) / (exp θ + 1)
      = ((exp θ) / (exp θ + 1)) * ((exp θ)⁻¹ / (exp θ)⁻¹) := by simp [T.div_self (inv_pos (@exp_pos _ θ))]
    _ = ((exp θ * (exp θ)⁻¹) / ((exp θ + 1) * (exp θ)⁻¹)) := by rw [T.div_mul_div]
    _ = (1 / ((exp θ + 1) * (exp θ)⁻¹)) := by simp only [T.mul_inv_cancel (@exp_pos _ θ)]
    _ = 1 / ((exp θ * (exp θ)⁻¹) + 1 * (exp θ)⁻¹) := by simp only [right_distrib]
    _ = 1 / (1 + exp (- θ)) := by { simp only [T.mul_inv_cancel (@exp_pos _ θ), one_mul]; rw [exp_inv]}

  calc ∇ (λ θ => k (softplus θ)) θ
      = ∇ (λ θ => k (log (exp θ + 1))) θ := rfl
    _ = ∇ (λ θ => k (log (θ + 1))) (exp θ) * exp θ := by rw [T.grad_exp (λ θ => k (log (θ + 1)))]
    _ = ∇ (λ θ => k (log θ)) (exp θ + 1) * exp θ := by rw [T.grad_add₁ (λ θ => k (log θ))]
    _ = ∇ k (log (exp θ + 1)) / (exp θ + 1) * exp θ := by rw [T.grad_log k (exp θ + 1) (plus_one_pos exp_pos)]
    _ = ∇ k (softplus θ) * (exp θ / (exp θ + 1)) := by { rw [← T.mul_div_mul]; rfl}
    _ = ∇ k (softplus θ) * (1 / (1 + exp (- θ))) := by rw [H]
    _ = ∇ k (softplus θ) / (1 + exp (- θ)) := by simp [T.one_div_inv, T.div_mul_inv]


lemma grad_sigmoid {shape : S} (k : T shape → TReal) (θ : T shape) :
  ∇ (λ θ => k (sigmoid θ)) θ = ∇ k (sigmoid θ) * sigmoid θ * (1 - sigmoid θ) :=
  have H_pre : 1 + exp (- θ) > 0 := by apply one_plus_pos exp_pos
  have H : exp (- θ) / (1 + exp (- θ)) = 1 - sigmoid θ :=
    calc  exp (- θ) / (1 + exp (- θ))
        = ((1 + exp (- θ)) - 1) / (1 + exp (- θ)) := by simp [sub_add_eq_sub_sub]
      _ = ((1 + exp (- θ)) / (1 + exp (- θ))) - 1 / (1 + exp (- θ)) := by rw [T.div_sub_div_same]
      _ = 1 - sigmoid θ := by { rw [T.div_self (one_plus_pos exp_pos)]; rfl}

  calc  ∇ (λ θ => k (sigmoid θ)) θ
      = ∇ (λ θ => k (1 / (1 + exp (- θ)))) θ := rfl
    _ = - ∇ (λ θ => k (1 / (1 + exp θ))) (- θ) := by rw [T.grad_neg (λ θ => k (1 / (1 + exp θ)))]
    _ = - (∇ (λ θ => k (1 / (1 + θ))) (exp (- θ)) * exp (- θ)) := by rw [T.grad_exp (λ θ => k (1 / (1 + θ)))]
    _ = - (∇ (λ θ => k (1 / θ)) (1 + exp (- θ)) * exp (- θ)) := by rw [T.grad_add₂ (λ θ => k (1 / θ))]
    _ = -(-(∇ k (1 / (1 + exp (-θ))) * 1) / square (1 + exp (-θ)) * exp (-θ)) := by rw [(T.grad_div₂ k 1 (1 + exp (- θ)) (square_pos_of_pos $ one_plus_pos exp_pos))]
    _ =    (∇ k (1 / (1 + exp (-θ))))     / square (1 + exp (-θ)) * exp (-θ)  := by rw [T.neg_div]; rw [neg_mul]; rw [neg_neg]; simp
    _ =    (∇ k (sigmoid θ))              / square (1 + exp (-θ)) * exp (-θ)  := rfl
    _ =    (∇ k (sigmoid θ)) * (1 / (1 + exp (-θ))) * (exp (-θ) / (1 + exp (- θ))) := by
      simp [square, T.div_mul_inv, T.mul_inv_pos H_pre H_pre]
      ring
      -- rw [← mul_assoc]
      -- rw [← mul_assoc]
      -- have H2 : (1 + (-θ).exp)⁻¹ * (-θ).exp = (-θ).exp * (1 + (-θ).exp)⁻¹ := by rw [mul_comm]
      -- rw [← H2]
    _ = (∇ k (sigmoid θ)) * sigmoid θ * (exp (-θ) / (1 + exp (- θ))) := rfl
    _ = ∇ k (sigmoid θ) * sigmoid θ * (1 - sigmoid θ) := by rw [H]


-- Gradients wrt arbitrary functions
lemma grad_add_fs {ishape : S} (θ : T ishape) (f₁ f₂ : T ishape → TReal) :
  is_cdifferentiable f₁ θ → is_cdifferentiable f₂ θ →
  ∇ (λ θ₀ => f₁ θ₀ + f₂ θ₀) θ = ∇ (λ θ₀ => f₁ θ₀) θ + ∇ (λ θ₀ => f₂ θ₀) θ := by
  intro H_f₁ H_f₂
  have H₁ : is_cdifferentiable (λ θ₀ => f₁ θ₀ + f₂ θ) θ := by
     apply Iff.mp (is_cdifferentiable_add_fs _ _ _) ; constructor; exact H_f₁; apply is_cdifferentiable_const
  have H₂ : is_cdifferentiable (λ θ₀ => f₁ θ + f₂ θ₀) θ := by
     apply Iff.mp (is_cdifferentiable_add_fs _ _ _) ; constructor; apply is_cdifferentiable_const; exact H_f₂
  rw [grad_binary (λ θ₁ θ₂ => f₁ θ₁ + f₂ θ₂) _ H₁ H₂]
  rw [grad_chain_rule _ (λ θ₀ => θ₀ + f₂ θ) θ, grad_chain_rule _ (λ θ₀ => f₁ θ + θ₀) θ]
  rw [tmulT_scalar, D_scalar, tmulT_scalar, D_scalar]
  rw [grad_add₁ (λ θ => θ), grad_id, one_smul]
  rw [grad_add₂ (λ θ => θ), grad_id, one_smul]

-- #check @OfNat.ofNat

-- lemma trivial_mul_one  (α : TReal) (shape : S): (const α [] * (1: TReal)) = const α [] := by
--   simp
--   apply mul_one

lemma trivial_mul_one  (α : TReal) {shape : S}: (const α shape * 1) = const α shape := by simp
-- lemma trivial_mul_one' (α : TReal) : (const α [] * 1) = const α [] := by apply trivial_mul_one

-- failure reason:
-- multiply arbitrary shapes with TReal (e.g., 1) is not propoerly defined yet
-- also(and thus), 1 is interpreted as arbitrary shape

lemma grad_scale_f {ishape : S} (θ : T ishape) (α : TReal) (f : T ishape → TReal) :
  ∇ (λ θ₀ => α • f θ₀) θ = α • ∇ (λ θ₀ => f θ₀) θ := by
  rw [grad_chain_rule f (λ θ => α • θ) θ]
  rw [grad_scale (λ θ => θ)]
  rw [grad_id]
  -- at this point, 1 is treated as TReal 1, instead Tensor One; this is problematic
  -- rw [smul.def]
  -- have H : (const α [] * 1) = const α [] := by simp; apply mul_one
  rw [TReal_one] -- we introduce a new axiom here
  rw [tmulT_scalar]
  rw [D_scalar]



lemma H_grad_log_simple :  {x : TReal} →  x > 0 → ∇ log x = x⁻¹ := by
  intro x h1
  have h2 :=  grad_log (k := (λ (y:TReal) => y))
  have h3 := h2 x
  rw [grad_id] at h3
  have h4 : ∇ (fun θ => θ.log) x = 1 / x := by apply h3; apply h1 -- two zeros are different, TReal, tensor zero
  have h5 : 1 / x = x⁻¹ := by apply T.one_div_inv
  rw [← h5]
  rw [← h4]

-- because grad expects the function maps a tensor to a real number
-- while log maps tensor to tensor, lean infers the output tensor must a real number
-- as a result, the input tensor should be a real number as well


lemma grad_log_f {shape : S} (θ : T shape) (f : T shape → TReal) : f θ > 0 → ∇ (λ θ₀ => log (f θ₀)) θ = (f θ)⁻¹ • ∇ f θ := by

  intro H_pos
  rw [grad_chain_rule, tmulT_scalar, D_scalar, H_grad_log_simple H_pos]


lemma grad_sumr {X : Type} {shape : S} (θ : T shape) (f : T shape → X → TReal) :
  Π (xs : List X),
    is_cdifferentiable (λ (θ₀ : T shape) => sumr (List.map (f θ₀) xs)) θ →
    ∇ (λ (θ₀ : T shape) =>  sumr (List.map (f θ₀) xs)) θ
    =
    sumr (List.map (λ x => ∇ (λ θ₀ => f θ₀ x) θ) xs)
  | [],      H_diff => by { unfold List.map sumr; rw [grad_const] }
  | (x::xs), H_diff => by
    unfold List.map sumr
    unfold List.map sumr at H_diff
    rw [grad_add_fs _ _ _ (Iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff).left (Iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff).right]
    rw [grad_sumr _  _ _ ((Iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff).right)]




def SimpGradRewrite (tid : MVarId) (exprs : List (MetaM Expr)) : TacticM RewriteResult := do
  match exprs with
  | [] => --pure []
    throwError "SimpGradRewrite: None is successful:("
  | e :: es =>
    try
      let target ← instantiateMVars (← tid.getType)
      let target ← whnf target
      let rr ← tid.rewrite target (← e)
      Term.synthesizeSyntheticMVarsNoPostponing
      return rr
    catch _ =>
      SimpGradRewrite tid es

def BuildSimpGradLemmas (k: Expr) : TacticM (List (MetaM Expr)) := do
    let rules : List (MetaM  Expr) := [
          (mkAppM ``certigrad.T.grad_id #[]),
          (mkAppM ``certigrad.T.grad_const #[k]),
          (mkAppM ``certigrad.T.grad_exp #[k]),
          (mkAppM ``certigrad.T.grad_log #[k]),
          (mkAppM ``certigrad.T.grad_scale #[k]),
          (mkAppM ``certigrad.T.grad_neg #[k]),
          (mkAppM ``certigrad.T.grad_add₁ #[k]),
          (mkAppM ``certigrad.T.grad_add₂ #[k]),
          (mkAppM ``certigrad.T.grad_sub₁ #[k]),
          (mkAppM ``certigrad.T.grad_sub₂ #[k]),
          (mkAppM ``certigrad.T.grad_mul₁ #[k]),
          (mkAppM ``certigrad.T.grad_mul₂ #[k]),
          (mkAppM ``certigrad.T.grad_div₁ #[k]),
          (mkAppM ``certigrad.T.grad_div₂ #[k]),
          (mkAppM ``certigrad.T.grad_dot₁ #[k]),
          (mkAppM ``certigrad.T.grad_dot₂ #[k]),
          (mkAppM ``certigrad.T.grad_square #[k]),
          (mkAppM ``certigrad.T.grad_sqrt #[k]),
          (mkAppM ``certigrad.T.grad_softplus #[k]),
          (mkAppM ``certigrad.T.grad_sigmoid #[k]),
          (mkAppM ``certigrad.T.grad_gemm₁ #[k]),
          (mkAppM ``certigrad.T.grad_gemm₂ #[k]),
          (mkAppM ``certigrad.T.grad_sum #[k]),
          (mkAppM ``certigrad.T.grad_scale_f #[k])
        ]
    return rules



partial def SimpGradCoreLoop
    (lhs: Expr)
    : TacticM (Option (List MVarId × Expr)) := do
    let fn := lhs.getAppFn
    let args := lhs.getAppArgs
    if fn.isConstOf ``certigrad.T.grad && args.size == 3 then
        let k ←  computeK lhs
        let rules ← BuildSimpGradLemmas k
        let ty ← inferType lhs
        let olhs ← mkFreshExprMVar ty
        let tgt ← mkEq olhs lhs
        let newGoal ← mkFreshExprMVar tgt
        try
          let subresult ← SimpGradRewrite newGoal.mvarId! rules
          let subgoals: List MVarId := subresult.mvarIds
          let rwproof: Expr := subresult.eqProof
          olhs.mvarId!.assign lhs
          let eqlhs_lhs ← mkEqRefl lhs
          let proof ← mkAppM ``Eq.mp #[ rwproof, eqlhs_lhs]
          return (some (subgoals, proof))
        catch _ =>
          return some ([], ← mkEqRefl lhs)
    else
      try
        match lhs with
          | Expr.app f x =>
              try
                let (fsubgoals, fproof) ← (← SimpGradCoreLoop f)
                let (xsubgoals, xproof) ← (← SimpGradCoreLoop x)
                let subgoals := fsubgoals ++ xsubgoals
                let newproof ← mkCongr fproof xproof
                return (some (subgoals, newproof))
              catch _ =>
                let proof ← mkEqRefl lhs
                return (some ([], proof))
          | _ =>
              let proof ← mkEqRefl lhs
              return (some ([], proof))
      catch ex =>
        return some ([], ← mkEqRefl lhs)

partial def SimpGradCore (tid: MVarId)  : TacticM Unit := do
  let e ← tid.getType
  -- [WARNING!!!]
  let e ← whnf e
  match e.eq? with
  | some (_, lhs, _) =>
    let (subgoals, proof) ← (←  SimpGradCoreLoop lhs)
    let target ← instantiateMVars e
    let rewriteResult ← tid.rewrite target proof
    let goal' ← tid.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
    let gens := rewriteResult.mvarIds.filter fun g => g != tid
    replaceMainGoal (goal' :: gens ++ subgoals)
    -- tid.assign (← mkEqRefl lhs)
    if rewriteResult.eNew == e then
      return ()
    else  -- let newGoals ← SimpGradCore tid
      SimpGradCore (←getMainGoal)
  | none =>
    throwError "SimpGradCore: goal is not an equality, got: {e}"


elab "simplifyGrad": tactic => do
  SimpGradCore (← getMainGoal)
  let varIds ← Meta.repeat' proveDifferentiableCore (← getGoals)

  let varIds ← myAssumption varIds

  let varIds ← Meta.repeat' provePreconditionsCore varIds

  let varIds ← myAssumption varIds

  setGoals varIds




lemma grad_mvn_kl₁ (k : TReal → TReal) (shape : S) (μ σ : T shape) : ∇ (λ μ => k (mvn_kl μ σ)) μ = ∇ k (mvn_kl μ σ) • μ := by
  unfold mvn_kl
  simplifyGrad
  simp [T.smul.def]
  rw [two_shape_eq_two, mul_comm, mul_assoc, mul_comm]
  rw [T.inv_mul_cancel two_pos]
  simp

lemma grad_mvn_kl₂ (k : TReal → TReal) (shape : S) (μ σ : T shape) (H_σ : σ > 0) (H_k : is_cdifferentiable k (mvn_kl μ σ)) :
  ∇ (λ σ => k (mvn_kl μ σ)) σ = ∇ k (mvn_kl μ σ) • (σ - (1 / σ)) := by
    have H_σ₂ : square σ > 0 := square_pos_of_pos H_σ
    have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape) => k (-2⁻¹ * T.sum (1 + T.log (square θ₀) - square μ - square σ))) σ := by proveDifferentiable
    have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape) => k (-2⁻¹ * T.sum (1 + T.log (square σ) - square μ - square θ₀))) σ := by proveDifferentiable
    unfold mvn_kl
    rw [grad_binary (λ θ₁ θ₂ => k (-2⁻¹ * T.sum (1 + T.log (square θ₁) - square μ - square θ₂))) _ H_diff₁ H_diff₂]
    simplifyGrad
    simp [T.smul.def, two_shape_eq_two, div_mul_inv]
    set A := (∇ (fun x => k x) (-(2⁻¹ * (1 + σ.square.log - μ.square - σ.square).sum))).const shape
    have H_1: A * 2⁻¹ * σ.square⁻¹ * 2 * σ = A * σ.square⁻¹ * σ * (2 * 2⁻¹) := by ring_nf
    have H_2: A * 2⁻¹ * 2 * σ = A * σ * (2 * 2⁻¹) := by ring_nf
    rw [H_1, H_2, T.mul_inv_cancel two_pos]
    simp [mul_one]
    unfold square
    rw [T.mul_inv_pos H_σ H_σ]
    have H_3: A * (σ⁻¹ * σ⁻¹) * σ = A * σ⁻¹ * (σ * σ⁻¹) := by ring_nf
    rw [H_3, T.mul_inv_cancel H_σ, mul_one]
    ring




lemma mvn_grad_logpdf_μ_correct {shape : S} (μ σ x : T shape) (H_σ : σ > 0) :
  ∇ (λ θ => mvn_logpdf θ σ x) μ = mvn_grad_logpdf_μ μ σ x := by
  unfold mvn_logpdf mvn_grad_logpdf_μ
  simplifyGrad
  unfold square
  simp [T.smul.def, div_mul_inv, T.mul_inv_pos H_σ H_σ, two_shape_eq_two, T.inv_mul_cancel two_pos]
  ring

lemma mvn_grad_logpdf_σ_correct {shape : S} (μ σ x : T shape) (H_σ : σ > 0) :
  ∇ (λ θ => mvn_logpdf μ θ x) σ = mvn_grad_logpdf_σ μ σ x := by
  let H_σ₂ := square_pos_of_pos H_σ
  have H_d₁ : is_cdifferentiable (λ θ₀ => -2⁻¹ * sum (square ((x - μ) / θ₀) + log (2 * pi shape) + log (square σ))) σ := by proveDifferentiable
  have H_d₂ : is_cdifferentiable (λ θ₀ => -2⁻¹ * sum (square ((x - μ) / σ) + log (2 * pi shape) + log (square θ₀))) σ := by proveDifferentiable
  unfold mvn_logpdf mvn_grad_logpdf_σ
  rw [grad_binary (λ θ₁ θ₂ => -2⁻¹ * sum (square ((x - μ) / θ₁) + log (2 * pi shape) + log (square θ₂))) _ H_d₁ H_d₂]
  simplifyGrad
  unfold square
  simp [T.smul.def, div_mul_inv,two_shape_eq_two, mul_inv_pos H_σ H_σ]
  have H_1: 2⁻¹ * 2 * ((x - μ) * σ⁻¹) * (x - μ) * (σ⁻¹ * σ⁻¹) + -(2⁻¹ * (σ⁻¹ * σ⁻¹) * 2 * σ) = (2 * 2⁻¹) * ((x - μ) * σ⁻¹) * (x - μ) * (σ⁻¹ * σ⁻¹) - (σ⁻¹ * (σ * σ⁻¹) * (2 * 2⁻¹)) := by ring
  simp [H_1, T.mul_inv_cancel two_pos, T.mul_inv_cancel H_σ, one_mul, mul_one]
  have H_σ_σ : σ * σ > 0 := by apply square_pos_of_pos H_σ
  simp [mul_inv_pos H_σ H_σ_σ,mul_inv_pos H_σ H_σ]
  ring





lemma grad_bernoulli_neglogpdf₁ (k : TReal → TReal) (shape : S) (p z : T shape)
  (H_p₁ : 0 < p) (H_p₂ : 0 < 1 - p) (H_k : is_cdifferentiable k (bernoulli_neglogpdf p z)) :
  ∇ (λ p => k (bernoulli_neglogpdf p z)) p = ∇ k (bernoulli_neglogpdf p z) •
    ((1 - z) / (eps shape + (1 - p)) - z / (eps shape + p)) := by
    have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape) => k (-T.sum (z * T.log (eps shape + θ₀) + (1 - z) * T.log (eps shape + (1 - p))))) p := by proveDifferentiable
    have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape) => k (-T.sum (z * T.log (eps shape + p) + (1 - z) * T.log (eps shape + (1 - θ₀))))) p := by proveDifferentiable
    unfold bernoulli_neglogpdf
    rw [T.grad_binary (λ θ₁ θ₂ => k (-T.sum (z * T.log (eps shape + θ₁) + (1 - z) * T.log (eps shape + (1 - θ₂))))) _ H_diff₁ H_diff₂]
    simplifyGrad
    simp [T.smul.def, const_neg, T.neg_div, T.div_mul_inv, left_distrib, right_distrib]
    rw [T.neg_div]
    simp [mul_neg, neg_mul]
    apply congr_arg
    apply congr_arg
    simp [T.smul.def, const_neg, T.neg_div, T.div_mul_inv, left_distrib, right_distrib]
