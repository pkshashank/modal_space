import data.nat.basic
import syntax
import tactic.basic
set_option pp.notation true


---------------------------------------------------------
-- Kripke semantics
universe u

@[class]
structure frames (W : Type u) := (R : W → W → Prop)

-- Some examples of frames. Natural numbers with the usual ordering.
instance nat_frame_lt : frames ℕ := ⟨nat.lt⟩

-- Also a singleton set, which here can be denoted by a unit type forms a frame with the universal relation and with the empty relation
instance sing_uni : frames unit := @frames.mk unit (λ a b, true)

-- Next, we define models, which are frames + valuations
@[class]
structure model (W : Type u) extends frames W := (V : ℕ → set W)

open model

-- Definition of truth 

@[simp]
def tr {W : Type u} (M :model W) : W → bmod_form → Prop
| w (p n) := V n w
| _ ⊥ := false
| w (! φ) := ¬ (tr w φ)
| w (φ ⋀ ψ) := tr w φ ∧ tr w ψ
| w (◇ φ) := ∃ (u : W), (frames.R w u ∧ tr u φ)


-- The usual notation for truth
notation M ` - ` w ` ⊨ ` φ  : 50 := tr M w φ

----------------------------------------------

section abbreviations

variables {W : Type u} (φ ψ : bmod_form) (M : model W) (w : W)
include φ ψ M w

-- We can check what the abbreviations look like
example : M - w ⊨ (φ ⋁ ψ) = (M - w ⊨ φ ∨ M - w ⊨ ψ) :=
begin
  simp only [tr, not_and, not_not, eq_iff_iff], -- Lean's simplifier does most of the job here.
  tauto, -- We are proving a propositional tautology
end

-- It is important to see how truth of boxed formulas is interpreted
example : (M - w ⊨ □ φ) = ∀ (u : W), (frames.R w u → M - u ⊨ φ) := by simp only [not_exists, tr, not_and, not_not]


-- Similarly for other abbreviations we have the following.

example : (M - w ⊨ (φ ⇒ ψ)) = (M - w ⊨ φ → M - w ⊨ ψ) := by simp only [tr, not_and, not_not]
example : (M - w ⊨ ⊤) := 
begin
  iterate 2 {rw tr},
  trivial,
end

end abbreviations

---------------------------------------------------------

-- Next, we define validity with respect to a frame
def valid {W : Type u} (φ : bmod_form) (F : frames W) := ∀ v (w : W), ⟨v⟩-w ⊨ φ

-- Class of frames
def valid_class {W : Type u} (φ : bmod_form) (clF : set (frames W)) := ∀ F ∈ clF, valid φ F

-- Next, we have an example, which says that the formula p → ◇ p is valid on the class of all reflexive frames.

-- We first try to create the object `the class of all reflexive frames`, which we call as rel_cl
def rel_cl (W : Type u) : set (frames W) := { f | reflexive f.R }

example {W : Type u} : valid_class (p 1 ⇒ ◇ p 1) (rel_cl W) :=
begin
  rw valid_class,
  unfold rel_cl,
  intros F hr,

  rw valid,
  intros val w,
  let M := @model.mk _ F val,
  show M - w ⊨ (p 1 ⇒ ◇ p 1),
  simp only [not_exists, exists_prop, tr, not_and, not_not, not_forall],

  intro hw,
  existsi w,
  split,
  exact hr w,
  assumption,
end

-- As a short example, we prove that propositional tautologies are valid on all classes of frames.
-- Before that we prove a helper lemma.
-- We do it in steps.
-- The first thing we do is to obtain a propositional valuation from a model valuation.
noncomputable def frame_to_prop_val {W : Type u} (v_frame : ℕ → W → Prop) (w : W) (n : ℕ) :=
ite (v_frame n w) tt ff


-- Next, we prove the helper lemma.
-- The lemma says the following.
-- Given a propositional formula φ, model M and a state w ∈ M, φ is true at w in M,
-- iff φ is true under the above obtained vaulation.
lemma prop_truth_inv {W : Type u} (φ : prop_form) (M : model W) (w : W) : M - w ⊨ φ ↔ prop_true φ (frame_to_prop_val V w) :=
begin
  --Induction on all propositional formulas
  induction φ with n ψ hψ ψ1 ψ2 hψ1 hψ2,
  
  -- Case for the propositional variables
  { have hcoe_n : ↑(prop_form.var n) = p n, refl,
  rw hcoe_n,
  split,
  intro hf,
  rw [prop_true, prop_eval, frame_to_prop_val],
  simp only [and_true, tr, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] at *,
  exact hf,
  intro hv,
  rw [prop_true, prop_eval, frame_to_prop_val] at hv,
  simp only [and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] at hv,
  rw tr,
  exact hv,},

  -- Case for bot
  {have hcoe_bot : ↑(prop_form.bot) = bmod_form.bot, refl,
  split,
  intro hf,
  rw hcoe_bot at hf,
  simp only [tr] at hf,
  contradiction,
  intro hv,
  rw [prop_true, prop_eval] at hv,
  rw hcoe_bot,
  simp only at hv,
  contradiction,},

  -- Case for neg
  have hcoe_neg : ↑(prop_form.neg ψ) = ! ψ, refl,
  split,

  {intro hf,
  rw [hcoe_neg, tr, hψ] at hf,
  rw [prop_true, prop_eval],
  rw prop_true at hf,
  simp only [eq_ff_eq_not_eq_tt] at hf,
  rw hf,
  rw bnot,},

  {intro hv,
  rw [hcoe_neg, tr, hψ],
  rw [prop_true, prop_eval] at hv,
  simp only [bnot_eq_true_eq_eq_ff] at hv,
  rw [prop_true, hv],
  contradiction,},
  
  -- Case for and 
  have hcoe_and : ↑(prop_form.and ψ1 ψ2) = (↑ψ1 ⋀ ↑ψ2), refl,
  split,

  {intro hf,
  rw [hcoe_and, tr] at hf,
  cases hf with hf1 hf2,
  rw hψ1 at hf1,
  rw hψ2 at hf2,
  rw [prop_true, prop_eval],
  simp only [band_eq_true_eq_eq_tt_and_eq_tt],
  rw prop_true at hf1,
  rw prop_true at hf2,
  exact ⟨hf1, hf2⟩,},

  intro hv,
  rw [hcoe_and, tr, hψ1, hψ2, prop_true, prop_true],
  rw [prop_true, prop_eval] at hv,
  simp only [band_eq_true_eq_eq_tt_and_eq_tt] at hv,
  assumption,
  
end

-- Using the above lemma, we prove that propositonal tautologies are valid on all frames
theorem val_prop_taut {W : Type u} (φ : prop_form) (cl : set (frames W)) (hptaut : prop_taut φ) : valid_class φ cl :=
begin
  rw prop_taut at hptaut,
  rw valid_class,
  intros F hcl,
  rw valid,

  intros v w,
  let M := @model.mk _ F v,
  show M - w ⊨ ↑φ,

  -- Using the helper lemma,
  rw prop_truth_inv,
  exact hptaut (frame_to_prop_val M.V w),
end
---------------------------------------------------------------