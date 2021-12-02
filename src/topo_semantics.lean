import syntax
import topology.basic
import tactic.basic

-----------------------------------------------

/- Topo-models -/
class topo_model {X : Type*} (T : topological_space X) := (V : ℕ → X → Prop)

/- Truth with respect to topological semantics-/
@[simp]
def top_tr {X : Type*} {T : topological_space X} (M : topo_model T) : X → bmod_form → Prop
| w (p n) := topo_model.V T n w
| _ ⊥ := false
| w (! φ) := ¬ (top_tr w φ)
| w (φ ⋀ ψ) := top_tr w φ ∧ top_tr w ψ
| w (◇ φ) := ∀ (U : set X), (is_open U → w ∈ U → (∃ (y ∈ U), top_tr y φ))


/- We could choose the notation ⊨, but I am not sure whether
that will be a problem later, because we have already used this
notation. I choose ⊩ as the notation -/
notation M ` - ` w ` ⊩ ` φ  : 50 := top_tr M w φ

/- More notation - all points where φ is true -/
notation M ` ⟦` φ `⟧ ` := {w | M - w ⊩ φ}

/- A simple example  -/
example {X : Type*} [T : topological_space X] (M : topo_model T) (φ : bmod_form) : M ⟦φ⟧ ⊆ M ⟦◇ φ⟧:=
begin
  intros w hwp,
  simp only [top_tr, exists_prop, set.mem_set_of_eq] at hwp ⊢,
  intros U hoU hwU,
  exact ⟨w,⟨hwU,hwp⟩⟩,
end

/- The set of points where ◇ φ is true, is the closure of the set 
of points where φ is true  -/
@[simp]
lemma diamond_is_closure {X : Type*} [T : topological_space X] (M : topo_model T) (φ : bmod_form) : M ⟦◇ φ⟧ =  closure (M ⟦φ⟧) :=
begin
  apply eq.symm,
  rw set.subset.antisymm_iff,
  split,
    {
      intros x h0,
      rw mem_closure_iff at h0,
      simp only [top_tr, exists_prop, set.mem_set_of_eq],
      intros U h1 h2,
      specialize h0 U,
      rw is_open at h0,
      exact h0 h1 h2,
    },
  intros φ hdp,
  rw mem_closure_iff,
  simp only [top_tr, exists_prop, set.mem_set_of_eq] at hdp,
  intros U hoU hpU,
  rw is_open at hoU,
  specialize hdp U hoU hpU,
  exact hdp,
end

/- Some lemmas which we will use later -/
@[simp]
lemma neg_is_compl {X : Type*} {T : topological_space X}  (M : topo_model T) (φ : bmod_form) : M ⟦!φ⟧ = (M ⟦φ⟧)ᶜ := rfl 

@[simp]
lemma and_is_inter {X : Type*} {T : topological_space X} (M : topo_model T) (φ ψ : bmod_form) : M ⟦(φ ⋀ ψ)⟧ = M ⟦φ⟧ ∩ M ⟦ψ⟧ := rfl

/- Similarly □ corresponds to interior -/
lemma box_is_closure {X : Type*} {T : topological_space X} (M : topo_model T) (φ : bmod_form) : interior ((M ⟦φ⟧)) = (M ⟦□ φ⟧) :=
begin
  have hc, from diamond_is_closure M (!φ),
  rw [neg_is_compl,closure_compl] at hc,
  rw [neg_is_compl, hc, compl_compl],
end

------------------------------------------------

/- Validity -/
def tvalid {X : Type*} (φ : bmod_form) (T : topological_space X) :=
∀ (V : ℕ → X → Prop) (x : X), @topo_model.mk _ T V - x ⊩ φ

def tvalid_class {X : Type*} (φ : bmod_form) (cl : set (topological_space X)):=
∀ (T ∈ cl) (V : ℕ → X → Prop) (x : X), @topo_model.mk _ T V - x ⊩ φ


/- Two points should be noted
1. In `tvalid_class`, the set of topological spaces is restricted
by the topological spaces defined on the type `X`.
2. Further, the textbook definition is for a class of frames,
and here I have taken cl to be a set. -/
 
/- The formula `(◇ (p 1) ⇔ !□! (p 1))` is valid on every class of topological
spaces.  -/ 
example {X : Type*} (cl : set (topological_space X)) : tvalid_class (◇ (p 1) ⇔ !□! (p 1)) cl :=
begin
  simp only,
  rw tvalid_class,
  intros T ht val x,
  simp only [top_tr, imp_self, not_and, not_not, and_self],
end

/- To define completeness and soundness, we need the set
of all formulas valid on a class of topological spaces-/
def top_class_valid_form {X : Type*} (cl : set (topological_space X)) := { φ | tvalid_class φ cl}

---------------------------------------------------------------

/- Propositional tautologies are valid on the any class of
topological spaces -/

noncomputable def topo_model_to_prop_val {W : Type*} (v_top : ℕ → W → Prop) (w : W) (n : ℕ) :=
ite (v_top n w) tt ff

lemma prop_truth_inv_top {X : Type*} {T : topological_space X} (φ : prop_form) (M : topo_model T) (w : X) : M - w ⊩ φ ↔ prop_true φ (topo_model_to_prop_val M.V w) :=
begin
  induction φ with n ψ hψ ψ1 ψ2 hψ1 hψ2,
  { have hcoe_n : ↑(prop_form.var n) = p n, refl,
  rw hcoe_n,
  split,
  intro hf,
  rw [prop_true, prop_eval, topo_model_to_prop_val],
  simp only [top_tr, and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] at *,
  exact hf,
  intro hv,
  rw [prop_true, prop_eval, topo_model_to_prop_val] at hv,
  simp only [and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib] at hv,
  rw top_tr,
  exact hv,},

  -- Case for bot
  {have hcoe_bot : ↑(prop_form.bot) = bmod_form.bot, refl,
  split,
  intro hf,
  rw hcoe_bot at hf,
  simp only [top_tr] at hf,
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
  rw [hcoe_neg, top_tr, hψ] at hf,
  rw [prop_true, prop_eval],
  rw prop_true at hf,
  simp only [eq_ff_eq_not_eq_tt] at hf,
  rw hf,
  rw bnot,},

  {intro hv,
  rw [hcoe_neg, top_tr, hψ],
  rw [prop_true, prop_eval] at hv,
  simp only [bnot_eq_true_eq_eq_ff] at hv,
  rw [prop_true, hv],
  contradiction,},
  
  -- Case for and 
  have hcoe_and : ↑(prop_form.and ψ1 ψ2) = (↑ψ1 ⋀ ↑ψ2), refl,
  split,

  {intro hf,
  rw [hcoe_and, top_tr] at hf,
  cases hf with hf1 hf2,
  rw hψ1 at hf1,
  rw hψ2 at hf2,
  rw [prop_true, prop_eval],
  simp only [band_eq_true_eq_eq_tt_and_eq_tt],
  rw prop_true at hf1,
  rw prop_true at hf2,
  exact ⟨hf1, hf2⟩,},

  intro hv,
  rw [hcoe_and, top_tr, hψ1, hψ2, prop_true, prop_true],
  rw [prop_true, prop_eval] at hv,
  simp only [band_eq_true_eq_eq_tt_and_eq_tt] at hv,
  assumption,
end

lemma tval_prop_taut {X : Type*} (φ : prop_form) (hptaut : φ ∈ prop_taut) (cl : set (topological_space X)) : tvalid_class φ cl :=
begin
  rw prop_taut at hptaut,
  rw tvalid_class,
  intros T hcl v w,
  set M := @topo_model.mk _ T v,
  rw prop_truth_inv_top,
  apply hptaut,
end