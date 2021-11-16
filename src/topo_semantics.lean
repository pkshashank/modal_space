import syntax
import topology.basic
import tactic.basic

universe u
-----------------------------------------------

/- Topo-models -/
structure topo_model {X : Type u} := (T : topological_space X)(V : ℕ → X → Prop)

/- Truth with respect to topological semantics-/
@[simp]
def top_tr {X : Type u} (M : topo_model) : X → bmod_form → Prop
| w (p n) := M.V n w
| _ ⊥ := false
| w (! φ) := ¬ (top_tr w φ)
| w (φ ⋀ ψ) := top_tr w φ ∧ top_tr w ψ
| w (◇ φ) := ∀ (U : set X), (M.T.is_open U → w ∈ U → (∃ (y ∈ U), top_tr y φ))


/- We could choose the notation ⊨, but I am not sure whether
that will be a problem later, because we have already used this
notation. I choose ⊩ as the notation -/
notation M ` - ` w ` ⊩ ` φ  : 50 := top_tr M w φ

/- More notation - all points where φ is true -/
notation M ` ⟦` φ `⟧ ` := {w | M - w ⊩ φ}

/- A simple example  -/
lemma lem1 {X : Type u} (M : @topo_model X) (φ : bmod_form) : M ⟦φ⟧ ⊆  M ⟦◇ φ⟧:=
begin
  intros w hwp,
  simp only [top_tr, exists_prop, set.mem_set_of_eq] at hwp ⊢,
  intros U hoU hwU,
  exact ⟨w,⟨hwU,hwp⟩⟩,
end

/- The set of points where ◇ φ is true, is the closure of the set 
of points where φ is true  -/
lemma diamond_is_closure {X : Type u} (M : @topo_model X) (φ : bmod_form) : @closure _ M.T (M ⟦φ⟧)= M ⟦◇ φ⟧ :=
begin
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
lemma neg_is_compl {X : Type u} (M : @topo_model X) (φ : bmod_form) : M ⟦!φ⟧ = (M ⟦φ⟧)ᶜ := rfl 

lemma and_is_inter {X : Type u} (M : @topo_model X) (φ ψ : bmod_form) : M ⟦(φ ⋀ ψ)⟧ = M ⟦φ⟧ ∩ M ⟦ψ⟧ := rfl

/- Similarly □ corresponds to interior -/
lemma box_is_closure {X : Type u} (M : @topo_model X) (φ : bmod_form) : @interior _ M.T ((M ⟦φ⟧)) = (M ⟦□ φ⟧) :=
begin
  have hc, from diamond_is_closure M (!φ),
  rw [neg_is_compl,closure_compl] at hc,
  rw [neg_is_compl, ← hc, compl_compl],
end

------------------------------------------------
/- Validity -/

def tvalid {X : Type u} (φ : bmod_form) (T : topological_space X) :=
∀ (V : ℕ → X → Prop) (x : X), ⟨T,V⟩ - x ⊩ φ

def tvalid_class {X : Type u} (φ : bmod_form) (cl : set (topological_space X)) :=
∀ (T ∈ cl) (V : ℕ → X → Prop) (x : X), ⟨T,V⟩ - x ⊩ φ


/- Two points should be noted
1. In `tvalid_class`, the set of topological spaces is restricted
by the topological spaces defined on the type `X`.
2. Further, the textbook definition is for a class of frames,
and here I have taken cl to be a set. -/
 
/- The formula `(◇ (p 1) ⇔ !□! (p 1))` is valid on every class of topological
spaces.  -/ 
example {X : Type u} (cl : set (topological_space X)) : tvalid_class (◇ (p 1) ⇔ !□! (p 1)) cl :=
begin
  simp only,
  rw tvalid_class,
  intros T ht val x,
  simp only [top_tr, imp_self, not_and, not_not, and_self],
end

/- To define completeness and soundness, we need the set
of all formulas valid on a class of topological spaces-/
def top_class_valid_form {X : Type u} (cl : set (topological_space X)) := { φ | tvalid_class φ cl}

----------------------------------------------------------------
