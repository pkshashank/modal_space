import kripke_semantics.normal_logics

-----------------------------------------------------
/-Soundness-/

def sound {W : Type*} (Γ : set bmod_form) (cl : set (frames W)) := 
Γ ⊆ frame_logic cl

/- Note: Although in the literature the notion of soundess is only 
defined for normal logics, but I can't see how to do it here.
So here, soundness is a concept defined for all set of formulas. 
Likewise for completeness. -/

/- We prove K is sound with respect to any class of frames, and 
hence with respect to all class of frames. -/

example {W : Type*} (cl : set (frames W)) : sound K cl :=
begin
  rw [sound, K, frame_logic_normal],
  apply subset_lift_normal_logic,
  simp only [set.empty_subset],
end

/- Next result says that S4 is sound on the class of all reflexive
transitive frames -/

def refl_trans_cl (W : Type*) : set (frames W) :=
{F | transitive F.R ∧ reflexive F.R}

example {W : Type*} : sound S4 (refl_trans_cl W) :=
begin
  rw [sound, S4, frame_logic_normal],
  apply subset_lift_normal_logic,
  -- Reduces to proving that the extra axioms are valid
  -- as validity preservation under operations and other axioms
  -- have already been taken care of.
  intros φ hpt4,
  simp only [set.mem_insert_iff, set.mem_singleton_iff] at hpt4,
  cases hpt4,
    {
      rw [hpt4, frame_logic, set.mem_set_of_eq, Ax_T, valid_class],
      intros F hfcl,
      rw valid,
      intros val w,
      set M := @model.mk _ F val with hm,
      simp only [not_exists, exists_prop, tr, not_and, not_not, not_forall, ←hm],
      intros hp1w,
      rw [refl_trans_cl, set.mem_set_of_eq, reflexive] at hfcl,
      exact ⟨w, hfcl.right w, hp1w⟩,
    },
    rw [hpt4, frame_logic, set.mem_set_of_eq, Ax_4, valid_class],
    intros F hfcl,
    rw valid,
    intros val w,
    simp only [and_imp, forall_exists_index, tr, not_and, not_not],
    intros u hrwu v hruv hvp1,
    rw [refl_trans_cl, set.mem_set_of_eq, transitive] at hfcl,
    exact ⟨v, hfcl.left hrwu hruv, hvp1⟩,
end

-------------------------------------------------------------
/- Completeness -/
def complete {W : Type*} (Γ : set bmod_form) (cl : set (frames W)) := 
frame_logic cl ⊆ Γ

-- We postpone completeness proofs till needed.