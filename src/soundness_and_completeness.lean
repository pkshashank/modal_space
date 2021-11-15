import top_down_proofs

-----------------------------------------------
/- Soundness -/
def sound (log : set bmod_form) (cl : set frames) := log ∈ normal_logic ∧ log ⊆ frame_logic cl

/- The logic K is sound with respect to all class of frames -/
example (cl : set frames) : sound (nl ∅) cl :=
begin
  rw sound,
  split,
    exact nls_are_normal ∅,
    rw [frame_logic, nls_are_KΓs, KΓ, set_Cs],
    simp only [forall_exists_index, forall_eq_apply_imp_iff', set.sUnion_subset_iff, set.mem_set_of_eq],
    intros n,
    induction n with k ih,
      {
        rw [C,base],
        simp only [set.empty_union, set.union_singleton,set.union_subset_iff],
        split,
          {
            have h1, from val_prop_taut,
            intros ψ h2,
            simp only [set.mem_set_of_eq],
            cases h2 with φ h2,
            specialize h1 φ cl h2.left,
            convert h1,
            rw ←h2.right,
            refl,
          },
          intros φ h0,
          simp only [set.mem_insert_iff, set.mem_singleton_iff, set.mem_set_of_eq] at h0 ⊢,
          cases h0,
          all_goals {rw h0, rw valid_class, intros F h1},
          exact val_dual F,
          exact val_K F,
      },
    rw ←frame_logic at ih ⊢,
    have h0, from @frame_logic_is_normal cl,
    rw normal_is_closed at h0,
    rw C,
    repeat {rw set.union_subset_iff, split},
    exact ih,
      {
        have h1, from mp_contain ih,
        intros φ h2,
        exact h0.right.left (h1 h2),
      },
      {
        have h1, from gen_set_contain ih,
        intros φ h2,
        exact h0.right.right.left (h1 h2),
      },
      {
        have h1, from subst_set_contain ih,
        intros φ h2,
        exact h0.right.right.right (h1 h2),
      },
end

/- Completeness -/
def complete (log : set bmod_form) (cl : set frames) := log ∈ normal_logic ∧ frame_logic cl ⊆ log

-- We postpone the completeness proofs till needed.