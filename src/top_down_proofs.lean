import kripke_completeness

/- Next, we prove that for a 
class of frames, the formulas valid on them form a normal 
logic. -/

def frame_logic (cl_F : set frames) : set bmod_form := {φ | valid_class φ cl_F }

/-The next lemma states that Dual is valid on every frame -/
lemma val_dual : ∀ (F : frames), valid Dual F :=
begin
  intro F,
  rw valid,
  intros v w,
  let M : model := ⟨F,v⟩,
  show M - w ⊨ Dual,
  rw Dual,
  simp only [not_exists, and_imp, exists_prop, forall_exists_index, tr, not_and, not_not, and_self, not_forall],
  intros w' h0 h1,
  exact ⟨w', ⟨h0,h1⟩⟩,
end

/- The next lemma say K is valid on every frame -/
lemma val_K : ∀ (F : frames), valid K F :=
begin
  intro F,
  rw valid,
  intros v w,
  let M : model := ⟨F,v⟩,
  show M - w ⊨ K,
  rw K,
  simp only [not_exists, exists_prop, tr, not_and, not_not],
  intros h0 h1 w1 h3,
  specialize h0 w1 h3,
  exact h0 (h1 w1 h3),
end

/- We have already proved that propositional tautologies 
are valid on all frames (the theorem 'val_prop_taut') -/

/- Next we prove that validity with respect to a frame is 
preserved under modus ponens, generalization and 
substitution. -/

lemma val_mod_pon : ∀ F φ ψ, valid φ F → valid (φ ⇒ ψ) F → valid ψ F :=
begin
  simp only,
  intros F φ ψ h0 h1,
  rw valid at h0 h1 ⊢,
  intros v w,
  specialize h1 v w,
  specialize h0 v w,
  set M := model.mk F v,
  simp only [tr, not_and, not_not] at h1,
  exact h1 h0,
end 

lemma val_gen : ∀ F φ, valid φ F → valid (□ φ) F :=
begin
  intros F φ h0,
  rw valid at h0 ⊢,
  intros v w,
  specialize h0 v,
  simp only [not_exists, tr, not_and, not_not],
  intros x h1,
  specialize h0 x,
  exact h0,
end

lemma val_subst : ∀ F φ ψ, valid φ F → subs_inst ψ φ → valid ψ F :=
begin
  sorry
end

/- To prove something is normal logic, we use that any 
set of modal formulas which contains K, Dual and 
propositional tautologies, and is closed under modus 
ponens, substitution and generalisation is a normal logic 
(namely the theorem 'normal_is_closed') -/
example {cl_F : set frames} : frame_logic cl_F ∈ normal_logic :=
begin
  rw normal_is_closed,
  repeat {split},
    {
      simp only [set.union_subset_iff],
      split,
        {
          rw frame_logic,
          intros φ h0,
          simp only [set.mem_set_of_eq],
          simp only [set.mem_insert_iff, set.mem_singleton_iff] at h0,
          cases h0,
          all_goals {rw [h0, valid_class], intros φ h1},
          apply val_dual,
          apply val_K,  
        },
      rw frame_logic,
      intros φ h0,
      simp only [set.mem_set_of_eq],
      rcases h0 with ⟨ψ,h1,h2⟩,
      have h3, from val_prop_taut,
      specialize h3 ψ cl_F h1,
      convert h3,
      exact eq.symm h2,
    },
    {
      intros φ h0,
      rw [mp_set,frame_logic] at h0,
      simp only [exists_prop, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq] at h0,
      rcases h0 with ⟨φ1,φ2,h1,h2,h3⟩,
      rw valid_class at h1 h2,
      rw frame_logic,
      simp only [set.mem_set_of_eq],
      rw valid_class,
      intros F h4,
      specialize h2 F h4,
      specialize h1 F h4,
      rw h3 at h1,
      refine val_mod_pon _ _ _ h2 h1,
    },
    {
      intros φ h0,
      rw [gen_set,frame_logic] at h0,
      simp only [exists_prop, set.mem_set_of_eq] at h0,
      rcases h0 with ⟨ψ,h1,h2⟩,
      rw [frame_logic, h2, set.mem_set_of_eq],
      rw valid_class at h1 ⊢,
      intros F h3,
      specialize h1 F h3,
      refine val_gen F ψ h1,
    },


  
end