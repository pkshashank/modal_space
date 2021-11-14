import normal_logics

----------------------------------------------------

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


/- Next, we have a definition and a lemma which will be 
used later -/
def sub_model (M : model) (s : ℕ → bmod_form) : model := ⟨M.F, λ n, {w' | M - w' ⊨ s(n)}⟩

lemma val_subst : ∀ M φ s w, (M - w ⊨ subs s φ ↔ (sub_model M s) - w ⊨ φ) :=
begin
  intros M φ s,
  induction φ with n φn hn φ1 φ2 hφ1 hφ2 φd hφd,
    { intro w,
      split,
        {
          intro h0,
          exact h0,
        },
        
          intro h0,
          simp only [tr, subs] at h0 ⊢,
          exact h0,  
    },
    { intro w,
      split,
        {
          intro h0,
          simp only [tr, subs] at h0,
          contradiction,
        },
        intro h0,
        simp only [subs,tr] at h0,
        contradiction,
    },
    { intro w,
      split,
        {
          intro h0,
          simp only [tr, subs] at h0 ⊢,
          rw ← hn,
          exact h0,
        },
        intro h0,
        simp only [tr, subs] at h0 ⊢,
        rw hn, -- Notice the only change from the previous case!
        exact h0,
    },
    { intro w,
      split,
        {
          intro h0,
          simp only [tr, subs] at h0 ⊢,
          rw [hφ1,hφ2] at h0,
          exact h0,
        },
        intro h0,
        simp only [tr, subs] at h0 ⊢,
        rw [←hφ1,←hφ2] at h0,
        exact h0,
    },
    { intro w,
      split,
        {
          intro h0,
          simp only [tr, subs] at h0 ⊢,
          rcases h0 with ⟨u,h1,h2⟩,
          existsi u,
          specialize hφd u,
          have h3 : M.F.R w u ↔ (sub_model M s).F.R w u, refl,
          rw [←h3,← hφd],
          exact ⟨h1,h2⟩,
        },
        intro h0,
          simp only [tr, subs] at h0 ⊢,
          rcases h0 with ⟨u,h1,h2⟩,
          existsi u,
          specialize hφd u,
          have h3 : M.F.R w u ↔ (sub_model M s).F.R w u, refl,
          rw [h3,hφd],
          exact ⟨h1,h2⟩,
    }
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
  intros φ h0,
  rw [subst_set,frame_logic] at h0,
  simp only [exists_prop, set.mem_set_of_eq] at h0,
  rcases h0 with ⟨ψ,h1,h2⟩,
  rw frame_logic,
  simp only [set.mem_set_of_eq],
  rw subs_inst at h2,
  cases h2 with s h2,
  rw h2,
  rw valid_class at h1 ⊢,
  intros F hF,
  specialize h1 F hF,
  rw valid at h1 ⊢,
  intros v w,
  specialize h1 (sub_model ⟨F,v⟩ s).V w,
  refine (val_subst {F := F, V := v} ψ s w).mpr h1,  
end

/- Thus, the set of formula valid on a class of frames forms a 
normal logic-/

/- Next, intersection of normal logics is a normal logic-/

lemma normal_intersection : ∀ (S : set (set bmod_form)), S ⊆ normal_logic → ⋂₀ S ∈ normal_logic :=
begin
  intros S h0,
  rw normal_is_closed,
  repeat {split},
    {
      intros φ h1,
      norm_num,
      intros s h2,
      specialize h0 h2,
      rw normal_is_closed at h0,
      apply h0.left,
      exact h1,
    },
    {
      intros φ h1,
      norm_num,
      intros s h2,
      specialize h0 h2,
      rw normal_is_closed at h0,
      apply h0.right.left,
      rw mp_set at h1,
      simp only [exists_prop, set.mem_sInter, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq] at h1,
      rw mp_set,
      simp only [exists_prop, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq],
      rcases h1 with ⟨ψ1,ψ2,h3,h4,h5⟩,
      existsi ψ1,
      existsi ψ2,
      exact ⟨h3 s h2,⟨h4 s h2,h5⟩⟩,
    },
    {
      intros φ h1,
      norm_num,
      intros s h2,
      specialize h0 h2,
      rw normal_is_closed at h0,
      apply h0.right.right.left,
      rw gen_set at h1,
      simp only [exists_prop, set.mem_sInter, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq] at h1,
      rw gen_set,
      simp only [exists_prop, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq],
      rcases h1 with ⟨ψ1,h3,h4⟩,
      existsi ψ1,
      exact ⟨h3 s h2, h4⟩,
    },
    intros φ h1,
      norm_num,
      intros s h2,
      specialize h0 h2,
      rw normal_is_closed at h0,
      apply h0.right.right.right,
      rw subst_set at h1, --  This 
      simp only [exists_prop, set.mem_sInter, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq] at h1,
      rw subst_set, -- and this are the only change from the previous case
      simp only [exists_prop, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq],
      rcases h1 with ⟨ψ1,h3,h4⟩,
      existsi ψ1,
      exact ⟨h3 s h2, h4⟩,
end

/- Thus, there's a smallest normal logic, which is also called K.
We will call it nl K for 'normal logic K', as we already have 
something named K -/

def nl (Γ : set bmod_form) := ⋂₀ {L ∈ normal_logic | Γ ⊆ L}

/- These nls are normal logic as they are intersection of normal logics -/

lemma nls_are_normal : ∀ Γ, nl Γ ∈ normal_logic :=
begin
  intro Γ,
  rw nl,
  apply normal_intersection,
  apply set.sep_subset,
end

/- This lemma brings everything together. This says that 
top down and bottom up result in the same set. -/
lemma nls_are_KΓs : ∀ Γ, nl Γ = KΓ Γ :=
begin
  intro Γ,
  rw set.subset.antisymm_iff,
  split,
    {
      rw nl,
      have h0 : KΓ Γ ∈ normal_logic,
        {
          rw normal_logic,
          simp only [exists_apply_eq_apply', set.mem_set_of_eq],
        },
      have h1 : Γ ⊆ KΓ Γ, exact gam_sub_normal Γ,
      refine set.sInter_subset_of_mem _,
      exact ⟨h0,h1⟩,
    },
  rw nl,
  simp only [and_imp, set.mem_sep_eq, set.subset_sInter_iff],
  intros t h0 h1,
  rw normal_is_closed at h0,
  rw [KΓ, set_Cs],
  simp only [forall_exists_index, forall_eq_apply_imp_iff', set.sUnion_subset_iff, set.mem_set_of_eq],
  intro n,
  induction n with k ih,
    {
      rw [C,base,set.union_subset_iff],
      have h2, exact h0.left,
      rw set.union_subset_iff at h2,
      split,
        {
          rw set.union_subset_iff,
          exact ⟨h1,h2.right⟩,
        },
      exact h2.left,
    },
  rw C,
  repeat {rw set.union_subset_iff},
  repeat {split},
    {exact ih},
    { 
      transitivity,
      apply mp_contain ih,
      exact h0.right.left,
    },
    {
      transitivity,
      apply gen_set_contain ih,
      exact h0.right.right.left,
    },
    {
      transitivity,
      apply subst_set_contain ih,
      exact h0.right.right.right,
    },
end

/- So, we can now use nl Γs and KΓ Γs interchangebly in 
our proofs courtesy nls_are_KΓs, and the fact that these
are normal is given by the definiton of normal logic,
although a simpler way would be to use nls_are_normal -/

--------------------------------------------------