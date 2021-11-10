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

example {cl_F : set frames} : frame_logic cl_F ∈ normal_logic := sorry