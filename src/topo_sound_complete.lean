import topo_semantics
import normal_logics

/- Defining soundness and completeness with respect to a class of topological spaces-/

def tsound {X : Type*} (Γ : set bmod_form) (cl : set (topological_space X)) :=
Γ ⊆ top_class_valid_form cl

def tcomplete {X : Type*} (Γ : set bmod_form) (cl : set (topological_space X)) :=
top_class_valid_form cl ⊆ Γ


---------------------------------------------------------
/- Some lemmas and definitions to handle substitution as in
the case of Kripke semantics. -/
def tsub_model {X : Type*} {T : topological_space X} (M : topo_model T) (s : ℕ → bmod_form) : topo_model T := ⟨λ n, {w' | M - w' ⊩ s(n)}⟩

lemma tval_subst {X : Type*} {T : topological_space X} (M : topo_model T) (φ : bmod_form) (s : ℕ → bmod_form) :
∀ w, M - w ⊩ subs s φ ↔ (tsub_model M s) - w ⊩ φ :=
begin
  induction φ with n φn hpn ψ1 ψ2 hs1 hs2 φd hφd,
  intro w, refl,
  intro w, refl,
  intro w, rw [top_tr,subs,←hpn], refl,
  intro w, rw [top_tr, subs, ←hs1, ←hs2], refl,
  intro w, rw [top_tr, subs, top_tr],
  split,
  {
    intros hmsub U hoU hwU,
    specialize hmsub U hoU hwU,
    rcases hmsub with ⟨y,hyU,hysub⟩,
    existsi y,
    existsi hyU,
    apply (hφd y).mp hysub,
  },
  intros hsubm U hoU hwU,
  specialize hsubm U hoU hwU,
  rcases hsubm with ⟨y,hyU,hsuby⟩,
  existsi y,
  existsi hyU,
  apply (hφd y).mpr hsuby,
end

/- The set of all formulas valid on a class of topological
spaces forms a normal logic -/
lemma top_class_logic_normal {X : Type*} (cl : set (topological_space X)) :
top_class_valid_form cl = KΓ (top_class_valid_form cl) :=
begin
  rw set.subset.antisymm_iff,
  split,
  apply KΓ.Γ_cond,
  intros φ hpkg,
  induction hpkg with ψ hsl ψ hstaut ψ1 ψ2 hs12kl hs1kl hs12l
  hs1l ψ1 ψ2 hsub hs1kl hs1 ψ hskl hsl,
  exact hsl,
  {
    rw [top_class_valid_form, set.mem_set_of_eq, tvalid_class, Ax_K],
    intros T htcl V x,
    set M := @topo_model.mk _ T V,
    simp only [not_exists, and_imp, top_tr, exists_prop, forall_exists_index, not_and, not_not, not_forall],
    intros U hUo hxU hU12 W hVo hxW hW12,
    existsi (W ∩ U),
    repeat {split},
    exact @is_open.and _ _ _ T hVo hUo,
    repeat {assumption},
    intros z hzWU,
    exact (hU12 z hzWU.right) (hW12 z hzWU.left),
  },
  {
    rw [top_class_valid_form, set.mem_set_of_eq, tvalid_class, Ax_Dual],
    intros T htcl V x,
    set M := @topo_model.mk _ T V,
    simp only [top_tr, imp_self, not_and, not_not, and_self],
  },
  {
    apply tval_prop_taut,
    apply hstaut,
  },
  {
    rw [top_class_valid_form, set.mem_set_of_eq, tvalid_class] at hs12l hs1l ⊢,
    intros T hcl v x,
    specialize hs1l T hcl v x,
    specialize hs12l T hcl v x,
    set M := @topo_model.mk _ T v,
    simp only [top_tr, not_and, not_not] at hs12l,
    apply hs12l hs1l,
  },
  {
    rw [top_class_valid_form, set.mem_set_of_eq, tvalid_class] at hs1 ⊢,
    intros T hcl v x,
    set M := @topo_model.mk _ T v,
    rw subs_inst at hsub,
    cases hsub with s hsub,
    rw hsub,
    specialize hs1 T hcl (tsub_model M s).V x,
    rw tval_subst,
    apply hs1,
  },
  rw [top_class_valid_form, set.mem_set_of_eq, tvalid_class] at hsl ⊢,
  intros T hcl v x,
  specialize hsl T hcl v,
  set M := @topo_model.mk _ T v,
  simp only [not_exists, top_tr, exists_prop, not_and, not_not, not_forall],
  existsi (@set.univ X),
  repeat {split},
  exact @is_open_univ X T,
  intros x hxuni,
  apply hsl x,
end

/- The next result is S4 is sound with respect to the class of all topological spaces -/
lemma S4_sound_any {X : Type*} (any : set (topological_space X)) : tsound S4 any :=
begin
  rw [tsound, S4, top_class_logic_normal],
  apply subset_lift_normal_logic,
  intros φ hpt4,
  simp only [set.mem_insert_iff, set.mem_singleton_iff] at hpt4,
  cases hpt4,
    {
      rw [hpt4, top_class_valid_form, set.mem_set_of_eq, tvalid_class, Ax_T],
      intros T hcl v x,
      set M := @topo_model.mk _ T v,
      simp only [not_exists, top_tr, exists_prop, not_and, not_not, not_forall],
      intros h1x U hUo hxU,
      exact ⟨x,⟨hxU,h1x⟩⟩,
    },
    rw [hpt4, top_class_valid_form, set.mem_set_of_eq, tvalid_class, Ax_4],
    intros T hcl v x,
    set M := @topo_model.mk _ T v,
    simp only [not_exists, top_tr, exists_prop, not_and, not_not, not_forall],
    intros hyp U hUo hxU,
    specialize hyp U hUo hxU,
    rcases hyp with ⟨y, hyU, hyp2⟩,
    specialize hyp2 U hUo hyU,
    exact hyp2,
end