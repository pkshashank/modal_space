import syntax
import kripke_semantics

----------------------------------------------------------

--We define uniform substitution
@[simp]
def subs (var_sub : ℕ → bmod_form) : bmod_form → bmod_form
| (p n) := var_sub n
| ⊥ := ⊥
| (! φ) := ! (subs φ)
| (φ ⋀ ψ) := (subs φ) ⋀ (subs ψ)
| (◇ φ) := ◇ (subs φ)

-- Next, we define a relation between modal formula, namely of being a substitution instance.

def subs_inst (ψ φ : bmod_form) := ∃ v, ψ = subs v φ

-- As an example, we see that ((□ p 1 ⋁ p 2) ⋀ (! p 3 ⇒ □ p 4)) ⋁ p 5 is a substitution instance of ((p 1 ⋀ p 2) ⋁ p 3).
--For that we need to show the existence of an appropriate var_sub.

example : subs_inst (((□ p 1 ⋁ p 2) ⋀ (! p 3 ⇒ □ p 4)) ⋁ p 5) ((p 1 ⋀ p 2) ⋁ p 3) :=
begin
  rw subs_inst,
  let v : ℕ → bmod_form := λ n, match n with
    | 0 := bmod_form.var 0
    | 1 := (□ p 1 ⋁ p 2)
    | 2 := (! p 3 ⇒ □ p 4)
    | 3 := p 5
    | (a + 4) := bmod_form.var (a + 4)
  end,
  
  existsi v,
  simp only [subs],
  repeat {split},
end

--Next, we define normal modal logics as an inductive type.
--We first define the modal formulas Ax_K and Ax_Dual.
def Ax_K := (□ (p 1 ⇒ p 2)) ⇒ ((□ p 1) ⇒ □ p 2)
def Ax_Dual := ◇ (p 1) ⇔ ! □ ! p 1

-- Normal Logics.
@[class]
inductive KΓ (Γ : set bmod_form) : set bmod_form
| Γ_cond (φ ∈ Γ) : KΓ φ
| K_cond : KΓ Ax_K
| Dual_cond : KΓ Ax_Dual
| taut_cond {φ : prop_form} (hptaut : φ ∈ prop_taut) : KΓ φ
| mp {φ ψ : bmod_form} (hps : KΓ (φ ⇒ ψ)) (hp : KΓ φ) : KΓ ψ
| subst {φ ψ : bmod_form} (hsub : subs_inst ψ φ) (hp : KΓ φ) : KΓ ψ
| gen {φ : bmod_form} (hp : KΓ φ) : KΓ (□ φ)

/- We have used the bottom up approach to build normal logics.
The set of all modal formulas form a normal logic -/
example (all : set bmod_form) (hall : ∀ φ, φ ∈ all) : all = KΓ all :=
begin
  rw set.subset.antisymm_iff,
  split,
    {
      intros ψ hsall,
      exact (@KΓ.Γ_cond all ψ) hsall,
    },
    intros ψ hska,
    exact hall ψ,
end

/- Next, we have a definition and a lemma which will be 
used later when we prove that validity with respect to to a class
of frames is preserved under uniform substitution  -/
def sub_model {W : Type*} (M : model W) (s : ℕ → bmod_form) : model W := ⟨λ n, {w' | M - w' ⊨ s(n)}⟩

lemma val_subst {W : Type*} (M : model W) (φ : bmod_form) (s : ℕ → bmod_form) : ∀ w, M - w ⊨ subs s φ ↔ (sub_model M s) - w ⊨ φ :=
begin
  induction φ with n φn hpn ψ1 ψ2 hs1 hs2 φd hφd,
  intro w, refl,
  intro w, refl,
  intro w, rw [tr,subs,←hpn], refl,
  intro w, rw [tr, subs, ←hs1, ←hs2], refl,
  intro w, rw [tr, subs, tr],
  split,
    {
      intros hmsub,
      rcases hmsub with ⟨u, hwu, hum⟩,
      exact ⟨u, hwu , ((hφd u).mp) hum⟩,
    },
    {
      intros hsubm,
      rcases hsubm with ⟨u, hwu, hum⟩,
      exact ⟨u, hwu , ((hφd u).mpr) hum⟩,
    },
end

/--The set of modal formulas valid on a class of frames-/
def frame_logic {W : Type*} (cl_F : set (frames W)): set bmod_form := {φ | valid_class φ cl_F}

/- Example : The set of all formulas valid on a frame
is a normal logic -/
lemma frame_logic_normal {W : Type*} (cl_F : set (frames W)) : frame_logic cl_F = KΓ (frame_logic cl_F):=
begin
  rw set.subset.antisymm_iff,
  split,
  exact KΓ.Γ_cond,
  intros φ hpkfl,
  rw [frame_logic, set.mem_set_of_eq, valid_class],
  intros F hfcl,
  induction hpkfl with ψ hsl ψ hstaut ψ1 ψ2 hs12kl hs1kl hs12l
  hs1l ψ1 ψ2 hsub hs1kl hs1 ψ hskl hsl,
    {
      rw [frame_logic, set.mem_set_of_eq, valid_class] at hsl,
      exact hsl F hfcl,
    },
    {
      rw [Ax_K, valid],
      intros val w,
      simp only [not_exists, exists_prop, tr, not_and, not_not],
      intros h12 hw1 x hrwx,
      exact h12 x hrwx (hw1 x hrwx),
    },
    {
      rw [Ax_Dual, valid],
      intros val w,
      simp only [not_exists, and_imp, exists_prop, forall_exists_index, tr, not_and, not_not, and_self, not_forall],
      tauto,
    },
    {
      have hpt, from val_prop_taut ψ cl_F hstaut,
      rw [valid_class] at hpt,
      exact hpt F hfcl,
    },
    {
      rw valid at hs12l hs1l ⊢,
      intros val w,
      specialize hs12l val w,
      specialize hs1l val w,
      set M := @model.mk _ F val with hm,
      simp only [tr, not_and, not_not] at hs12l,
      exact hs12l hs1l,
    },
    {
      rw valid at hs1 ⊢,
      intros val w,
      set M := @model.mk _ F val with hm,
      rw subs_inst at hsub,
      cases hsub with s hsub,
      specialize hs1 (sub_model M s).V w,
      rw [hsub, val_subst],
      exact hs1,
    },
    {
      rw valid at hsl ⊢,
      intros val w,
      set M := @model.mk _ F val with hm,
      simp only [not_exists, tr, not_and, not_not, ←hm],
      intros u hwu,
      exact hsl val u,
    }
end

/- Arbitrary intersection of normal logics is a normal logic -/
example (Γs : set (set bmod_form)): (KΓ (⋂ (Γ ∈ Γs), KΓ Γ)) = (⋂ (Γ ∈ Γs), KΓ Γ) :=
begin
  rw set.subset.antisymm_iff,
  split,
    { simp only [set.subset_Inter_iff],
      intros Γ hgg φ hpkg,
      induction hpkg with ψ hsl ψ hstaut ψ1 ψ2 hs12kl hs1kl hs12l
      hs1l ψ1 ψ2 hsub hs1kl hs1 ψ hskl hsl,
      {
        rw set.mem_Inter at hsl,
        specialize hsl Γ,
        simp only [set.mem_Inter] at hsl,
        exact hsl hgg,
      },
      exact KΓ.K_cond,
      exact KΓ.Dual_cond,
      exact KΓ.taut_cond hstaut,
      exact KΓ.mp hs12l hs1l,
      exact KΓ.subst hsub hs1,
      exact KΓ.gen hsl,
    },
    apply KΓ.Γ_cond,
end

/- We define axioms and the their corresponding logics. -/
def Ax_4 := (◇ ◇ p 1) ⇒ ◇ p 1
def Ax_T := p 1 ⇒ (◇ p 1)

def K := KΓ ∅
def S4:= KΓ {Ax_T,Ax_4}

/- We prove a lemma which will help us use
frame_logic_normal for that result. -/

lemma subset_lift_normal_logic (Γ1 Γ2 : set bmod_form) (hgsub : Γ1 ⊆ Γ2) : KΓ Γ1 ⊆ KΓ Γ2 :=
begin
  intros φ hpg1,
  induction hpg1 with ψ hsl ψ hstaut ψ1 ψ2 hs12kl hs1kl hs12l
  hs1l ψ1 ψ2 hsub hs1kl hs1 ψ hskl hsl,
  exact KΓ.Γ_cond ψ (hgsub hsl),
  exact KΓ.K_cond,
  exact KΓ.Dual_cond,
  exact KΓ.taut_cond hstaut,
  exact KΓ.mp hs12l hs1l,
  exact KΓ.subst hsub hs1,
  exact KΓ.gen hsl,
end