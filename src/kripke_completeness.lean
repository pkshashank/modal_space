import syntax
set_option trace.simplify.rewrite true
----------------------------------------------------------

-- We define uniform substitution.
@[simp]
def subs (var_sub : ℕ → bmod_form) : bmod_form → bmod_form
| (p n) := var_sub n
| ⊥ := ⊥
| (! φ) := ! (subs φ)
| (φ ⋀ ψ) := (subs φ) ⋀ (subs ψ)
| (◇ φ) := ◇ (subs φ)

-- Next, we define a relation between modal formula, namely of being a substitution instance.

def subs_inst : bmod_form → bmod_form → Prop := λ ψ φ, (∃ (v : ℕ → bmod_form), ψ = subs v φ)

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
  simp,
  repeat {split},
end

--Next, we define normal modal logics as an inductive type.
--We first define the modal formulas K and Dual.
def K : bmod_form := (□ p 1 ⇒ □ p 2) ⇒ □ (p 1 ⇒ p 2)
def Dual : bmod_form:= ◇ (p 1) ⇔ ! □ ! p 1

-- We present some helper definitions.
-- The construction will be bottom up.
-- We will start with a base set and construct the normal logic by taking a closure
-- under needed functions.

-- This will be the starting set
def base (Γ : set bmod_form) := Γ ∪ prop_taut ∪ {Dual, K}

-- mp_set s is exactly the formulas that can be obtained from s by applying modus ponens to elements in s
def mp_set (s :  set bmod_form) : set bmod_form := { φ | ∃ φ1 φ2 ∈ s, (φ2 = (φ1 ⇒ φ))}

-- A similar definition for generalisation
def gen_set (s : set bmod_form) : set bmod_form := { φ | ∃ ψ ∈ s, (φ = □ ψ) }

-- And a similar one for substituion instances
def subst_set (s : set bmod_form) : set bmod_form := { φ | ∃ ψ ∈ s, subs_inst φ ψ }

-- Next, we construct the sets and in the end take the union 
def C (Γ : set bmod_form) : ℕ → set bmod_form
| 0 := base Γ 
| (n + 1) := (C n) ∪ mp_set (C n) ∪ gen_set (C n) ∪ subst_set (C n)

-- Once, we have the family, we take its union and define it to be KΓ
-- We do this in two steps, first we make a set containing the family
def set_Cs (Γ : set bmod_form) : set (set bmod_form) := { D | ∃ n, D = C Γ n }

-- Finally we take the union on this set containing the family to obtain the normal logic KΓ
def KΓ (Γ : set bmod_form) := ⋃₀ set_Cs Γ

-- All such KΓs are normal logics
def normal_logic : set (set bmod_form) := { N | ∃ Γ, N = KΓ Γ }

--Next, we have some examples, but before that we need a helper lemma to use in one of our examples.
lemma gam_sub_normal : ∀ (Γ : set bmod_form), Γ ⊆ KΓ Γ :=
begin
  intro Γ,
  have h0 : Γ ⊆ base Γ ,
    {begin
      rw base,
      refine set.subset_union_of_subset_left _ {Dual, K},
      exact set.subset_union_left Γ ↑prop_taut,
    end},
  have h1 : base Γ = C Γ 0 , refl,
  have h2 : base Γ ⊆ KΓ Γ,
    {begin
      rw KΓ,
      rw set_Cs,
      rw h1,
      refine {D : set bmod_form | ∃ (n : ℕ), D = C Γ n}.subset_sUnion_of_subset _ _ _,
      -- using mathlib heavily to simplify stuff,
      exact C Γ 0,
      refl,
      existsi 0,
      refl,
    end},
  transitivity,
  exact h0,
  exact h2,
end


-- We next prove that the set of all modal formulas formulas  forms a normal logic
example {All : set bmod_form} (ha : ∀ φ, φ ∈ All) : normal_logic All :=
begin
  rw normal_logic,
  existsi All,
  apply funext,
  intro ψ,
  apply propext,

  split,
  intro hp,
  apply gam_sub_normal,
  assumption,

  intro hkp,
  exact (ha ψ),
end

-- Next, we prove that intersection of normal logics is a normal logic
-- But before that it will be better to prove that the top down approach and the
-- bottom up approach result in the same set
-- We have a series of helper lemmas which will help in breaking down the proof.

-- This lemma says essentially that KΓ Γ is the union of C Γs.
lemma kg_iff_cn {Γ : set bmod_form} {φ : bmod_form} : φ ∈ KΓ Γ ↔ ∃ n, φ ∈ C Γ n :=
begin
  split,
  {
    intros h0,
    rw [KΓ,set_Cs] at h0,
    rw set.mem_set_of_eq at h0,
    simp at h0,
    rcases h0 with ⟨D,h1,h2⟩,
    cases h1 with m h1,
    existsi m,
    rw ←h1,
    exact h2,
  },
  
  {
    intro hn,
    cases hn with n hn,
    have h0 : C Γ n ⊆ KΓ Γ,
      {
        rw [KΓ, set_Cs],
        intros ψ h0,
        simp,
        existsi C Γ n,
        split,
          {
            existsi n,
            refl,
          },
        exact h0,
      },
    tauto,
  }
end

--This lemma says that for m > n , C Γ n ⊆ C Γ m
lemma cn_subset_cnk {Γ : set bmod_form} {n k : ℕ} : C Γ n ⊆ (C Γ (k + n)) :=
begin
  induction k with k ik,
  {
    rw zero_add,
  },
  transitivity,
  exact ik,
  have h0 : (k + 1) + n = (k + n) + 1,
  {
    rw add_assoc,
    rw add_comm 1 n,
    rw add_assoc,
  },
  rw h0,
  intros φ h1,
  rw C,
  repeat {apply or.intro_left},
  exact h1,
end

lemma mgn_imp_cn_in_cm {m n : ℕ} {Γ : set bmod_form} : m ≥ n → C Γ n ⊆ C Γ m :=
begin
  intro h0,
  have h1 : m = (m - n) + n, by omega,
  rw h1,
  apply cn_subset_cnk,
end

lemma lem1 {D : set bmod_form} : D ∈ normal_logic ↔ (({Dual, K} ∪ ↑prop_taut ⊆ D) ∧ mp_set D ⊆ D ∧ gen_set D ⊆ D ∧ subst_set D ⊆ D) :=
begin
  
  split,

  intro hd,
  rw normal_logic at hd,
  simp at hd,
  cases hd with Γ hd,
  have hc0 : C Γ 0 ⊆ KΓ Γ,
  {
    intros φ h0,
    rw kg_iff_cn,
    existsi 0,
    exact h0,
  },
  repeat {split},
  refine set.union_subset_iff.mpr _,
  split,
  {
    rw hd,
    transitivity,
    have h0 : {Dual, K} ⊆ C Γ 0,
      {
        rw [C,base],
        intros φ h0,
        apply or.intro_right,
        exact h0,
      },
    exact h0,
    exact hc0,
  },
  {
    rw hd,
    transitivity,
    have h0 : ↑prop_taut ⊆ C Γ 0, 
    {
      rw [C,base],
      intros φ h0,
      apply or.intro_left,
      apply or.intro_right,
      exact h0,
    },
    exact h0,
    exact hc0,
  },
  {
   rw hd,
   intros φ h0,
   rw kg_iff_cn,
   rw mp_set at h0,
   simp at h0,
   rcases h0 with ⟨ψ, h1⟩,
   cases h1 with h1 h2,
   rw kg_iff_cn at h1,
   rw kg_iff_cn at h2,
   cases h1 with n1 h1,
   cases h2 with n2 h2,
   have h3, from classical.em (n1 ≥ n2),
   cases h3 with h3 h4,
    {
      existsi (n1 + 1),
      rw C,
      iterate 2 {apply or.intro_left},
      apply or.intro_right,
      rw mp_set,
      simp,
      existsi ψ,
      apply and.intro h1,
      have h4 : C Γ n2 ⊆ C Γ n1, from mgn_imp_cn_in_cm h3,
      apply h4,
      exact h2,
    },
    have h3 : n2 ≥ n1, omega,
    existsi (n2 + 1),
      rw C,
      iterate 2 {apply or.intro_left},
      apply or.intro_right,
      rw mp_set,
      simp,
      existsi ψ,
      rw and.comm,
      apply and.intro h2,
      have h4 : C Γ n1 ⊆ C Γ n2, from mgn_imp_cn_in_cm h3,
      apply h4,
      exact h1,

  },
  {
    rw hd,
    intros φ h0,
    rw kg_iff_cn,
    rw gen_set at h0,
    simp at h0,
    rcases h0 with ⟨ψ, h1,h2⟩,
    rw kg_iff_cn at h1,
    cases h1 with n h3,
    existsi n + 1,
    rw C,
    apply or.intro_left,
    repeat {apply or.intro_right},
    rw gen_set,
    rw set.mem_set_of_eq,
    existsi ψ,
    existsi h3,
    exact h2,
  },
  {
    rw hd,
    intros φ h0,
    rw kg_iff_cn,
    rw subst_set at h0,
    simp at h0,
    rcases h0 with ⟨ψ, h1,h2⟩,
    rw kg_iff_cn at h1,
    cases h1 with n h3,
    existsi n + 1,
    rw C,
    repeat {apply or.intro_right},
    rw subst_set,
    rw set.mem_set_of_eq,
    existsi ψ,
    existsi h3,
    exact h2,
    -- Notice how the code is very similiar to the previous case
    -- There must be a way to make it nicer
  },
  intro h0,
  rcases h0 with ⟨h1,h2,h3,h4⟩,
  rw [normal_logic, set.mem_set_of_eq],
  existsi D,
  -- It is the smallest normal logic containing itself
  have h5 : ∀ n, C D n ⊆ D,
    {
      intro n,
      induction n with k ih,
        {
          rw [C,base],
          intros φ h5,
          cases h5 with h5 h6,
          sorry,
        },
      sorry,
    },
end
