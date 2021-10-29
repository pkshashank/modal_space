import syntax

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
-- We first define the modal formulas K and Dual.
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
