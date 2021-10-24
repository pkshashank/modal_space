
-- Syntax of the basic modal language
inductive bmod_form : Type
| var (n : ℕ) : bmod_form
| bot : bmod_form
| neg : bmod_form → bmod_form
| and : bmod_form → bmod_form → bmod_form
| dia : bmod_form → bmod_form

open bmod_form

--Notations
notation `⊥` := bot
notation `!` := neg
notation `p` := var
infix `∧` := and
notation `◇` := dia

-- Common Abbreviations
notation φ `∨` ψ := ¬ (¬ φ ∧ ¬ ψ)
notation φ `→` ψ := (¬ φ) ∨ ψ
notation φ `↔` ψ := (φ → ψ) ∧ (ψ → φ)
notation `⊤` := ¬ ⊥
notation `□` φ := ¬ (◇ (¬ φ))

#check ◇ (! ⊥)
#check !(⊥ ∧ (◇ (p 1) ∧ p 2))