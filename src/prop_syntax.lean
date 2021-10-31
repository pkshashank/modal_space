import tactic
attribute [instance] classical.prop_decidable
-------------------------------------------------------
--Syntax for basic propositonal language

inductive prop_form : Type
| var : ℕ → prop_form
| bot : prop_form
| neg : prop_form → prop_form
| and : prop_form → prop_form → prop_form

open prop_form

 -- Evaluating a propositional formula
@[simp]
def prop_eval (v : ℕ → bool) : prop_form → bool
| (var n) := (v n)
| bot := ff
| (neg φ) := bnot (prop_eval φ)
| (and φ ψ) := band (prop_eval φ) (prop_eval ψ)

---Defining a propositional formula to be true

def prop_true (φ : prop_form) (v : ℕ → bool) : Prop := prop_eval v φ = tt

-- Defining a propositional tautology
def prop_taut : set prop_form := { φ | ∀ v, prop_true φ v }

---------------------------------------------------------
