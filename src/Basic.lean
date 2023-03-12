import data.fintype.basic
import logic.relation
import computability.language

inductive Symbol (NT : Type) (T : Type) : Type
| Terminal : T → Symbol
| NonTerminal : NT → Symbol  

structure CFG (NT : Type) (T : Type) :=
(rules : set (NT × list (Symbol NT T)))
(start : NT)

variables {NT T : Type}

def CFG_Derives_1_Step (g : CFG NT T) (w1 w2 : list (Symbol NT T)) : Prop :=
  ∃ r : NT × list (Symbol NT T),
    (
      r ∈ g.rules ∧ ∃ a c : list (Symbol NT T),
      (
          w1 = a ++ [ Symbol.NonTerminal r.fst] ++ c
        ∧ w2 = a ++ r.snd ++ c
      )
    )

def CFG_Derives (g : CFG NT T) : list (Symbol NT T) →  list (Symbol NT T) → Prop :=
  relation.refl_trans_gen (CFG_Derives_1_Step g)

def liftTermToSymbol (NT : Type) (a : T) : Symbol NT T :=
  Symbol.Terminal a

def liftWordToSf (w : list T) (NT : Type) : list (Symbol NT T) :=
  list.map (liftTermToSymbol NT) w

def CFG_Generates (g : CFG NT T) (w : list T) : Prop :=
  CFG_Derives (g) ([ Symbol.NonTerminal g.start ]) (liftWordToSf w NT)

def RuleNonTerms (r : NT × list (Symbol NT T)) : NT → Prop :=
  λ A : NT,
  r.fst = A ∨ (Symbol.NonTerminal A) ∈ r.snd

def CFG_NonTerms (g : CFG NT T) : NT → Prop :=
  λ A : NT,
  A = g.start ∨ ∃ r : NT × list (Symbol NT T), r ∈ g.rules ∧ RuleNonTerms r A