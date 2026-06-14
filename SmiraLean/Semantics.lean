import SmiraLean.AST

namespace Smira

/--
  Ensures a natural number is strictly greater than zero.
  (Twelf's `not_zero` relation).
-/
inductive NotZero : Nat → Prop where
  | s : ∀ {n}, NotZero (Nat.succ n)

/--
  List projection.
  `Proj L N E` means the `N`-th element of list `L` is `E`.
  (Twelf's `proj_exp` relation).
-/
inductive Proj {α : Type} : List α → Nat → α → Prop where
  | z : ∀ {x : α} {xs : List α},
      Proj (x :: xs) Nat.zero x
  | s : ∀ {x : α} {xs : List α} {n : Nat} {x' : α},
      Proj xs n x' →
      Proj (x :: xs) (Nat.succ n) x'

/--
  List update.
  (Twelf's `update_exp` relation).
-/
inductive Update {α : Type} : List α → α → Nat → List α → α → Prop where
  | z : ∀ {x : α} {xs : List α} {x' : α},
      Update (x :: xs) x' Nat.zero (x' :: xs) x
  | s : ∀ {y : α} {xs : List α} {x' : α} {n : Nat} {xs' : List α} {x : α},
      Update xs x' n xs' x →
      Update (y :: xs) x' (Nat.succ n) (y :: xs') x

inductive Eval : RegisterBank → Operand → Operand → Prop where
  /-- Evaluating a bullet just yields a bullet. -/
  | blt : ∀ {rb}, Eval rb Operand.blt Operand.blt
  /--
    Evaluating a physical register `(reg rₙ pₙ)` yields the pseudo `(psd pₙ)`,
    provided that projecting index `rₙ` out of the bank `rb` yields `(psd pₙ)`,
    and the pseudo ID `pₙ` is strictly greater than zero.
  -/
  | reg : ∀ {rb rₙ pₙ},
      Proj rb rₙ (Operand.psd pₙ) →
      -- `pₙ = 0` represents the non-initialized registers ⊥
      NotZero pₙ →
      Eval rb (Operand.reg rₙ pₙ) (Operand.psd pₙ)

/--
  Small-step operational semantics for sMIRA.
  `C` is the immutable Code Heap (environment).
-/
inductive Step (C : Program) : State → State → Prop where

  | mov : ∀ {R rₙ pₙ o I R' v oOld},
      Eval R o v →
      Update R (Operand.psd pₙ) rₙ R' oOld →
      Step C
        (BasicBlock.cons (Inst.mov (Operand.reg rₙ pₙ) o) I, R)
        (I, R')

  | jmp : ∀ {R lbl I'},
      Proj C lbl.id I' →
      Step C
        (BasicBlock.jump lbl, R)
        (I', R)

  | jeq : ∀ {R rₙ pₙ lbl I v},
      Eval R (Operand.reg rₙ pₙ) v →
      Step C
        (BasicBlock.cons (Inst.cnd (Operand.reg rₙ pₙ) lbl) I, R)
        (I, R)

  | jne : ∀ {R rₙ pₙ lbl I I' v},
      Eval R (Operand.reg rₙ pₙ) v →
      Proj C lbl.id I' →
      Step C
        (BasicBlock.cons (Inst.cnd (Operand.reg rₙ pₙ) lbl) I, R)
        (I', R)

-- Small-step notation: Environment ⊢ State₁ ⇒ State₂
notation C " ⊢ " s1 " ⇒ " s2 => Step C s1 s2

end Smira
