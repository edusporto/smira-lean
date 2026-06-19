import SmiraLean.AST
import SmiraLean.Semantics

namespace Smira

/--
  Types in the register allocator.
-/
inductive Ty where
  /-- Type of the bullet `blt` operand. -/
  | const : Ty
  /-- Type of a register holding a pseudo `pₙ`. -/
  | psd : Nat → Ty

/--
  Register type environment (Γ).
-/
abbrev TypeEnv := List Ty

/--
  Program (code heap) type (Ψ).
-/
abbrev TypeHeap := List TypeEnv

/--
  `Sub Γ Γ'` means environment `Γ` is a valid subtype of `Γ'`.
-/
inductive Sub : TypeEnv → TypeEnv → Prop where
  | empbk : Sub [] []
  /-- If the target block expects `psd 0` (uninitialized/dead state ⊥),
      the current block can safely provide any live pseudo `pₙ` or ⊥. -/
  | rzero : ∀ {n Γ Γ'},
      Sub Γ Γ' →
      Sub (Ty.psd n :: Γ) (Ty.psd 0 :: Γ')
  /-- If the target expects a live pseudo (succ n),
      we must provide that live pseudo. -/
  | rnotz : ∀ {n Γ Γ'},
      Sub Γ Γ' →
      Sub (Ty.psd (Nat.succ n) :: Γ) (Ty.psd (Nat.succ n) :: Γ')

-- Subtyping notation
infix:50 " ⊑ " => Sub

/--
  Type judgement of operands.

  `TyOP Γ O T` means operand `O` has type `T` in environment `Γ`.
-/
inductive TyOp : TypeEnv → Operand → Ty → Prop where
  | gab : ∀ {Γ}, TyOp Γ Operand.blt Ty.const
  | reg : ∀ {Γ rₙ pₙ},
      Proj Γ rₙ (Ty.psd pₙ) →
      NotZero pₙ →
      TyOp Γ (Operand.reg rₙ pₙ) (Ty.psd pₙ)

-- Operand typing notation
notation:50 Γ " ⊢ₚ " o " : " τ => TyOp Γ o τ

/--
  Type judgement of instructions.
-/
inductive TyInst : TypeHeap → TypeEnv → Inst → TypeEnv → Prop where
  | mov : ∀ {Ψ Γ₀ Γ₁ rₙ pₙ o τ pOld},
      (Γ₀ ⊢ₚ o : τ) →
      NotZero pₙ →
      Update Γ₀ (Ty.psd pₙ) rₙ Γ₁ pOld →
      TyInst Ψ Γ₀ (Inst.mov (Operand.reg rₙ pₙ) o) Γ₁
  | cnd : ∀ {Ψ Γ Γ' rₙ pₙ lbl Tₒ},
      (Γ ⊢ₚ (Operand.reg rₙ pₙ) : Tₒ) →
      Proj Ψ lbl.id Γ' →
      (Γ ⊑ Γ') →
      TyInst Ψ Γ (Inst.cnd (Operand.reg rₙ pₙ) lbl) Γ
      -- `cnd` doesn't change the environment if it falls through.

-- Instruction typing notation
notation:50 Ψ " ⊢ᵢ " inst " : " Γ₀ " ↦ " Γ₁ => TyInst Ψ Γ₀ inst Γ₁

/--
  Type judgement of basic blocks.
-/
inductive TyBlock : TypeHeap → TypeEnv → BasicBlock → Prop where
  | cons : ∀ {Ψ Γ Γ' i I},
      (Ψ ⊢ᵢ i : Γ ↦ Γ') →
      TyBlock Ψ Γ' I →
      TyBlock Ψ Γ (BasicBlock.cons i I)
  | jump : ∀ {Ψ Γ Γ' lbl},
      Proj Ψ lbl.id Γ' →
      (Γ ⊑ Γ') →
      TyBlock Ψ Γ (BasicBlock.jump lbl)

notation:50 Ψ " ⊢ₛ " I " : " Γ => TyBlock Ψ Γ I

/--
  Type judgement of the register bank.

  `TyRegBank R Γ` proves that the physical register `R` matches the layout
  of the type environment `Γ`.
-/
inductive TyRegBank : RegisterBank → TypeEnv → Prop where
  | nil: TyRegBank [] []
  | cons : ∀ {pₙ R' Γ'},
      TyRegBank R' Γ' →
      TyRegBank (Operand.psd pₙ :: R') (Ty.psd pₙ :: Γ')

-- Register Bank typing notation
notation:50 "⊢ᵣ " R " : " Γ => TyRegBank R Γ

/--
  Auxiliary lemma for the code heap type judgement.

  Iterates through the `Program` (C) and a local `TypeHeap` (Ψ'), ensuring
  that every block type-checks against the global `TypeHeap` (Ψ).
  (Twelf's `tpCodeHeapAux`).

  TODO: We can try to replace this with Mathlib's `List.Forall₂` later.
-/
inductive TyCodeHeapAux : TypeHeap → Program → TypeHeap → Prop where
  | nil : ∀ {Ψ}, TyCodeHeapAux Ψ [] []
  | cons : ∀ {Ψ C Γ Ψ'} {I : BasicBlock},
      (Ψ ⊢ₛ I : Γ) →
      TyCodeHeapAux Ψ C Ψ' →
      TyCodeHeapAux Ψ (I :: C) (Γ :: Ψ')

/-- Type judgement of the program (code heap). -/
inductive TyCodeHeap : TypeHeap → Program → Prop where
  | mk : ∀ {Ψ C},
      TyCodeHeapAux Ψ C Ψ →
      TyCodeHeap Ψ C

notation:50 "⊢ₕ " C " : " Ψ => TyCodeHeap Ψ C

/--
  Type judgement of the machine state.

  Takes the immutable Code Heap `C` and the mutable `State`.
-/
inductive TyState : Program → State → Prop where
  | mk : ∀ {Ψ Γ Γ'} {C : Program} {R : RegisterBank} {I : BasicBlock},
      (⊢ₕ C : Ψ) →
      (⊢ᵣ R : Γ) →
      (Ψ ⊢ₛ I : Γ') →
      (Γ ⊑ Γ') →
      TyState C (I, R)

-- Machine State typing notation
notation:50 "⊢ₘ " "⟨" C ", " s "⟩" => TyState C s

end Smira
