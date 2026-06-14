
namespace Smira

inductive Operand where
  /-- Pseudo-register (variable). -/
  | psd : Nat → Operand
  /-- Bullet, which has no effect in the allocation process. -/
  | blt : Operand
  /--
    Pre-colored register.

    Represents a pair `(r, p)`, where `r` is a position in the register bank,
    and `p` is the pseudo stored in that position.
  -/
  | reg : Nat → Nat → Operand

/--
  Label of a basic block. A program is a list of basic blocks, each addressed
  by a single label.
-/
structure Label where
  id : Nat

/--
  Program instruction.
-/
inductive Inst where
  | mov : Operand → Operand → Inst
  | cnd : Operand → Label → Inst
  -- Note that `jmp`s are encoded in the basic block.
  -- | jmp : Label → Inst
  -- The original Twelf code is missing calls:
  -- | call : Operand → List Operand → Inst

/-- A basic block of instructions. -/
inductive BasicBlock where
  | cons : Inst → BasicBlock → BasicBlock
  | jump : Label → BasicBlock

/--
  The Code Heap (C), or the program.

  It is basically a lookup table where index `i` represents the label `i`. -/
abbrev Program := List BasicBlock

/-- Register bank R. -/
abbrev RegisterBank := List Operand

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
  The mutable execution state:
  The current basic block (I) and the Register Bank (R).
-/
abbrev State := BasicBlock × RegisterBank

/--
  Small-step operational semantics for sMIRA.
  `C` is the immutable Code Heap (environment).
-/
inductive Step (C : Program) : State → State → Prop where

  | mov : ∀ {rb rₙ pₙ o I rb' v pOld},
      Eval rb o v →
      Update rb (Operand.psd pₙ) rₙ rb' pOld →
      Step C
        (BasicBlock.cons (Inst.mov (Operand.reg rₙ pₙ) o) I, rb)
        (I, rb')

  | jmp : ∀ {rb lbl I'},
      Proj C lbl.id I' →
      Step C
        (BasicBlock.jump lbl, rb)
        (I', rb)

  | jeq : ∀ {rb rₙ pₙ l I v},
      Eval rb (Operand.reg rₙ pₙ) v →
      Step C
        (BasicBlock.cons (Inst.cnd (Operand.reg rₙ pₙ) l) I, rb)
        (I, rb)

  | jne : ∀ {rb rₙ pₙ lbl I I' v},
      Eval rb (Operand.reg rₙ pₙ) v →
      Proj C lbl.id I' →
      Step C
        (BasicBlock.cons (Inst.cnd (Operand.reg rₙ pₙ) lbl) I, rb)
        (I', rb)

-- Notation: Environment ⊢ State₁ ⇒ State₂
notation C " ⊢ " s1 " ⇒ " s2 => Step C s1 s2


-- =============== Types ====================

/-- Types in the register allocator. -/
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
  Code heap type (Ψ).
-/
abbrev TypeHeap := List TypeEnv

/--
  `Sub Γ Γ'` means environment `Γ` is a valid subtype of `Γ'`.
-/
inductive Sub : TypeEnv → TypeEnv → Prop where
  | empbk : Sub [] []
  /--
    If the target block expects `psd 0` (uninitialized/dead),
    the current block can safely provide any pseudo `pₙ`.
  -/
  | rzero : ∀ {n Γ Γ'},
      Sub Γ Γ' →
      Sub (Ty.psd n :: Γ) (Ty.psd 0 :: Γ')
  /--
    If the target expects a live pseudo (succ n),
    we must provide that live pseudo.
  -/
  | rnotz : ∀ {n Γ Γ'},
      Sub Γ Γ' →
      Sub (Ty.psd (Nat.succ n) :: Γ) (Ty.psd (Nat.succ n) :: Γ')

-- Subtyping notation
infix:50 " ⊑ " => Sub

/--
  Types of operands of instructions.

  `TyOP G O T` means operand `O` has type `T` in environment `G`.
-/
inductive TyOp : TypeEnv → Operand → Ty → Prop where
  | gab : ∀ {Γ}, TyOp Γ Operand.blt Ty.const
  | reg : ∀ {Γ rₙ pₙ},
      Proj Γ rₙ (Ty.psd pₙ) →
      NotZero pₙ →
      TyOp Γ (Operand.reg rₙ pₙ) (Ty.psd pₙ)

-- Operand typing notation
notation:50 Γ " ⊢ₒ " o " : " T => TyOp Γ o T
/--
  Types of instructions.
-/
inductive TyInst : TypeHeap → TypeEnv → Inst → TypeEnv → Prop where
  | mov : ∀ {Ψ Γ₀ Γ₁ rₙ pₙ o Tₒ pOld},
      (Γ₀ ⊢ₒ o : Tₒ) →
      NotZero pₙ →
      Update Γ₀ (Ty.psd pₙ) rₙ Γ₁ pOld →
      TyInst Ψ Γ₀ (Inst.mov (Operand.reg rₙ pₙ) o) Γ₁
  | cnd : ∀ {Ψ Γ Γ' rₙ pₙ lbl Tₒ},
      (Γ ⊢ₒ (Operand.reg rₙ pₙ) : Tₒ) →
      Proj Ψ lbl.id Γ' →  -- Project the expected type of the target label
      (Γ ⊑ Γ') →          -- Ensure our current state `G` satisfies `G'`
      TyInst Ψ Γ (Inst.cnd (Operand.reg rₙ pₙ) lbl) Γ
      -- `cnd` doesn't change the environment if it falls through.

-- Instruction typing notation
notation:50 Ψ " ⊢ᵢ " inst " : " Γ₀ " ↦ " Γ₁ => TyInst Ψ Γ₀ inst Γ₁

/--
  Types of basic blocks.
-/
inductive TyBlock : TypeHeap → TypeEnv → BasicBlock → Prop where
  | cons : ∀ {Ψ Γ Γ' inst I},
      (Ψ ⊢ᵢ inst : Γ ↦ Γ') →
      TyBlock Ψ Γ' I →
      TyBlock Ψ Γ (BasicBlock.cons inst I)
  | jump : ∀ {Ψ Γ Γ' lbl},
      Proj Ψ lbl.id Γ' →
      (Γ ⊑ Γ') →
      TyBlock Ψ Γ (BasicBlock.jump lbl)

notation:50 Ψ " ⊢ₛ " block " : " Γ => TyBlock Ψ Γ block

/--
  Type of the register bank.

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
  Auxiliary lemma for the Code Heap type.

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

/-- Type of the code heap `C`. -/
inductive TyCodeHeap : TypeHeap → Program → Prop where
  | mk : ∀ {Ψ C},
      TyCodeHeapAux Ψ C Ψ →
      TyCodeHeap Ψ C

notation:50 "⊢ₕ " C " : " Ψ => TyCodeHeap Ψ C

/--
  Type of a machine state.

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


-- =============== Subtyping theorems ====================

/--
  If `Γ ⊑ Γ'` and `Γ'` projects a live variable `pₙ` at register `rₙ`,
  then `Γ` must also project that exact same variable `pₙ` at `rₙ`.
-/
theorem subRegLemma {Γ Γ' : TypeEnv} {rₙ pₙ : Nat}
    (hSub : Γ ⊑ Γ')
    (hProj' : Proj Γ' rₙ (Ty.psd pₙ))
    (hNZ : NotZero pₙ) :
    Proj Γ rₙ (Ty.psd pₙ) := by
  induction hSub generalizing rₙ pₙ with
  -- If the environments are empty, projecting is impossible.
  | empbk => contradiction
  | rzero _ hSub_ih =>
    -- The target environment expects `.psd 0` at the head.
    cases hProj' with
    | z => contradiction
    | s hProj_tail => exact Proj.s (hSub_ih hProj_tail hNZ)
  | rnotz _ hSub_ih =>
    -- Both environments expect `psd (succ n)` at the head.
    cases hProj' with
    | z => exact Proj.z
    | s hProj_tail => exact Proj.s (hSub_ih hProj_tail hNZ)

/--
  Transitivity of subtyping.

  If `S ⊑ T` and `T ⊑ R`, then `S ⊑ R`.
-/
theorem subTransLemma {S T R : TypeEnv}
    (hST : S ⊑ T)
    (hTR : T ⊑ R) :
    S ⊑ R := by
  induction hST generalizing R with
  | empbk => exact hTR
  | rzero _ hST_ih =>
    cases hTR with
    | rzero hTR_tail => exact Sub.rzero (hST_ih hTR_tail)
    -- `rnotz` pruned
  | rnotz _ hST_ih =>
    cases hTR with
    | rzero hTR_tail => exact Sub.rzero (hST_ih hTR_tail)
    | rnotz hTR_tail => exact Sub.rnotz (hST_ih hTR_tail)

/--
  If `Γ ⊑ Γ'` and you can successfully update register `rₙ` in `Γ'`,
  then you can successfully update register `rₙ` in `Γ`.
-/
theorem subUpdtLemma {Γ Γ' Γ'_new : TypeEnv} {rₙ pₙ : Nat} {y' : Ty}
    (hSub : Γ ⊑ Γ')
    (hUpdt' : Update Γ' (Ty.psd pₙ) rₙ Γ'_new y') :
    ∃ Γ_new y, Update Γ (Ty.psd pₙ) rₙ Γ_new y := by
  induction hSub generalizing rₙ Γ'_new y' with
  -- Empty environment.
  | empbk => contradiction
  | rzero _ hSub_ih =>
    -- Target expects `psd 0`
    cases hUpdt' with
    | z => exact ⟨_, _, Update.z⟩
    | s hUpdt_tail =>
      have ⟨Γ_new_tail, y, hUpdt_G_tail⟩ := hSub_ih hUpdt_tail
      exact ⟨_, _, Update.s hUpdt_G_tail⟩
  | rnotz _ hSub_ih =>
    -- Both expect `psd (succ n)`.
    cases hUpdt' with
    | z => exact ⟨_, _, Update.z⟩
    | s hUpdt_tail =>
      have ⟨Γ_new_tail, y, hUpdt_G_tail⟩ := hSub_ih hUpdt_tail
      exact ⟨_, _, Update.s hUpdt_G_tail⟩

/--
  Preservation of subtyping after move.

  If `Γ ⊑ Γ'`, and we overwrite register `rₙ` with a live variable `pₙ`
  in both environments, the resulting environments still satisfy `Γ_new ⊑ Γ'_new`.
-/
theorem subUpdtSubLemma {Γ Γ' Γ_new Γ'_new : TypeEnv} {rₙ pₙ : Nat} {y y' : Ty}
    (hSub : Γ ⊑ Γ')
    (hUpdt' : Update Γ' (Ty.psd pₙ) rₙ Γ'_new y')
    (hUpdt : Update Γ (Ty.psd pₙ) rₙ Γ_new y)
    (hNZ : NotZero pₙ) :
    Γ_new ⊑ Γ'_new := by
  induction hSub generalizing rₙ Γ'_new Γ_new y y' with
  | empbk => contradiction
  | rzero hSub_tail hSub_ih =>
    cases hUpdt' with
    | z =>
      cases hUpdt
      cases hNZ
      exact Sub.rnotz hSub_tail
    | s hUpdt'_tail =>
      cases hUpdt with
      | s hUpdt_tail => exact Sub.rzero (hSub_ih hUpdt'_tail hUpdt_tail)
  | rnotz hSub_tail hSub_ih =>
    cases hUpdt' with
    | z =>
      cases hUpdt
      cases hNZ
      exact Sub.rnotz hSub_tail
    | s hUpdt'_tail =>
      cases hUpdt with
      | s hUpdt_tail => exact Sub.rnotz (hSub_ih hUpdt'_tail hUpdt_tail)


-- =============== Type soundness theorems ====================

/--
  Auxiliary lemma for the sequencing lemma.

  Iterates through the code heap C and type heap Ψ simultaneously.
-/
theorem seqLemmaAux {Ψ Ψ' C n I Γ}
    (hTCHA : TyCodeHeapAux Ψ C Ψ')
    (hProjC : Proj C n I)
    (hProjΨ : Proj Ψ' n Γ) :
    Ψ ⊢ₛ I : Γ := by
  induction hTCHA generalizing n I Γ with
  -- Code heap cannot be empty
  | nil => contradiction
  | cons hBlk _ hTCHA_ih =>
    -- Code heap is `I_head :: C_tail` and `Ψ'` is `Γ_head :: Ψ'_tail`.
    cases hProjC with
    | z =>
      cases hProjΨ with
      | z => exact hBlk
    | s hProjC_tail =>
      cases hProjΨ with
      | s hProjΨ_tail => exact hTCHA_ih hProjC_tail hProjΨ_tail

/-
  Sequencing lemma.

  If the code heap `C` is well-typed with `Ψ`, projecting the `n`-th
  block and the `n`-th expected environment yields a well-typed block.
-/
theorem seqLemma {Ψ C n I Γ}
    (hTCH : ⊢ₕ C : Ψ)
    (hProjC : Proj C n I)
    (hProjΨ : Proj Ψ n Γ) :
    Ψ ⊢ₛ I : Γ := by
  cases hTCH with
  | mk hTCHA => exact seqLemmaAux hTCHA hProjC hProjΨ

/--
  Register bank consistency.

  If the physical register bank matches the type environment, and
  both are updated at the same index with the same pseudo-variable,
  the resulting register bank matches the resulting environment.
-/
theorem rbLemma {R R' Γ Γ' rₙ pₙ} {o : Operand} {τ : Ty}
    (hTRB : ⊢ᵣ R : Γ)
    (hUR : Update R (Operand.psd pₙ) rₙ R' o)
    (hUG : Update Γ (Ty.psd pₙ) rₙ Γ' τ) :
    ⊢ᵣ R' : Γ' := by
  induction hTRB generalizing rₙ R' Γ' o τ with
  | nil => contradiction
  | cons hTRB_tail hTRB_ih =>
    cases hUR with
    | z =>
      cases hUG with
      | z => exact TyRegBank.cons hTRB_tail
    | s hUR_tail =>
      cases hUG with
      | s hUG_tail =>
        exact TyRegBank.cons (hTRB_ih hUR_tail hUG_tail)

/--
  Preservation theorem for sMIRA.

  If a machine state is well-typed under the code heap `C`, and it
  takes exactly one execution step to a new state, the resulting state
  is guaranteed to be well-typed.
-/
theorem preservation {C : Program} {s₁ s₂ : State}
    (hTy : ⊢ₘ ⟨C, s₁⟩)
    (hStep : C ⊢ s₁ ⇒ s₂) :
    ⊢ₘ ⟨C, s₂⟩ := by
  have ⟨h_code, h_reg, h_blk, h_sub⟩ := hTy
  cases hStep with
  -- `mov` case
  | mov h_eval h_updt_rb =>
    cases h_blk with
    | cons h_inst h_blk_tail =>
      cases h_inst with
      | mov h_op h_nz h_updt_Γ' =>
        have ⟨Γ_new, pOld_Γ, h_updt_Γ⟩ := subUpdtLemma h_sub h_updt_Γ'
        have h_sub_new := subUpdtSubLemma h_sub h_updt_Γ' h_updt_Γ h_nz
        have h_reg_new := rbLemma h_reg h_updt_rb h_updt_Γ
        exact TyState.mk h_code h_reg_new h_blk_tail h_sub_new
  -- `jeq` case
  | jeq h_eval =>
    cases h_blk with
    | cons h_inst h_blk_tail =>
      cases h_inst with
      | cnd _ _ _ => exact TyState.mk h_code h_reg h_blk_tail h_sub
  -- `jmp` case
  | jmp h_proj_C =>
    cases h_blk with
    | jump h_proj_Ψ h_sub' =>
      have h_blk_target := seqLemma h_code h_proj_C h_proj_Ψ
      have h_sub_total := subTransLemma h_sub h_sub'
      exact TyState.mk h_code h_reg h_blk_target h_sub_total
  -- `jne` case
  | jne h_eval h_proj_C =>
    cases h_blk with
    | cons h_inst h_blk_tail =>
      cases h_inst with
      | cnd h_op h_proj_Ψ h_sub' =>
        have h_blk_target := seqLemma h_code h_proj_C h_proj_Ψ
        have h_sub_total := subTransLemma h_sub h_sub'
        exact TyState.mk h_code h_reg h_blk_target h_sub_total

/-
  Register bank updatability.

  If the regsiter bank matches the type environment, and the environment
  can be updated at index `rₙ`, then the physical register bank can also
  be updated at index `rₙ`.
-/
theorem updtLemma {R : RegisterBank} {Γ Γ' : TypeEnv} {rₙ pₙ : Nat} {τ : Ty}
    (hTRB : ⊢ᵣ R : Γ)
    (hUG : Update Γ (Ty.psd pₙ) rₙ Γ' τ) :
    ∃ R' o, Update R (Operand.psd pₙ) rₙ R' o := by
  induction hTRB generalizing rₙ Γ' τ with
  -- Empty environments.
  | nil => contradiction
  | cons hTRB_tail hTRB_ih =>
    -- R and Γ share identical heads.
    -- Inspect where the environment update occurred:
    cases hUG with
    | z => exact ⟨_, _, Update.z⟩
    | s hUG_tail =>
      have ⟨R'_new_tail, x, hUR_tail⟩ := hTRB_ih hUG_tail
      exact ⟨_, _, Update.s hUR_tail⟩

/--
  Register bank projection.

  If the register bank matches the type environment, and the environment
  projects a live pseudo-variable at index `rₙ`, the register bank
  projects that exact same pseudo-variable at `rₙ`.
-/
theorem regLemma {R : RegisterBank} {Γ : TypeEnv} {rₙ pₙ : Nat}
    (hTRB : ⊢ᵣ R : Γ)
    (hProjΓ : Proj Γ rₙ (Ty.psd pₙ)) :
    Proj R rₙ (Operand.psd pₙ) := by
  induction hTRB generalizing rₙ pₙ with
  | nil => contradiction
  | cons hTRB_tail hTRB_ih =>
    cases hProjΓ with
    | z => exact Proj.z
    | s hProjΓ_tail => exact Proj.s (hTRB_ih hProjΓ_tail)

/--
  Auxiliary for the jump lemma (code heap projection).

  Iterates through the code heap and type heap simultaneously.
-/
theorem jmpLemmaAux {Ψ Ψ' : TypeHeap} {C' : Program} {n : Nat} {Γ : TypeEnv}
    (hTCHA : TyCodeHeapAux Ψ C' Ψ')
    (hProjΨ : Proj Ψ' n Γ) :
    ∃ I : BasicBlock, Proj C' n I := by
  induction hTCHA generalizing n Γ with
  | nil => contradiction
  | cons _ _ hTCHA_ih =>
    cases hProjΨ with
    | z => exact ⟨_, Proj.z⟩
    | s hProjΨ_tail =>
      have ⟨I_tail, hProjC_tail⟩ := hTCHA_ih hProjΨ_tail
      exact ⟨_, Proj.s hProjC_tail⟩

/--
  Jump lemma (code heap projection)
-/
theorem jmpLemma {Ψ : TypeHeap} {C : Program} {n : Nat} {Γ : TypeEnv}
    (hTCH : ⊢ₕ C : Ψ)
    (hProjΨ : Proj Ψ n Γ) :
    ∃ I : BasicBlock, Proj C n I := by
  have ⟨hTCHA⟩ := hTCH
  exact jmpLemmaAux hTCHA hProjΨ

/--
  Progress theorem for sMIRA.

  If a machine state is well-typed, it can always take at least one valid
  execution step. Note that there is no termination in sMIRA.
-/
theorem progress {C : Program} {R : RegisterBank} {I : BasicBlock}
    (hTy : ⊢ₘ ⟨C, (I, R)⟩) :
    ∃ s', C ⊢ (I, R) ⇒ s' := by
  have ⟨h_code, h_reg, h_blk, h_sub⟩ := hTy
  cases h_blk with
  | jump h_proj_Ψ _ =>
    -- Unconditional `jmp` to a label.
    have ⟨I_target, h_proj_C⟩ := jmpLemma h_code h_proj_Ψ
    exact ⟨(I_target, R), Step.jmp h_proj_C⟩
  | cons h_inst _ =>
    -- Instruction at the head of the block.
    cases h_inst with
    | mov h_op _ h_updt_Γ' =>
      -- The instruction is `mov`.
      cases h_op with
      | gab =>
        -- Operand is a bullet.
        have ⟨Γ_new, _, h_updt_Γ⟩ := subUpdtLemma h_sub h_updt_Γ'
        have ⟨R_new, _, h_updt_R⟩ := updtLemma h_reg h_updt_Γ
        exact ⟨(_, R_new), Step.mov Eval.blt h_updt_R⟩
      | reg h_proj_Γ' h_nz_src =>
        -- Operand is a physical register.
        have h_proj_Γ := subRegLemma h_sub h_proj_Γ' h_nz_src
        have h_proj_R := regLemma h_reg h_proj_Γ
        have h_eval := Eval.reg h_proj_R h_nz_src

        have ⟨Γ_new, _, h_updt_Γ⟩ := subUpdtLemma h_sub h_updt_Γ'
        have ⟨R_new, _, h_updt_R⟩ := updtLemma h_reg h_updt_Γ
        exact ⟨(_, R_new), Step.mov h_eval h_updt_R⟩
    | cnd h_op _ _ =>
      -- Instruction is `cnd`. We know `op` must be a `reg`
      cases h_op with
      | reg h_proj_Γ' h_nz_src =>
        have h_proj_Γ := subRegLemma h_sub h_proj_Γ' h_nz_src
        have h_proj_R := regLemma h_reg h_proj_Γ
        have h_eval := Eval.reg h_proj_R h_nz_src
        exact ⟨(_, R), Step.jeq h_eval⟩

end Smira
