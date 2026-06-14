import SmiraLean.AST
import SmiraLean.Semantics
import SmiraLean.Typing
import SmiraLean.Proofs.Subtyping

namespace Smira

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
