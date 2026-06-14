import SmiraLean.AST
import SmiraLean.Semantics
import SmiraLean.Typing

namespace Smira

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

end Smira
