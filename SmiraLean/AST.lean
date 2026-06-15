namespace Smira

inductive Operand where
  /-- Pseudo-register (variable). -/
  | psd : Nat → Operand
  /-- Bullet, which has no effect in the allocation process. -/
  | blt : Operand
  /--
    Pre-colored register.

    Represents a pair `(rₙ, pₙ)`, where `rₙ` is a position in the register bank,
    and `pₙ` is the pseudo stored in that position.
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
  The code heap (C), or the program.

  It is essentially a lookup table where index `i` represents the label `i`. -/
abbrev Program := List BasicBlock

/-- Register bank R. -/
abbrev RegisterBank := List Operand

/--
  The mutable execution state:
  The current basic block (I) and the Register Bank (R).
-/
abbrev State := BasicBlock × RegisterBank

end Smira
