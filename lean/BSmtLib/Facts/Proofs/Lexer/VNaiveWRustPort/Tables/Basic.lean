module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes

@[expose] public section

/-!
# Byte tables checked byte by byte

`byte_table`: a property of every byte, from its check for every number below 256.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic

/-- A property of every byte, from its check for every number below 256. -/
theorem byte_table {P : UInt8 → Prop} (h : ∀ n, n < 256 → P n.toUInt8) (c : UInt8) : P c := by
  have := h c.toNat c.toNat_lt
  rwa [show c.toNat.toUInt8 = c by simp] at this

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic
