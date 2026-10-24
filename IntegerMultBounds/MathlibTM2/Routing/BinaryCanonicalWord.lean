module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalCopy
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCeilLogData
public import IntegerMultBounds.MathlibTM2.Routing.SourceMask

/-! Identify the existing canonical-copy routine with the exact shortest binary
word, including zero. No target-width computation or resizing is needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

theorem canonicalBits_binSyms {A : ℕ} (bs : List Bool) (hc : GrowingCounterData.Canonical bs) :
    (bs.map bitSymbol : List (Fin (A+4))) =
      binSyms (Nat.clog 2 (Counter.value bs+1)) (Counter.value bs) := by
  have hl := canonicalBinary_length_clog bs hc
  have hb := binaryBits_value_repr bs
  rw [hl] at hb
  rw [binSyms_eq,hb]

theorem binaryCanonicalWord_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src tmp : Fin T) (hst : src ≠ tmp)
    (L x : ℕ) (hx : x < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms L x) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryCanonicalProgram src tmp) (mk v S) (4*L+6)
        (mk v' { S with R := Function.update S.R src (binSyms (Nat.clog 2 (x+1)) x) }) := by
  obtain ⟨bs,v',hc,hv,_,hu,he⟩ := binaryCanonical_exec body src tmp hst L x hx v S hsrc htmp
  have hb := canonicalBits_binSyms (A := A) bs hc
  rw [hv] at hb
  rw [hb] at he
  exact ⟨v',hu,he⟩

theorem binaryCanonicalWordCopy_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src dst tmp work : Fin T)
    (hregs : [src,dst,tmp,work].Nodup) (L x : ℕ) (hx : x < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L x)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryCanonicalCopyProgram src dst tmp work) (mk v S) (10 * L + 12)
        (mk v' { S with R := Function.update S.R dst (binSyms (Nat.clog 2 (x+1)) x) }) := by
  obtain ⟨bs,v',hc,hv,_,hu,he⟩ := binaryCanonicalCopy_exec body src dst tmp work hregs L x hx
    v S hsrc hdst htmp hwork
  have hb := canonicalBits_binSyms (A := A) bs hc
  rw [hv] at hb
  rw [hb] at he
  exact ⟨v',hu,he⟩

end IntegerMultBounds.MathlibTM2.Routing
