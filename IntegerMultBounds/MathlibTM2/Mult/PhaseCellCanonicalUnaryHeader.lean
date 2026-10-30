module

public import IntegerMultBounds.MathlibTM2.Host.UnaryBinaryHalving
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalData

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

/-- The halving converter emits precisely the canonical binary digits. -/
theorem binBits_size_bits (n : ℕ) : binBits (Nat.size n) n = n.bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [binBits]
  | bit b n h ih =>
    have hne : Nat.bit b n ≠ 0 := by
      intro he
      have hz := Nat.bit_eq_zero_iff.mp he
      have hb := h hz.1
      simp_all
    rw [Nat.size_bit hne,binBits_succ,Nat.bits_append_bit n b h]
    cases b <;> simp [Nat.bit,Nat.testBit_zero,ih,Nat.mul_comm]
    rw [show (n*2+1)/2 = n by omega]
    exact ih

theorem nat_bits_canonical (n : ℕ) : GrowingCounterData.Canonical n.bits := by
  induction n using Nat.binaryRec' with
  | zero => exact Or.inl rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    by_cases hn : n = 0
    · subst n
      have hb := h rfl
      subst b
      exact Or.inr rfl
    · have hnonempty : n.bits ≠ [] := by
        intro he
        have hh := congrArg List.length he
        rw [Nat.size_eq_bits_len] at hh
        exact hn (Nat.size_eq_zero.mp hh)
      have hlast := ih.resolve_left hnonempty
      cases he : n.bits with
      | nil => exact False.elim (hnonempty he)
      | cons c cs => exact Or.inr (by simpa only [he,List.getLast?_cons_cons] using hlast)

theorem binBits_size_canonical (n : ℕ) : GrowingCounterData.Canonical (binBits (Nat.size n) n) := by
  rw [binBits_size_bits]
  exact nat_bits_canonical n

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def canonicalUnaryHeader (src dst a half par bits cnt saved : Fin T) : Pr P T Q A U :=
  .seq (unaryBinary src dst a half par bits cnt saved)
    (.act (.push (.rt dst) (fun _ => separator) .done))

/-- Generate an actual interchange header from a borrowed unary dimension.
All arithmetic scratch is restored; no chosen bit word is assumed as input. -/
theorem canonicalUnaryHeader_exec
    (src dst a half par bits cnt saved : Fin T)
    (hreg : [src,dst,a,half,par,bits,cnt,saved].Nodup) (n : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hn : (S.R src).length = n)
    (hfresh : ∀ i ∈ [dst,a,half,par,bits,cnt,saved], S.R i = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 21*n+11 ∧
      Exec body (canonicalUnaryHeader src dst a half par bits cnt saved) (mk v S) m
        (mk v' {S with R := (Function.update S.R dst
          (separator::(binBits (Nat.size n) n).map bitSymbol))}) ∧
      Counter.value (binBits (Nat.size n) n) = n ∧
      GrowingCounterData.Canonical (binBits (Nat.size n) n) := by
  obtain ⟨v',m,hu,hm,he⟩ := unaryBinary_exec (body := body) hreg n v S hn hfresh
  let M : Stacks T A := {S with R := Function.update S.R dst (binSyms (Nat.size n) n)}
  have hp := Exec.act (body := body) (.push (.rt dst) (fun _ => separator) .done) (mk v' M)
  refine ⟨v',m+1,hu,by omega,(Exec.seq he hp).cast rfl ?_,?_,binBits_size_canonical n⟩
  · simp [M,Action.run,update_rt,binSyms,binBits,List.map_ofFn,Function.comp_def]
  · exact Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self n)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
