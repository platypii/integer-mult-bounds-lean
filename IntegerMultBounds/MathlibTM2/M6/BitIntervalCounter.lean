module

public import IntegerMultBounds.MathlibTM2.Host.UnaryBinaryHalving
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordVolumeHeaders

/-! Build the internal row splitter's binary counter from the inherited payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast

def intervalCounter {T Q A : ℕ} {P U : Type} (r : Fin 9 ↪ Fin T) : Pr P T Q A U :=
  (udiv 142080 (r 0) (r 1) (r 8)).seq
    ((unaryBinary (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8)).seq (uclear (r 1)))

/-- Count complete role groups, retaining the payload and clearing all temporary words. -/
theorem intervalCounter_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (r : Fin 9 ↪ Fin T) (m : ℕ) (u : HS T Q A U) (S : Stacks T A)
    (size : (S.R (r 0)).length = m*142080) (empty : ∀ i, i ≠ 0 → S.R (r i) = []) :
    ∃ z t, z.user = u.user ∧ t ≤ 4*(m*142080)+23*m+16 ∧
      Exec body (intervalCounter r) (mk u S) t
        (mk z {S with R := Function.update S.R (r 2) ((FlatCoordinateSchedule.bits m).map bitSymbol)}) := by
  have ne {i j : Fin 9} (h : i ≠ j) := r.injective.ne h
  obtain ⟨v,t,user,time,div⟩ := udiv_exec body (by decide : 1 ≤ 142080)
    (ne (by decide : (0 : Fin 9) ≠ 1)) (ne (by decide : (0 : Fin 9) ≠ 8))
    (ne (by decide : (1 : Fin 9) ≠ 8)) u S (empty 8 (by decide))
  rw [size, Nat.mul_div_cancel _ (by decide), empty 1 (by decide), List.append_nil] at div
  let D : Stacks T A := {S with R := Function.update S.R (r 1) (List.replicate m tick)}
  have regs := ((by decide : ([1,2,3,4,5,6,7,8] : List (Fin 9)).Nodup).map r.injective)
  obtain ⟨w,b,wu,bt,encode⟩ := unaryBinary_exec (body := body) regs m v D
    (by simp [D]) (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
                      rcases hk with h|h|h|h|h|h|h <;> subst k <;> simp [D,r.injective.eq_iff,empty])
  obtain ⟨z,zu,clear⟩ := uclear_exec body (r 1) w _
  have run := Exec.seq div (Exec.seq encode clear)
  refine ⟨z,t+(b+(2*m+2)),zu.trans (wu.trans user),?_,?_⟩
  · rw [size] at time
    omega
  · have restore (xs : List (Fin (A+4))) :
        Function.update (Function.update S.R (r 2) xs) (r 1) (S.R (r 1)) = Function.update S.R (r 2) xs := by
      funext j
      by_cases h : j = r 1
      · subst j; simp [r.injective.eq_iff]
      · simp [Function.update_of_ne h]
    simpa [restore,intervalCounter,D,r.injective.eq_iff,Function.update_comm (ne (by decide : (1 : Fin 9) ≠ 2)),
      Function.update_idem,← empty 1 (by decide), Cover.Fallback.canonicalBits_symbols] using run

end IntegerMultBounds.MathlibTM2.M6.BitNode
