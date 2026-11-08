module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySize

/-! A small scalar bank width generated from the two retained solver masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def cyclicNormalizationWidth (P q : ℕ) : ℕ := Nat.size P+Nat.size q+6

theorem cyclicNormalizationWidth_room (p q : ℕ) :
    2^15*p < 2^cyclicNormalizationWidth (2^15*p) q ∧
    8*(p+2) < 2^cyclicNormalizationWidth (2^15*p) q ∧
    2*q+8 < 2^cyclicNormalizationWidth (2^15*p) q := by
  let x := 2^Nat.size (2^15*p)
  let y := 2^Nat.size q
  have hx : 2^15*p < x := Nat.lt_size_self _
  have hy : q < y := Nat.lt_size_self _
  have hx1 : 1 ≤ x := Nat.one_le_two_pow
  have hy1 : 1 ≤ y := Nat.one_le_two_pow
  have hpow : 2^cyclicNormalizationWidth (2^15*p) q = x*y*64 := by
    simp [cyclicNormalizationWidth,pow_add,x,y]
  have hxyx : x ≤ x*y := by nlinarith only [hy1]
  have hxyy : y ≤ x*y := by nlinarith only [hx1]
  have hpx : p < x := by omega
  rw [hpow]
  constructor
  · omega
  constructor <;> omega

def generateCyclicNormalizationWidth (kernel precision width a h par bits saved : Fin T) : Pr P T Q A U :=
  .seq (unarySize kernel width a h par bits saved)
    (.seq (unarySize precision width a h par bits saved)
      (.act (pushN width (fun _ => tick) 6 .done)))

theorem generateCyclicNormalizationWidth_exec {kernel precision width a h par bits saved : Fin T}
    (hreg : [kernel,precision,width,a,h,par,bits,saved].Nodup)
    (P₀ q : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hP : (S.R kernel).length = P₀) (hq : (S.R precision).length = q)
    (hwidth : S.R width = []) (hfresh : ∀ k ∈ [a,h,par,bits,saved], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 19*P₀+19*q+17 ∧
      Exec body (generateCyclicNormalizationWidth kernel precision width a h par bits saved)
        (mk v S) m
        (mk v' {S with R := (Function.update S.R width
          (List.replicate (cyclicNormalizationWidth P₀ q) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unarySize_exec (body := body)
    (show [kernel,width,a,h,par,bits,saved].Nodup by regs_nodup) P₀ v S hP hfresh
  let S₁ : Stacks T A := {S with R := Function.update S.R width (List.replicate (Nat.size P₀) tick)}
  have he₁' : Exec body (unarySize kernel width a h par bits saved) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [S₁,hwidth,List.append_nil] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unarySize_exec (body := body)
    (show [precision,width,a,h,par,bits,saved].Nodup by regs_nodup) q v₁ S₁
    (by simpa [S₁,‹precision ≠ width›] using hq)
    (by intro k hk
        have hne : k ≠ width := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp_all [ne_comm]
        simpa [S₁,hne] using hfresh k hk)
  let S₂ : Stacks T A := {S with R := (Function.update S.R width
    (List.replicate (Nat.size q+Nat.size P₀) tick))}
  have he₂' : Exec body (unarySize precision width a h par bits saved) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₂,S₁,Function.update_self,←List.replicate_add,Function.update_idem] using he₂
  have he₃ := Exec.act (body := body) (pushN width (fun _ => tick) 6 .done) (mk v₂ S₂)
  refine ⟨v₂,m₁+(m₂+1),hu₂.trans hu₁,by omega,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast rfl ?_⟩
  rw [pushN_run]
  simp only [S₂,Action.run,Function.update_self,Function.update_idem]
  rw [List.replicate_append_replicate]
  have hn : 6+(Nat.size q+Nat.size P₀) = cyclicNormalizationWidth P₀ q := by
    dsimp [cyclicNormalizationWidth]
    omega
  rw [hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
