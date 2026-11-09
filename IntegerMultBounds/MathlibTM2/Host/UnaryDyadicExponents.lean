module

public import IntegerMultBounds.MathlibTM2.Host.UnaryBitLength
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Derive a power-of-two exponent and a ceiling exponent from borrowed unary
counts. Both computations reuse one restored arithmetic workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def unaryDyadicExponents (replicas rows power ceil a half par bits saved : Fin T) : Pr P T Q A U :=
  .seq (unaryPowerExponent replicas power a half par bits saved)
    (unaryBitLength true rows ceil a half par bits saved)

theorem unaryDyadicExponents_exec_within (replicas rows power ceil a half par bits saved : Fin T)
    (hreg : [replicas,rows,power,ceil,a,half,par,bits,saved].Nodup)
    (b N depth : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = 2^b) (hrows : (S.R rows).length = N)
    (hblank : ∀ r ∈ [power,ceil,a,half,par,bits,saved], S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (19*2^b+10)+(19*N+9) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(19*2^b+10)+2*(19*N+9))) depth
        (unaryDyadicExponents replicas rows power ceil a half par bits saved) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R power (List.replicate b tick))
          ceil (List.replicate (Nat.clog 2 N) tick))}) := by
  regs_ne hreg
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryPowerExponent_exec_within (body := body)
    replicas power a half par bits saved (by regs_nodup) b v S hreplicas
    (by
      intro r hr
      apply hblank r
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      rcases hr with hr | hr
      · exact Or.inl hr
      · exact Or.inr (Or.inr hr)) depth
  let M : Stacks T A := {S with R := Function.update S.R power (List.replicate b tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryCeilLog_exec_within (body := body)
    rows ceil a half par bits saved (by regs_nodup) N v₁ M
    (by simpa only [M,Function.update_of_ne ‹rows ≠ power›] using hrows)
    (by
      intro r hr
      have hr' : r ∈ [power,ceil,a,half,par,bits,saved] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
        exact Or.inr hr
      have hne : r ≠ power := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      simpa only [M,Function.update_of_ne hne] using hblank r hr') depth
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    by simpa only [unaryDyadicExponents,M] using mn_seq_within_add he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Host
