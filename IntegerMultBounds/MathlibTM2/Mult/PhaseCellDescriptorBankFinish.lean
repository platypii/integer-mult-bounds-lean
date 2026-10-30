module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorBank
public import IntegerMultBounds.MathlibTM2.Mult.ClearRegisterBank

/-! Collect a batch output in order and clear its private bank for the next key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def finishDescriptorBank (ports : List (Fin T)) (output result tmp : Fin T) : Pr P T Q A U :=
  .seq (moveR output tmp id) (.seq (moveR tmp result id) (clearWords ports))

theorem finishDescriptorBank_exec (ports : List (Fin T)) (hports : ports.Nodup)
    (output result tmp : Fin T) (houtput : output ∈ ports) (hresult : result ∉ ports)
    (htmp : tmp ∉ ports) (hrt : result ≠ tmp)
    (v : HS T Q A U) (S : Stacks T A) (hblank : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 4*(S.R output).length+2*(ports.map (fun k => (S.R k).length)).sum+2*ports.length+5 ∧
      Exec body (finishDescriptorBank ports output result tmp) (mk v S) n
        (mk v' {S with R := fun k => if k ∈ ports then [] else
          if k = result then S.R output++S.R result else S.R k}) := by
  have hot : output ≠ tmp := by intro he; exact htmp (he ▸ houtput)
  have hor : output ≠ result := by intro he; exact hresult (he ▸ houtput)
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body output tmp hot id v S
  let S₁ : Stacks T A := {S with R := movedR S.R output tmp id (S.R output)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body tmp result hrt.symm id v₁ S₁
  let S₂ : Stacks T A := {S₁ with R := movedR S₁.R tmp result id (S₁.R tmp)}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) ports hports v₂ S₂
  have ht₁ : (S₁.R tmp).length = (S.R output).length := by
    simp [S₁,movedR,hblank]
  have hbank (k : Fin T) (hk : k ∈ ports) : (S₂.R k).length ≤ (S.R k).length := by
    have hkr : k ≠ result := by intro he; exact hresult (he ▸ hk)
    have hkt : k ≠ tmp := by intro he; exact htmp (he ▸ hk)
    by_cases hko : k = output
    · subst k
      simp [S₂,S₁,movedR,hor,hot]
    · simp [S₂,S₁,movedR,hkr,hkt,hko]
  have hsum := List.sum_le_sum (l := ports) hbank
  refine ⟨v₃,(2*(S.R output).length+2)+((2*(S₁.R tmp).length+2)+
    (2*(ports.map (fun k => (S₂.R k).length)).sum+2*ports.length+1)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [ht₁]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ ports
    · simp [hk]
    · have hko : k ≠ output := by intro he; exact hk (he ▸ houtput)
      by_cases hkr : k = result
      · subst k
        simp [S₂,S₁,movedR,hresult,hblank,hrt,hor.symm]
      · by_cases hkt : k = tmp
        · subst k
          simp [S₂,S₁,movedR,htmp,hkr,hblank]
        · simp [S₂,S₁,movedR,hk,hkr,hkt,hko]

/-- Collect the output and restore both sides of every private register. -/
def finishDescriptorBankBoth (ports : List (Fin T)) (output result tmp : Fin T) : Pr P T Q A U :=
  .seq (finishDescriptorBank ports output result tmp) (clearRegisters ports)

theorem finishDescriptorBankBoth_exec (ports : List (Fin T)) (hports : ports.Nodup)
    (output result tmp : Fin T) (houtput : output ∈ ports) (hresult : result ∉ ports)
    (htmp : tmp ∉ ports) (hrt : result ≠ tmp)
    (v : HS T Q A U) (S : Stacks T A) (hblank : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 4 * (S.R output).length +
        2 * (ports.map (fun k => (S.R k).length)).sum +
        4 * (ports.map (fun k => (S.L k).length)).sum + 6 * ports.length + 6 ∧
      Exec body (finishDescriptorBankBoth ports output result tmp) (mk v S) n
        (mk v' {S with
          L := fun k => if k ∈ ports then [] else S.L k
          R := fun k => if k ∈ ports then [] else
            if k = result then S.R output ++ S.R result else S.R k}) := by
  obtain ⟨v₁, n, hu₁, hn, he₁⟩ := finishDescriptorBank_exec (body := body)
    ports hports output result tmp houtput hresult htmp hrt v S hblank
  let S₁ : Stacks T A := {S with
    R := fun k => if k ∈ ports then [] else
      if k = result then S.R output ++ S.R result else S.R k}
  obtain ⟨v₂, hu₂, he₂⟩ := clearRegisters_exec (body := body) ports hports v₁ S₁
  have hsum : (ports.map fun k => 4 * (S₁.L k).length + 2 * (S₁.R k).length).sum =
      4 * (ports.map fun k => (S.L k).length).sum := by
    trans (ports.map fun k => 4 * (S.L k).length).sum
    · congr 1
      apply List.map_congr_left
      intro k hk
      simp [S₁, hk]
    · exact List.sum_map_mul_left ports (fun k => (S.L k).length) 4
  refine ⟨v₂, _, hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl ?_⟩
  · rw [hsum]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ ports <;> simp [S₁, hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
