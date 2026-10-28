module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySizes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloAdvanceWidth

/-! Generate a shared geometry workspace for halo origins and symbol advances. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloGeometryWidth (t w : ℕ) : ℕ := 2*Nat.size t+Nat.size w+7

theorem haloGeometryWidth_fits {t band w : ℕ} (hband : band ≤ t) :
    8*(t+1)^2+2*band+8 < 2^haloGeometryWidth t w := by
  let N := 2^Nat.size t
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have ht : t+1 ≤ N := Nat.lt_size_self t
  have hb : band ≤ N := hband.trans (by omega)
  have hsq := Nat.pow_le_pow_left ht 2
  have hpoly : 8*(t+1)^2+2*band+8 < 128*N^2 := by nlinarith only [hsq,hb,hN]
  have hpow : 128*N^2 = 2^(2*Nat.size t+7) := by
    dsimp only [N]
    rw [← pow_mul,show Nat.size t*2 = 2*Nat.size t by omega,pow_add]
    norm_num
    ring
  rw [hpow] at hpoly
  exact hpoly.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [haloGeometryWidth]; omega))

theorem haloControlWidth_le_geometryWidth {s t band w : ℕ} (hst : s ≤ t) (hband : band ≤ t) :
    haloControlWidth s t band w ≤ haloGeometryWidth t w := by
  apply max_le
  · exact Nat.size_le.mpr (haloGeometryWidth_fits hband)
  · have h := haloAdvanceWidth_le s w
    have hs := Nat.size_le_size hst
    dsimp only [haloGeometryWidth]
    omega

def generateHaloGeometryWidth : Pr P₀ 117 Q A U :=
  .seq (.act (pushN 115 (fun _ => tick) 7 .done)) (addUnarySizes [98,98,94])

def generateHaloGeometryWidthCost (t w : ℕ) : ℕ := 38*t+19*w+26

theorem generateHaloGeometryWidth_exec (t w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (ht : (S.R 98).length = t) (hw : (S.R 94).length = w)
    (h115 : S.R 115 = [])
    (hfresh : ∀ k ∈ [(0 : Fin 117),1,2,3,4], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateHaloGeometryWidthCost t w ∧
      Exec body generateHaloGeometryWidth (mk v S) n
        (mk v' {S with R := Function.update S.R 115 (List.replicate (haloGeometryWidth t w) tick)}) := by
  let B : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate 7 tick)}
  have he₁ : Exec body (.act (pushN 115 (fun _ => tick) 7 .done)) (mk v S) 1 (mk v B) := by
    have he := Exec.act (body := body) (pushN 115 (fun _ => tick) 7 .done) (mk v S)
    simpa [B,pushN_run,Action.run,h115] using he
  let value := fun r : Fin 117 => (S.R r).length
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := addUnarySizes_exec (body := body) [98,98,94]
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)
    value v B (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
                  rcases hr with rfl | rfl | rfl <;> simp [B,value])
    (by intro k hk; have hne : k ≠ 115 := by intro he; subst k; norm_num at hk
        simpa [B,hne] using hfresh k hk)
  have hcost : (([98,98,94] : List (Fin 117)).map (fun r => 19*value r+8)).sum =
      38*t+19*w+24 := by simp [value,ht,hw]; ring
  have hsize : (([98,98,94] : List (Fin 117)).map (fun r => Nat.size (value r))).sum =
      2*Nat.size t+Nat.size w := by simp [value,ht,hw]; ring
  rw [hcost] at hn₂
  rw [hsize] at he₂
  refine ⟨v₂,1+n₂,hu₂,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · dsimp [generateHaloGeometryWidthCost]; omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 115
    · subst k
      change List.replicate (2*Nat.size t+Nat.size w) tick ++ List.replicate 7 tick =
        List.replicate (haloGeometryWidth t w) tick
      rw [List.replicate_append_replicate]
      simp only [haloGeometryWidth]
    · simp [B,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
