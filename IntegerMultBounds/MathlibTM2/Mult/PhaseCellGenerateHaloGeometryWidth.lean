module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloAdvanceWidth

/-! Generate a shared geometry workspace for halo origins and symbol advances. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloGeometryWidth (t band w : ℕ) : ℕ := publicationGeometryWidth t band+Nat.size w

theorem haloControlWidth_le_geometryWidth {s t band w : ℕ} (hst : s ≤ t) :
    haloControlWidth s t band w ≤ haloGeometryWidth t band w := by
  apply max_le
  · have h := Nat.size_le.mpr (publicationGeometryWidth_fits t band)
    change Nat.size (8*(t+1)^2+2*band+8) ≤ publicationGeometryWidth t band+Nat.size w
    omega
  · have h := haloAdvanceWidth_le s w
    have hs := Nat.size_le_size hst
    dsimp only [haloGeometryWidth,publicationGeometryWidth]
    omega

def generateHaloGeometryWidth : Pr P₀ 117 Q A U :=
  .seq (.act (pushN 115 (fun _ => tick) 7 .done)) (addUnarySizes [98,100,98,100,94])

def generateHaloGeometryWidthCost (t band w : ℕ) : ℕ := 38*(t+band)+19*w+42

theorem generateHaloGeometryWidth_exec (t band w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (ht : (S.R 98).length = t) (hb : (S.R 100).length = band) (hw : (S.R 94).length = w)
    (h115 : S.R 115 = [])
    (hfresh : ∀ k ∈ [(0 : Fin 117),1,2,3,4], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateHaloGeometryWidthCost t band w ∧
      Exec body generateHaloGeometryWidth (mk v S) n
        (mk v' {S with R := Function.update S.R 115 (List.replicate (haloGeometryWidth t band w) tick)}) := by
  let B : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate 7 tick)}
  have he₁ : Exec body (.act (pushN 115 (fun _ => tick) 7 .done)) (mk v S) 1 (mk v B) := by
    have he := Exec.act (body := body) (pushN 115 (fun _ => tick) 7 .done) (mk v S)
    simpa [B,pushN_run,Action.run,h115] using he
  let value := fun r : Fin 117 => (S.R r).length
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := addUnarySizes_exec (body := body) [98,100,98,100,94]
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    value v B (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [B,value])
    (by intro k hk; have hne : k ≠ 115 := by intro he; subst k; norm_num at hk
        simpa [B,hne] using hfresh k hk)
  have hcost : (([98,100,98,100,94] : List (Fin 117)).map (fun r => 19*value r+8)).sum =
      38*(t+band)+19*w+40 := by simp [value,ht,hb,hw]; ring
  have hsize : (([98,100,98,100,94] : List (Fin 117)).map (fun r => Nat.size (value r))).sum =
      2*(Nat.size t+Nat.size band)+Nat.size w := by simp [value,ht,hb,hw]; ring
  rw [hcost] at hn₂
  rw [hsize] at he₂
  refine ⟨v₂,1+n₂,hu₂,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · dsimp [generateHaloGeometryWidthCost]; omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 115
    · subst k
      change List.replicate (2*(Nat.size t+Nat.size band)+Nat.size w) tick ++ List.replicate 7 tick =
        List.replicate (haloGeometryWidth t band w) tick
      rw [List.replicate_append_replicate]
      simp only [haloGeometryWidth,publicationGeometryWidth]
      congr 1
      omega
    · simp [B,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
