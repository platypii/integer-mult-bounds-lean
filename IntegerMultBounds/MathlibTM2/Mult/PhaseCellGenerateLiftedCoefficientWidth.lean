module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySizes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedCoefficientWidth

/-! Construct the shared lifted-coefficient width from ordinary unary headers.
Only its owned destination changes; headers and size-conversion scratch restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def liftedWidthSources : List (Fin 117) := (List.replicate 8 [(97 : Fin 117),98,99,100]).flatten

def generateLiftedCoefficientWidth : Pr P₀ 117 Q A U :=
  .seq (ucopy 94 115 104) (.seq (ucopy 112 115 104) (.seq (umul 13 114 115 104)
    (.seq (.act (pushN 115 (fun _ => tick) 24 .done)) (addUnarySizes liftedWidthSources))))

def generateLiftedCoefficientWidthCost (P q w s t u band : ℕ) : ℕ :=
  4*w+4*q+4*P+152*(s+t+u+band)+270

theorem generateLiftedCoefficientWidth_exec (P q w s t u band : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hq : (S.R 112).length = q) (hw : (S.R 94).length = w)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hu : (S.R 99).length = u) (hb : (S.R 100).length = band)
    (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (hfresh : ∀ k ∈ [(0 : Fin 117),1,2,3,4], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateLiftedCoefficientWidthCost P q w s t u band ∧
      Exec body generateLiftedCoefficientWidth (mk v S) n
        (mk v' {S with R := (Function.update S.R 115
          (List.replicate (liftedCoefficientWidth P q w s t u band) tick))}) := by
  let B (n : ℕ) : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate n tick)}
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 94) (b := 115) (t := 104)
    (by decide) (by decide) (by decide) v S h104
  have he₁' : Exec body (ucopy 94 115 104) (mk v S) (4*w+4) (mk v₁ (B w)) := by
    simpa [B,hw,h115] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 112) (b := 115) (t := 104)
    (by decide) (by decide) (by decide) v₁ (B w) (by simpa [B] using h104)
  have he₂' : Exec body (ucopy 112 115 104) (mk v₁ (B w)) (4*q+4) (mk v₂ (B (w+q))) := by
    simpa [B,hq,List.replicate_append_replicate,Nat.add_comm] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := umul_exec (body := body) 13 (a := 114) (b := 115) (t := 104)
    (by decide) (by decide) (by decide) v₂ (B (w+q)) (by simpa [B] using h104)
  have he₃' : Exec body (umul 13 114 115 104) (mk v₂ (B (w+q))) (4*P+4)
      (mk v₃ (B (w+q+13*P))) := by
    simpa [B,hP,List.replicate_append_replicate,Nat.add_comm] using he₃
  have he₄ := Exec.act (body := body) (pushN 115 (fun _ => tick) 24 .done) (mk v₃ (B (w+q+13*P)))
  rw [pushN_run,show (B (w+q+13*P)).R 115 = List.replicate (w+q+13*P) tick from rfl,
    List.replicate_append_replicate] at he₄
  have he₄' : Exec body (.act (pushN 115 (fun _ => tick) 24 .done))
      (mk v₃ (B (w+q+13*P))) 1 (mk v₃ (B (w+q+13*P+24))) := by
    simpa [B,Action.run,List.replicate_append_replicate,Nat.add_comm] using he₄
  let value := fun r : Fin 117 => (S.R r).length
  have hmem (r : Fin 117) (hr : r ∈ liftedWidthSources) : r = 97 ∨ r = 98 ∨ r = 99 ∨ r = 100 := by
    obtain ⟨rs,hrs,hr⟩ := List.mem_flatten.mp hr
    have he : rs = [(97 : Fin 117),98,99,100] := (List.mem_replicate.mp hrs).2
    subst rs
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hr
  obtain ⟨v₅,n₅,hu₅,hn₅,he₅⟩ := addUnarySizes_exec (body := body) liftedWidthSources
    (by intro r hr; rcases hmem r hr with rfl | rfl | rfl | rfl <;> decide)
    value v₃ (B (w+q+13*P+24)) (by
      intro r hr
      have hne : r ≠ 115 := by rcases hmem r hr with rfl | rfl | rfl | rfl <;> decide
      simp [B,hne,value]) (by
      intro k hk
      have hne : k ≠ 115 := by intro he; subst k; norm_num at hk
      simpa [B,hne] using hfresh k hk)
  have hcost : (liftedWidthSources.map (fun r => 19*value r+8)).sum =
      152*(s+t+u+band)+256 := by
    simp only [liftedWidthSources,List.map_flatten,List.sum_flatten,List.map_replicate,
      List.sum_replicate,smul_eq_mul]
    simp [value,hs,ht,hu,hb]; ring
  have hsize : (liftedWidthSources.map (fun r => Nat.size (value r))).sum =
      8*(Nat.size s+Nat.size t+Nat.size u+Nat.size band) := by
    simp only [liftedWidthSources,List.map_flatten,List.sum_flatten,List.map_replicate,
      List.sum_replicate,smul_eq_mul]
    simp [value,hs,ht,hu,hb]; ring
  rw [hcost] at hn₅
  rw [hsize] at he₅
  refine ⟨v₅,(4*w+4)+((4*q+4)+((4*P+4)+(1+n₅))),hu₅.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅)))).cast rfl ?_⟩
  · dsimp only [generateLiftedCoefficientWidthCost]; omega
  · apply congrArg (mk v₅)
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk : k = 115
      · subst k
        change List.replicate (8*(Nat.size s+Nat.size t+Nat.size u+Nat.size band)) tick++
          List.replicate (w+q+13*P+24) tick =
          List.replicate (liftedCoefficientWidth P q w s t u band) tick
        rw [List.replicate_append_replicate]
        have hv : 8*(Nat.size s+Nat.size t+Nat.size u+Nat.size band)+(w+q+13*P+24) =
            liftedCoefficientWidth P q w s t u band := by
          dsimp only [liftedCoefficientWidth,liftedCoefficientSize]
          omega
        rw [hv]
      · simp [B,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
