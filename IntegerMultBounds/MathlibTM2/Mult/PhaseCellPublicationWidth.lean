module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySizes

/-! Generate a geometry-sized workspace for the publication mask. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def publicationGeometryWidth (t band : ℕ) : ℕ := 2*(Nat.size t+Nat.size band)+7

theorem publicationGeometryWidth_fits (t band : ℕ) :
    8*(t+1)^2+2*band+8 < 2^(publicationGeometryWidth t band) := by
  let R := Nat.size t+Nat.size band
  let N := 2^R
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have htN : t ≤ N := (Nat.lt_size_self t).le.trans
    (Nat.pow_le_pow_right (by decide) (show Nat.size t ≤ R by dsimp [R]; omega))
  have hbN : band ≤ N := (Nat.lt_size_self band).le.trans
    (Nat.pow_le_pow_right (by decide) (show Nat.size band ≤ R by dsimp [R]; omega))
  have hsq : (t+1)^2 ≤ (2*N)^2 := Nat.pow_le_pow_left (by omega) 2
  have hsmall : 8*(t+1)^2+2*band+8 ≤ 64*N^2 := by nlinarith only [hsq,hbN,hN]
  have hpoly : 64*N^2 = 2^(2*R+6) := by
    dsimp only [N]
    rw [← pow_mul,show R*2 = 2*R by omega,pow_add]
    norm_num
    ring
  apply hsmall.trans_lt
  rw [hpoly]
  apply Nat.pow_lt_pow_right (by decide)
  dsimp [publicationGeometryWidth,R]
  omega

def generatePublicationWidth : Pr P₀ 117 Q A U :=
  .seq (.act (pushN 115 (fun _ => tick) 7 .done)) (addUnarySizes [98,100,98,100])

def generatePublicationWidthCost (t band : ℕ) : ℕ := 38*(t+band)+34

theorem generatePublicationWidth_exec (t band : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (ht : (S.R 98).length = t) (hb : (S.R 100).length = band)
    (h115 : S.R 115 = [])
    (hfresh : ∀ k ∈ [(0 : Fin 117),1,2,3,4], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatePublicationWidthCost t band ∧
      Exec body generatePublicationWidth (mk v S) n
        (mk v' {S with R := Function.update S.R 115 (List.replicate (publicationGeometryWidth t band) tick)}) := by
  let B : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate 7 tick)}
  have he₁ : Exec body (.act (pushN 115 (fun _ => tick) 7 .done)) (mk v S) 1 (mk v B) := by
    have he := Exec.act (body := body) (pushN 115 (fun _ => tick) 7 .done) (mk v S)
    simpa [B,pushN_run,Action.run,h115] using he
  let value := fun r : Fin 117 => (S.R r).length
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := addUnarySizes_exec (body := body) [98,100,98,100]
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)
    value v B (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
                  rcases hr with rfl | rfl | rfl | rfl <;> simp [B,value])
    (by intro k hk; have hne : k ≠ 115 := by intro he; subst k; norm_num at hk
        simpa [B,hne] using hfresh k hk)
  have hcost : (([98,100,98,100] : List (Fin 117)).map (fun r => 19*value r+8)).sum =
      38*(t+band)+32 := by simp [value,ht,hb]; ring
  have hsize : (([98,100,98,100] : List (Fin 117)).map (fun r => Nat.size (value r))).sum =
      2*(Nat.size t+Nat.size band) := by simp [value,ht,hb]; ring
  rw [hcost] at hn₂
  rw [hsize] at he₂
  refine ⟨v₂,1+n₂,hu₂,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · dsimp [generatePublicationWidthCost]; omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 115
    · subst k
      change List.replicate (2*(Nat.size t+Nat.size band)) tick ++ List.replicate 7 tick =
        List.replicate (publicationGeometryWidth t band) tick
      rw [List.replicate_append_replicate]
      rfl
    · simp [B,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
