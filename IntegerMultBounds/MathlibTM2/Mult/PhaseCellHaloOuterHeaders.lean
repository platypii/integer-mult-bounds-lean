module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledHaloGroupInput

/-! Retained halo endpoints on 141 and 142 supply owned copies on the private
solver's 111 and 113. Master parameters and endpoints survive every class. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem copiedGroupR_endpoint {A : ℕ} (P N q l s t u band L : ℕ)
    (R : Fin 144 → List (Fin (A+4))) (k : Fin 144) (hk : k = 111 ∨ k = 113) :
    copiedGroupR P N q l s t u band L R k = R k := by
  apply unaryCopiesR_off
  intro r hr
  rcases hk with rfl | rfl
  all_goals
    simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def copiedHaloGroupR {A : ℕ} (P N q l s t u band a b L : ℕ)
    (R : Fin 144 → List (Fin (A+4))) :=
  Function.update (Function.update (copiedGroupR P N q l s t u band L R)
    111 (List.replicate a tick)) 113 (List.replicate b tick)

theorem copiedHaloGroupR_off {A : ℕ} (P N q l s t u band a b L : ℕ)
    (R : Fin 144 → List (Fin (A+4))) (k : Fin 144) (hk : 117 ≤ k.val) :
    copiedHaloGroupR P N q l s t u band a b L R k = R k := by
  have h111 : k ≠ (111 : Fin 144) := by intro he; subst k; norm_num at hk
  have h113 : k ≠ (113 : Fin 144) := by intro he; subst k; norm_num at hk
  simp [copiedHaloGroupR,h111,h113,copiedGroupR_off P N q l s t u band L R k hk]

theorem groupProject_haloEndpoints {A : ℕ} (S : Stacks 144 A) (a b : ℕ) :
    embStk groupReg { S with R := (Function.update (Function.update S.R 111 (List.replicate a tick))
      113 (List.replicate b tick)) } =
      { embStk groupReg S with R := haloEndpointR a b (embStk groupReg S).R } := by
  ext1
  · rfl
  · rfl
  · rfl
  funext i
  simp [embStk,groupReg,haloEndpointR,Function.update_apply,Fin.ext_iff]

theorem copiedHaloGroup_project {A : ℕ} (P N q l s t u band a b L : ℕ) (S : Stacks 144 A)
    (raw borrowed : List (Fin (A+4)))
    (hL : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hR : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsrc : S.R 110 = raw++borrowed) :
    embStk groupReg { S with R := copiedHaloGroupR P N q l s t u band a b L S.R } =
      haloGroupInputBank P N q l s t u band a b L raw borrowed (S.R 93) S.inp S.out := by
  change embStk groupReg
    { { S with R := copiedGroupR P N q l s t u band L S.R } with R :=
      (Function.update (Function.update (copiedGroupR P N q l s t u band L S.R) 111 (List.replicate a tick))
        113 (List.replicate b tick)) } = _
  rw [groupProject_haloEndpoints,copiedGroup_project P N q l s t u band L S raw borrowed hL hR hsrc]
  rfl

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 144 Q A U}

def installHaloGroupHeaders : Pr P₀ 144 Q A U :=
  .seq installGroupHeaders (copyUnaryHeaders 133 [(141,111),(142,113)])

def installHaloGroupHeadersCost (P N q l s t u band a b L : ℕ) : ℕ :=
  installGroupHeadersCost P N q l s t u band L+4*(a+b)+9

theorem installHaloGroupHeaders_exec (P N q l s t u band a b L : ℕ)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hsrc : ∀ r ∈ groupHeaderCopies, (S.R r.1).length = groupHeaderValue P N q l s t u band L r.1)
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (h111 : S.R 111 = []) (h113 : S.R 113 = []) (h133 : S.R 133 = []) :
    ∃ v', v'.user = v.user ∧ Exec body installHaloGroupHeaders (mk v S)
      (installHaloGroupHeadersCost P N q l s t u band a b L)
      (mk v' { S with R := copiedHaloGroupR P N q l s t u band a b L S.R }) := by
  obtain ⟨v₁,hu₁,he₁⟩ := installGroupHeaders_exec (body := body) P N q l s t u band L v S hsrc h133
  let S₁ : Stacks 144 A := { S with R := copiedGroupR P N q l s t u band L S.R }
  let value := fun k : Fin 144 => if k = 141 then a else b
  obtain ⟨v₂,hu₂,he₂⟩ := copyUnaryHeaders_exec (body := body) 133 [(141,111),(142,113)]
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl <;> decide)
    (by intro r hr p hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr hp
        rcases hr with rfl | rfl <;> rcases hp with rfl | rfl <;> decide)
    value v₁ S₁ (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · simpa [S₁,value,copiedGroupR_off] using ha
      · simpa [S₁,value,copiedGroupR_off] using hb)
    (by simpa [S₁,copiedGroupR_off] using h133)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp [installHaloGroupHeadersCost,copyUnaryHeadersCost,value]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp [unaryCopiesR,value,S₁,copiedHaloGroupR,
      copiedGroupR_endpoint P N q l s t u band L S.R 111 (by simp),
      copiedGroupR_endpoint P N q l s t u band L S.R 113 (by simp),h111,h113]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
