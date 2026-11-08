module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithWindow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedHalo
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Reuse generated halo publication with borrowed retained endpoint rulers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def windowedPublication (lower upper : Fin 148) : Pr P 148 Q A U :=
  withWindow lower upper (embProg componentReg id publishHalo)

theorem windowedPublication_exec {P₀ N q l s t u band a b : ℕ} [NeZero s]
    (lower upper : Fin 148) (hports : [lower,upper,141,142,143].Nodup)
    (hA : 4 ≤ A) (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hband : band ≤ s)
    (D C : ZMod s → GaussianInt) (tail input : List (Fin (A+4)))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P₀ N q l s t u band 0 0 input (embStk componentReg S))
    (ha : (S.R lower).length = a) (hb : (S.R upper).length = b)
    (h141 : S.R 141 = []) (h142 : S.R 142 = []) (h143 : S.R 143 = [])
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++
      (cstream A (2*q+8) (chirpLine s C)++tail)) :
    let G := fun i => realPartWord (publicationField t band a b D C i)
    ∃ v' m, v'.user = v.user ∧
      m ≤ (4*a+4)+((4*b+4)+(publishHaloCost P₀ q s t u band a b+(2*(a+b)+5))) ∧
      Exec (embTab componentReg (embTab groupReg body)) (windowedPublication lower upper) (mk v S) m
        (mk v' {S with R := Function.update S.R 132 (cstream A (2*q+8) (chirpLine s G)++tail)}) := by
  dsimp only
  apply withWindow_exec lower upper hports _ a b _ _ v S ha hb h141 h142 h143
  intro vi
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 141 (List.replicate a tick)}
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 142 (List.replicate b tick)}
  have hready₂ : LengthKeyReady P₀ N q l s t u band 0 0 input (embStk componentReg S₂) := by
    have hproj142 := componentProject_updateR_inner S₁ (142 : Fin 144) (List.replicate b tick)
    have hc142 : componentReg (142 : Fin 144) = (142 : Fin 148) := by decide
    rw [hc142] at hproj142
    have hproj141 := componentProject_updateR_inner S (141 : Fin 144) (List.replicate a tick)
    have hc141 : componentReg (141 : Fin 144) = (141 : Fin 148) := by decide
    rw [hc141] at hproj141
    dsimp only [S₂]
    rw [hproj142]
    dsimp only [S₁]
    rw [hproj141]
    exact (hready.update_window 141 (Or.inl rfl) _).update_window 142 (Or.inr rfl) _
  obtain ⟨vn,m,hvn,hm,hen,hready'⟩ := publishHalo_exec (body := body)
    hA hst has hbs hband D C tail input (embDn componentReg vi) (embStk componentReg S₂)
    hready₂ (by simp [embStk,componentReg,S₂,S₁]) (by simp [embStk,componentReg,S₂])
    (by simpa [embStk,componentReg,S₂,S₁] using h143)
    (by simpa [embStk,componentReg,S₂,S₁] using hsource)
  obtain ⟨vf,hvf,huf,hef⟩ := exec_emb_ovr (e := componentReg) (ι := id)
    (body' := embTab componentReg (embTab groupReg body)) componentReg_injective (fun p => rfl)
    hen vi rfl S₂ rfl
  refine ⟨vf,m,huf.trans hvn,hm,hef.cast rfl ?_⟩
  apply congrArg (mk vf)
  rw [embOvr_updR componentReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
