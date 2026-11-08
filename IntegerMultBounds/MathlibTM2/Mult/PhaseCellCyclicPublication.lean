module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishArchivedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPublicationField

/-! Consume both archived interiors and emit one real cyclic recovery stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def cyclicPublication : Pr P 148 Q A U :=
  .seq (publishArchivedInterior 138 146) (publishArchivedInterior 144 145)

def cyclicPublicationCost (P q s t u band a n : ℕ) : ℕ :=
  publishArchivedInteriorCost P q s t u band 0 (n-min n (s-a))+
    publishArchivedInteriorCost P q s t u band a (a+min n (s-a))

theorem cyclicPublication_exec {P₀ N q l s t u band a n : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (ha : a < s) (hn : n ≤ s) (hband : band ≤ s)
    (D E Y : ZMod s → GaussianInt) (tail archiveTail input : List (Fin (A+4)))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P₀ N q l s t u band 0 0 input (embStk componentReg S))
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ ([(138 : Fin 148),141,142,143]), S.R k = [])
    (harchive : S.R 147 = cstream A (2*q+8) (chirpLine s E)++
      (cstream A (2*q+8) (chirpLine s D)++archiveTail))
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s Y)++tail) :
    let F : Stacks 148 A := {S with R := (Function.update (Function.update S.R 147 archiveTail) 132
      (cstream A (2*q+8) (chirpLine s (cyclicPublicationField t band a n D E Y))++tail))}
    ∃ v' m, v'.user = v.user ∧ m ≤ cyclicPublicationCost P₀ q s t u band a n ∧
      Exec (embTab componentReg (embTab groupReg body)) cyclicPublication (mk v S) m (mk v' F) ∧
      LengthKeyReady P₀ N q l s t u band 0 0 input (embStk componentReg F) := by
  dsimp only
  let right := fun i => realPartWord (publicationField t band 0 (n-min n (s-a)) E Y i)
  let leftWords := cstream A (2*q+8) (chirpLine s D)
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁,hready₁⟩ := publishArchivedInterior_exec (body := body)
    (a := 0) (b := n-min n (s-a)) 138 146 (by decide) (by decide) (by decide)
    hA hst (by omega) (by omega) hband E Y tail (leftWords++archiveTail) input v S hready
    (by simp [hfresh 138 (by simp)]) hrightEnd (hfresh 141 (by simp)) (hfresh 142 (by simp))
    (hfresh 143 (by simp)) harchive hsource
  let S₁ : Stacks 148 A := {S with R := (Function.update (Function.update S.R 147 (leftWords++archiveTail)) 132
    (cstream A (2*q+8) (chirpLine s right)++tail))}
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂,hready₂⟩ := publishArchivedInterior_exec (body := body)
    (a := a) (b := a+min n (s-a)) 144 145 (by decide) (by decide) (by decide)
    hA hst ha.le (by omega) hband D right tail archiveTail input v₁ S₁ hready₁
    (by simpa [S₁] using haSrc) (by simpa [S₁] using hleftEnd)
    (by simpa [S₁] using hfresh 141 (by simp)) (by simpa [S₁] using hfresh 142 (by simp))
    (by simpa [S₁] using hfresh 143 (by simp)) (by simp [S₁,leftWords]) (by simp [S₁])
  have hG : (fun i => realPartWord (publicationField t band a (a+min n (s-a)) D right i)) =
      cyclicPublicationField t band a n D E Y := by funext i; rfl
  have hfinal : {S₁ with R := (Function.update (Function.update S₁.R 147 archiveTail) 132
      (cstream A (2*q+8) (chirpLine s (fun i => realPartWord (publicationField t band a (a+min n (s-a)) D right i)))++tail))} =
      {S with R := (Function.update (Function.update S.R 147 archiveTail) 132
        (cstream A (2*q+8) (chirpLine s (cyclicPublicationField t band a n D E Y))++tail))} := by
    rw [hG]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h132 : k = 132 <;> by_cases h147 : k = 147 <;>
      simp [S₁,h132,h147]
  refine ⟨v₂,m₁+m₂,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,
    (Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) hfinal),?_⟩
  rw [← hfinal]
  exact hready₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
