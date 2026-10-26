module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationMaskHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWidth

/-! Generate the full publication mask and its workspace from ordinary headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def closedPublicationMask : Pr P₀ 117 Q A U :=
  .seq generatePublicationWidth (.seq publicationMaskFromHeaders (uclear 115))

def closedPublicationMaskCost (s t band a b : ℕ) : ℕ :=
  let V := publicationGeometryWidth t band
  generatePublicationWidthCost t band+publicationMaskFromHeadersCost V s t band a b+2*V+2

theorem closedPublicationMaskCost_le (s t band a b : ℕ) :
    closedPublicationMaskCost s t band a b ≤
      4000*(s+t+band+a+b+1)*(publicationGeometryWidth t band+4)^2 := by
  let V := publicationGeometryWidth t band
  change generatePublicationWidthCost t band+publicationMaskFromHeadersCost V s t band a b+2*V+2 ≤
    4000*(s+t+band+a+b+1)*(V+4)^2
  simp only [generatePublicationWidthCost,publicationMaskFromHeadersCost,publicationMaskHostCost,
    IntegerMultBounds.MathlibTM2.Fast.TableVM.tblC]
  nlinarith [Nat.zero_le (s*V^2), Nat.zero_le (t*V^2),
    Nat.zero_le (band*V^2), Nat.zero_le (a*V^2), Nat.zero_le (b*V^2),
    Nat.zero_le (s*V), Nat.zero_le (t*V), Nat.zero_le (band*V),
    Nat.zero_le (a*V), Nat.zero_le (b*V)]

theorem closedPublicationMaskCost_halo_le {s t band a b : ℕ}
    (hst : s ≤ t) (hband : band ≤ s) (ha : a ≤ s) (hb : b ≤ s) :
    closedPublicationMaskCost s t band a b ≤ 4000*(5*t+1)*(4*Nat.size t+11)^2 := by
  have hsize : Nat.size band ≤ Nat.size t := Nat.size_le_size (hband.trans hst)
  have hwidth : publicationGeometryWidth t band+4 ≤ 4*Nat.size t+11 := by
    dsimp [publicationGeometryWidth]
    omega
  have hcount : s+t+band+a+b+1 ≤ 5*t+1 := by omega
  exact (closedPublicationMaskCost_le s t band a b).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 4000 hcount) (Nat.pow_le_pow_left hwidth 2))

theorem closedPublicationMask_exec {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band)
    (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h115 : S.R 115 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ closedPublicationMaskCost s t band a b ∧
      Exec body closedPublicationMask (mk v S) n
        (mk v' {S with R := Function.update S.R 109 (publicationMaskSymbols A s t band a b++S.R 109)}) := by
  let V := publicationGeometryWidth t band
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatePublicationWidth_exec (body := body)
    t band v S ht hband h115 (by
      intro k hk
      have hk31 : k.val < 31 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
      exact hblank k hk31)
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate V tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := publicationMaskFromHeaders_exec (body := body)
    (V := V) (s := s) (t := t) (band := band) (a := a) (b := b) hst haS hbS hbandS
    (publicationGeometryWidth_fits t band) v₁ S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using ht) (by simpa [S₁] using hband)
    (by simpa [S₁] using ha) (by simpa [S₁] using hb) (by simpa [S₁] using h108)
    (by simp [S₁]) (by simpa [S₁] using h106)
    (by intro k hk
        have hne : k ≠ 115 := by intro he; subst k; norm_num at hk
        simpa [S₁,hne] using hblank k hk)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 109 (publicationMaskSymbols A s t band a b++S₁.R 109)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 115 v₂ S₂
  refine ⟨v₃,n₁+(n₂+(2*V+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · change n₁+(n₂+(2*V+2)) ≤ generatePublicationWidthCost t band+
      publicationMaskFromHeadersCost V s t band a b+2*V+2
    omega
  · simp [S₂,S₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk115 : k = 115 <;> by_cases hk109 : k = 109 <;>
      simp [S₂,S₁,hk115,hk109,h115]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
