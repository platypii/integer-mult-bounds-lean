module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWeightWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightLoad

/-! Generate width, load ordinary geometry once and initialize the retained
weight table. The resulting binary bank is reusable for the entire batch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def sharedWeightInit : Pr P₀ 117 Q A U :=
  .seq generateWeightWidth (.seq initializeCoefficientBank (.seq loadWeightHeaders retainedWeightInit))

def sharedWeightInitCost (P s t u q L w : ℕ) : ℕ :=
  let V := weightWorkspaceWidth P q w t u
  weightWidthCost P q w t u + (292*V+4*w+393) + weightHeadersCost P s t u q L 0 V +
    (158*P+8*q+424)*tblC V w

theorem sharedWeightInit_exec (P s t u q L w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hw : (S.R 94).length = w)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(104 : Fin 117), 106, 111, 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hL : L ≤ s) :
    let V := weightWorkspaceWidth P q w t u
    ∃ v' S' m st', v'.user = v.user ∧ m ≤ sharedWeightInitCost P s t u q L w ∧
      Exec body sharedWeightInit (mk v S) m (mk v' S') ∧
      WeightReady A V P q s t u L st' ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate w tick) st') ∧
      S'.R 115 = List.replicate V tick ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k.val ≥ 63 → k ≠ 115 → S'.R k = S.R k := by
  let V := weightWorkspaceWidth P q w t u
  have hlow (k : Fin 117) (hk : k.val < 63) : S.R k = [] := by
    obtain ⟨r, rfl⟩ := coefficientReg_covers k hk
    exact hblank r
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateWeightWidth_exec (body := body) P q w t u v S
    hP' hq hw ht' hu' (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hlow _ (by decide) | exact hfresh _ (by simp))
  let Sw : Stacks 117 A := { S with R := Function.update S.R 115 (List.replicate V tick) }
  obtain ⟨v₂, hu₂, he₂, hh₂⟩ := initializeCoefficientBank_exec (body := body) V w v₁ Sw
    (by simp [Sw]) (by simpa [Sw] using hw) (by simpa [Sw] using hfresh 106 (by simp)) (by
      intro r
      have hn : coefficientReg r ≠ (115 : Fin 117) := by
        intro he; have hr := coefficientReg_range r; rw [he] at hr; omega
      simpa [Sw, hn] using hblank r)
  let S₂ : Stacks 117 A := { Sw with R := chirpBankLoadR coefficientReg (fun _ => 106) V w (fun _ => 0) Sw.R }
  have hoff₂ (k : Fin 117) (hk : 63 ≤ k.val) : S₂.R k = Sw.R k := by
    apply chirpBankLoad_off
    intro r he
    have hr := coefficientReg_range r
    rw [he] at hk
    omega
  obtain ⟨v₃, S₃, m₃, hu₃, hm₃, he₃, hh₃, hf₃⟩ := loadWeightHeaders_exec (body := body)
    P s t u q L 0 V w v₂ S₂
    (by rw [hoff₂ 114 (by decide)]; simpa [Sw] using hP')
    (by rw [hoff₂ 97 (by decide)]; simpa [Sw] using hs')
    (by rw [hoff₂ 98 (by decide)]; simpa [Sw] using ht')
    (by rw [hoff₂ 99 (by decide)]; simpa [Sw] using hu')
    (by rw [hoff₂ 112 (by decide)]; simpa [Sw] using hq)
    (by rw [hoff₂ 111 (by decide)]; simp [Sw, hfresh 111 (by simp)])
    (by rw [hoff₂ 102 (by decide)]; simpa [Sw] using hL') hh₂
  have hoff₃ (k : Fin 117) (hk : 63 ≤ k.val) : S₃.R k = Sw.R k := by
    rw [hf₃.2.2.2 k (fun r he => by have hr := coefficientReg_range r; rw [he] at hr; omega)]
    exact hoff₂ k hk
  obtain ⟨v₄, S₄, m₄, st₄, hu₄, hm₄, he₄, hr₄, hh₄, hf₄⟩ := retainedWeightInit_exec (body := body)
    (weightHeaderState (A := A) P s t u q L 0) (by simp [weightHeaderState]) (by simp [weightHeaderState])
    (by simp [weightHeaderState]) (by simp [weightHeaderState]) (by simp [weightHeaderState])
    (by simp [weightHeaderState]) hP hs hst hu hL rfl (weightHeaderState_fits hP hs hst hu hs hL)
    rfl v₃ S₃ hh₃
  have hoff₄ (k : Fin 117) (hk : 63 ≤ k.val) : S₄.R k = Sw.R k := by
    rw [hf₄.2.2.2 k (fun r he => by have hr := coefficientReg_range r; rw [he] at hr; omega)]
    exact hoff₃ k hk
  refine ⟨v₄, S₄, m₁+((292*V+4*w+393)+(m₃+m₄)), st₄,
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)),
    hr₄, hh₄, ?_, hf₄.1.trans hf₃.1, hf₄.2.1.trans hf₃.2.1, hf₄.2.2.1.trans hf₃.2.2.1, ?_⟩
  · dsimp only [sharedWeightInitCost]
    dsimp only [V] at *
    omega
  · rw [hoff₄ 115 (by decide)]; simp [Sw, V]
  · intro k hk hk115
    rw [hoff₄ k hk]
    simp [Sw, hk115]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
