module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassControllerStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginLoadStock
public import IntegerMultBounds.MathlibTM2.Host.ClearBankExcept

/-! Loaded halo headers, one enumeration reserve, and allocation-free retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def preparedHaloClassWorkspace (V s t band a b L : ℕ) : ℕ :=
  3*(104*V+137)+(3*haloClassHeadersCost s t band a b L V+
    haloClassControllerWorkspace V (IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloLengthGroup s t band a b L).length)

theorem preparedHaloClass_width_exec_within (V s t band a b L : ℕ)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hV : (S.R 115).length = V) (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedHaloClassCost s t band a b L (V) ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          preparedHaloClassWorkspace V s t band a b L)
        depth preparedHaloClass (mk v S) n (mk v' S')) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update (Function.update S.R 109 (haloOriginPackets A (V) s t band a b L ++ S.R 109))
        116 (List.replicate (haloLengthGroup s t band a b L).length tick) := by
  obtain ⟨v₁, hu₁, he₁, hh₁⟩ := initializeOriginBank_exec (body := body) V v S hV h106
    (fun r => hblank _ (originReg_range r))
  let S₁ : Stacks 117 A := { S with R := chirpBankLoadR originReg (fun _ => 106) V V (fun _ => 0) S.R }
  have hoff₁ (k : Fin 117) (hk : 31 ≤ k.val) : S₁.R k = S.R k := by
    apply chirpBankLoad_off
    intro r he
    have hr := originReg_range r
    rw [he] at hk
    omega
  have hhigh (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he
    have hr := originReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hh₂, hf₂⟩ := loadHaloClassHeaders_exec (body := body) s t band a b L V v₁ S₁
    (by rw [hoff₁ 97 (by decide)]; exact hsSrc) (by rw [hoff₁ 98 (by decide)]; exact htSrc)
    (by rw [hoff₁ 100 (by decide)]; exact hbSrc)
    (by rw [hoff₁ 111 (by decide)]; exact haSrc) (by rw [hoff₁ 113 (by decide)]; exact hbEndSrc)
    (by rw [hoff₁ 102 (by decide)]; exact hLSrc) hh₁
  have hoff₂ (k : Fin 117) (hk : 31 ≤ k.val) : S₂.R k = S.R k :=
    (hf₂.2.2.2 k (hhigh k hk)).trans (hoff₁ k hk)
  obtain ⟨v₃, S₃, n₃, st₃, hu₃, hn₃, he₃, hout₃, hcount₃, hh₃, hb₃, hi₃, ho₃, hl₃, hf₃⟩ :=
    haloClassController_exec_within (body := body) hs hst hband has hbs hL hLs hwide hA v₂ S₂ hh₂
      (by rw [hoff₂ 104 (by decide)]; exact h104)
      (by rw [hoff₂ 106 (by decide)]; exact h106)
      (by rw [hoff₂ 116 (by decide)]; exact h116)
  obtain ⟨v₄, n₄, hu₄, hn₄, he₄⟩ := releaseOriginBank_exec (body := body) V st₃.val v₃ S₃ hh₃
  let S₄ : Stacks 117 A := { S₃ with R := fun k => if k.val < 31 then [] else S₃.R k }
  have hoff₃ (k : Fin 117) (hk : 31 ≤ k.val) (hk109 : k ≠ 109) (hk116 : k ≠ 116) : S₃.R k = S.R k :=
    (hf₃ k hk109 hk116 (hhigh k hk)).trans (hoff₂ k hk)
  refine ⟨v₄, S₄, (104*V+137)+(n₂+(n₃+n₄)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    ?_, hi₃.trans hf₂.1,
    ho₃.trans hf₂.2.1, hl₃.trans hf₂.2.2.1, ?_⟩
  · unfold preparedHaloClassCost
    omega
  · intro depth
    have ht₁ := mn_native_exec_within he₁ 3 (chirpBankLoad_native _ _ _ _) depth _ (Nat.le_refl _)
    have ht₂ := mn_native_exec_within he₂ 3 (loadOriginList_native _) depth
      (mnSize (mk v₁ S₁)+depth+3*haloClassHeadersCost s t band a b L V) (by omega)
    have ht₄ := mn_native_exec_within he₄ 0 (clearWords_native_zero _) depth _ (Nat.le_refl _)
    exact (mn_seq_within_add ht₁ (mn_seq_within_add ht₂ (mn_seq_within_add (he₃ depth) ht₄))).mono (by
      intro d z hz
      unfold preparedHaloClassWorkspace
      omega)
  · funext k
    by_cases hk109 : k = 109
    · subst k; simpa [S₄, hoff₂ 109 (by decide)] using hout₃
    by_cases hk116 : k = 116
    · subst k; simpa [S₄] using hcount₃
    by_cases hk : k.val < 31
    · simp [S₄, hk, hk109, hblank k hk,hk116]
    simp [S₄, hk, hk109,hk116, hoff₃ k (by omega) hk109 hk116]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
