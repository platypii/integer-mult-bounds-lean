module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloDescriptorCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloDescriptorPackets
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupHost
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountWords

/-! Execute the clipped phase scan and publish exact binary origin/length
descriptors, preserving the borrowed output suffix and all external stacks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloDescriptorHost : Pr P₀ 117 Q A U :=
  .seq (tblCompile originReg haloDescriptorCode) (moveR (originReg .acc) 109 (fun sym => bitSymbol (pairRe sym)))

theorem haloDescriptorHost_exec {W V s t band a b : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hcount : st.val 15 = t-s+1) (ha : st.val 13 = a) (hb : st.val 14 = b) (has : a ≤ s) (hbs : b ≤ s)
    (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) (hpacket : s < 2^V) (hw : V ≤ W) (hA : 4 ≤ A)
    (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st)) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (36*(t-s+1)+3)*tblC W V + 2*((haloCellPhases s t band a b).length*(2*V))+2 ∧
      Exec body haloDescriptorHost (mk v S) m (mk v' S') ∧
      S'.R 109 = haloDescriptorPackets A V s t band a b ++ S.R 109 ∧
      tblHolds originReg S' (tblRho W (List.replicate W tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^W) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  have hc := haloDescriptorCode_do (A := A) (W := W) (w := V) st hs' hband hden hone hz hcount ha hb has hbs hs hst hwide
  obtain ⟨st', ⟨ha, hb⟩, hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate W tick) (List.replicate V tick) (by simp) (by simp) hw (hc.bounded hbound) hbound
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hh₁, hf₁⟩ := hr v S hS
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (originReg .acc) 109 (by decide)
    (fun sym => bitSymbol (pairRe sym)) v₁ S₁
  let S₂ : Stacks 117 A := { S₁ with R := (movedR S₁.R (originReg .acc) 109
    (fun sym => bitSymbol (pairRe sym)) (S₁.R (originReg .acc))) }
  have hsym : S₁.R (originReg .acc) = ((haloCellPhases s t band a b).flatMap
      (fun phase => tblPairs A V (haloStart s t band a phase) 0 ++
        tblPairs A V (haloLength s t band a b phase) 0)).reverse := by
    rw [hh₁ .acc]
    simpa [tblRho, hacc] using ha
  have h109 : S₁.R 109 = S.R 109 := hf₁.2.2.2 109 (fun r he => by
    have hh := originReg_range r; rw [he] at hh; omega)
  have hlen : (S₁.R (originReg .acc)).length = (haloCellPhases s t band a b).length*(2*V) := by
    rw [hsym]
    simp [List.length_flatMap, tblPairs, Nat.two_mul]
  refine ⟨v₂, S₂, m₁+(2*((haloCellPhases s t band a b).length*(2*V))+2), st', hu₂.trans hu₁,
    by omega, (Exec.seq he₁ he₂).cast (by rw [hlen]) rfl, ?_, ?_, hb,
    hf₁.1, hf₁.2.1, hf₁.2.2.1, ?_⟩
  · simp [S₂, movedR, hsym, h109, List.map_reverse, haloDescriptorPairs_real_bits hA hpacket]
  · intro r
    have hout : originReg r ≠ (109 : Fin 117) := by intro he; have hh := originReg_range r; rw [he] at hh; omega
    simp only [S₂, movedR, Function.update_apply]
    rw [ite_eq_right hout]
    by_cases hracc : r = .acc
    · subst r; simp [tblRho]
    · rw [ite_eq_right (originReg_injective.ne hracc), hh₁ r]
      cases r <;> simp_all [tblRho]
  · intro k hk109 hk
    have h18 : k ≠ originReg .acc := (hk .acc).symm
    simp [S₂, movedR, hk109, h18, hf₁.2.2.2 k hk]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
