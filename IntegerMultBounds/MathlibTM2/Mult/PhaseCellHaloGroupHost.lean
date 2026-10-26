module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloGroupCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOriginPackets
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupHost
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountWords

/-! Execute a clipped length class and publish its binary origins and owned
unary count, preserving the borrowed output suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

/-- Generate origins and count the emitted words before attaching the borrowed suffix. -/
def haloGroupCountedHost : Pr P₀ 117 Q A U :=
  .seq (tblCompile originReg haloGroupCode)
    (.seq (countWords (originReg .wn) (originReg .acc) 116 106 104)
      (moveR (originReg .acc) 109 (fun sym => bitSymbol (pairRe sym))))

theorem haloGroupCountedHost_exec {W V s t band a b L : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hL' : st.val 3 = L)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hcount : st.val 15 = t-s+1) (ha : st.val 13 = a) (hb : st.val 14 = b) (has : a ≤ s) (hbs : b ≤ s)
    (hs : 0 < s) (hst : s < t) (hL : 0 < L)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) (hpacket : s ≤ 2^V) (hw : V ≤ W) (hA : 4 ≤ A)
    (hV : 0 < V) (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (36*(t-s+1)+3)*tblC W V + (haloLengthGroup s t band a b L).length*(8*V+6)+6 ∧
      Exec body haloGroupCountedHost (mk v S) m (mk v' S') ∧
      S'.R 109 = haloOriginPackets A V s t band a b L ++ S.R 109 ∧
      S'.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick ∧
      tblHolds originReg S' (tblRho W (List.replicate W tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^W) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  have hc := haloGroupCode_do (A := A) (W := W) (w := V) st hs' hband hL' hden hone hz hcount ha hb has hbs hs hst hL hwide
  obtain ⟨st', ⟨ha, hb⟩, hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate W tick) (List.replicate V tick) (by simp) (by simp) hw (hc.bounded hbound) hbound
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hh₁, hf₁⟩ := hr v S hS
  have hsym : S₁.R (originReg .acc) = ((haloLengthGroup s t band a b L).flatMap
      (fun phase => tblPairs A V (haloStart s t band a phase) 0)).reverse := by
    rw [hh₁ .acc]
    simpa [tblRho, hacc] using ha
  let words := ((haloLengthGroup s t band a b L).map
    (fun phase => (tblPairs A V (haloStart s t band a phase) 0).reverse)).reverse
  have hwords : words.flatten = S₁.R (originReg .acc) := by
    rw [hsym]
    simp [words, List.flatten_reverse, List.flatMap_def, List.map_map, Function.comp_def]
  have hwordlen : ∀ xs ∈ words, xs.length = V := by
    intro xs hx
    simp only [words, List.mem_reverse, List.mem_map] at hx
    obtain ⟨phase, _, rfl⟩ := hx
    simp [tblPairs]
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) : S₁.R k = S.R k :=
    hf₁.2.2.2 k (fun r he => by have hh := originReg_range r; rw [he] at hh; omega)
  obtain ⟨vc, huc, hec⟩ := countWords_exec (body := body)
    (width := originReg .wn) (src := originReg .acc) (dst := 116) (saved := 106) (tmp := 104)
    (by decide) V hV words hwordlen v₁ S₁
    (by rw [hh₁ .wn]; simp [tblRho]) hwords.symm
    (by rw [hoff 106 (by decide), h106]) (by rw [hoff 104 (by decide), h104])
  let Sc : Stacks 117 A := { S₁ with R := (Function.update S₁.R 116
    (List.replicate (haloLengthGroup s t band a b L).length tick)) }
  have hec' : Exec body (countWords (originReg .wn) (originReg .acc) 116 106 104)
      (mk v₁ S₁) ((haloLengthGroup s t band a b L).length*(6*V+6)+4) (mk vc Sc) := by
    simpa [Sc, words, hoff 116 (by decide), h116] using hec
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (originReg .acc) 109 (by decide)
    (fun sym => bitSymbol (pairRe sym)) vc Sc
  let S₂ : Stacks 117 A := { Sc with R := (movedR Sc.R (originReg .acc) 109
    (fun sym => bitSymbol (pairRe sym)) (Sc.R (originReg .acc))) }
  have h109 : S₁.R 109 = S.R 109 := hf₁.2.2.2 109 (fun r he => by
    have hh := originReg_range r; rw [he] at hh; omega)
  have hlen : (S₁.R (originReg .acc)).length = (haloLengthGroup s t band a b L).length*V := by
    rw [hsym]
    simp [List.length_flatMap, tblPairs]
  refine ⟨v₂, S₂, m₁+((haloLengthGroup s t band a b L).length*(6*V+6)+4)+(2*((haloLengthGroup s t band a b L).length*V)+2), st', hu₂.trans (huc.trans hu₁),
    by nlinarith only [hm₁], (Exec.seq he₁ (Exec.seq hec' he₂)).cast (by simp [Sc, show originReg .acc ≠ (116 : Fin 117) by decide, hlen]; ring) rfl, ?_, ?_, ?_, hb,
    hf₁.1, hf₁.2.1, hf₁.2.2.1, ?_⟩
  · simp [S₂, Sc, movedR, hsym, h109, List.map_reverse, haloOriginPairs_real_bits hA hpacket, show originReg .acc ≠ (116 : Fin 117) by decide]
  · simp [S₂, Sc, movedR, originReg]
  · intro r
    have hout : originReg r ≠ (109 : Fin 117) := by intro he; have hh := originReg_range r; rw [he] at hh; omega
    have h116r : originReg r ≠ (116 : Fin 117) := by
      intro he; have hh := originReg_range r; rw [he] at hh; omega
    simp only [S₂, Sc, movedR, Function.update_apply]
    simp only [ite_eq_right h116r]
    rw [ite_eq_right hout]
    by_cases hracc : r = .acc
    · subst r; simp [tblRho]
    · rw [ite_eq_right (originReg_injective.ne hracc), hh₁ r]
      cases r <;> simp_all [tblRho]
  · intro k hk109 hk116 hk
    have h18 : k ≠ originReg .acc := (hk .acc).symm
    simp [S₂, Sc, movedR, hk109, hk116, h18, hf₁.2.2.2 k hk]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
