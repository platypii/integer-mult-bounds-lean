module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthCandidatesCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloDescriptorController
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthCandidatesHost

/-! Execute the six halo length candidates and publish their binary words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloLengthCandidatePackets (A V s t band a b : ℕ) : List (Fin (A+4)) :=
  (haloLengthCandidates s t band a b).flatMap (binSyms V)

@[simp] theorem haloLengthCandidatePackets_length (A V s t band a b : ℕ) :
    (haloLengthCandidatePackets A V s t band a b).length = 6*V := by
  simp [haloLengthCandidatePackets, haloLengthCandidates, naturalLengthCandidates, binSyms]
  omega

theorem haloLengthCandidatePairs_bits {A V s t band a b : ℕ} (hst : s < t) (hA : 4 ≤ A)
    (hwidth : s+1 < 2^V) :
    ((haloLengthCandidates s t band a b).flatMap (fun L => tblPairs A V L 0)).map
      (fun sym => bitSymbol (pairRe sym)) = haloLengthCandidatePackets A V s t band a b := by
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro L hL
  exact tblPairs_real_bits hA (((haloLengthCandidates_uniform hst band a b hL).trans ((Nat.sub_le _ _).trans (Nat.add_le_add_right (Nat.div_le_self _ _) 1))).trans_lt hwidth)

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def haloLengthCandidatesController : Pr P 117 Q A U :=
  .seq (tblCompile originReg (originInitCode ;; haloLengthCandidatesCode))
    (moveR (originReg .acc) 87 (fun sym => bitSymbol (pairRe sym)))

theorem haloLengthCandidatesController_exec {V s t band a b : ℕ}
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick)
      (haloRawState A s t band a b))) :
    ∃ v' S' n, ∃ st' : TblSt 16 A, v'.user = v.user ∧ n ≤ 139*tblC V V+12*V+2 ∧
      Exec body haloLengthCandidatesController (mk v S) n (mk v' S') ∧
      S'.R 87 = haloLengthCandidatePackets A V s t band a b ++ S.R 87 ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ i, st'.val i < 2^V) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 87 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  have hinit := haloInitCode_do (A := A) (W := V) (w := V) (a := a) (b := b) hs hst hwide
  have hscan := haloLengthCandidatesCode_do (W := V) (w := V) (haloReadyState A s t band a b)
      (by simp [haloReadyState, haloRawState]) (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState]) (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState]) (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState]) (by simp [haloReadyState, haloRawState])
      has hbs hband hs hst hwide
  have hc : TblDo A V V (originInitCode ;; haloLengthCandidatesCode)
      (haloRawState A s t band a b) (fun st' => st'.acc =
        ((haloLengthCandidates s t band a b).flatMap (fun L => tblPairs A V L 0)).reverse) 139 :=
    hinit.seq (K₂ := 133) (fun st he => by
      subst he
      exact hscan.mono (fun st' hh => by simpa [haloReadyState, haloRawState] using hh) le_rfl)
  have hb := haloRawState_bounded (A := A) has hbs hst hband hwide
  obtain ⟨st', ⟨ha, hb'⟩, hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl (hc.bounded hb) hb
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hh₁, hf₁⟩ := hr v S hS
  have hsym : S₁.R (originReg .acc) =
      ((haloLengthCandidates s t band a b).flatMap (fun L => tblPairs A V L 0)).reverse := by
    rw [hh₁ .acc]
    simpa [tblRho, haloReadyState, haloRawState] using ha
  have h87 : S₁.R 87 = S.R 87 := hf₁.2.2.2 87 (fun r he => by
    have hh := originReg_range r; rw [he] at hh; omega)
  have hlen : (S₁.R (originReg .acc)).length = 6*V := by
    rw [hsym]
    simp [haloLengthCandidates, naturalLengthCandidates, tblPairs]
    omega
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (originReg .acc) 87 (by decide)
    (fun sym => bitSymbol (pairRe sym)) v₁ S₁
  let S₂ : Stacks 117 A := { S₁ with R := (movedR S₁.R (originReg .acc) 87
    (fun sym => bitSymbol (pairRe sym)) (S₁.R (originReg .acc))) }
  refine ⟨v₂, S₂, n₁+(2*(6*V)+2), st', hu₂.trans hu₁, by omega,
    (Exec.seq he₁ he₂).cast (by rw [hlen]) rfl, ?_, ?_, hb', hf₁.1, hf₁.2.1, hf₁.2.2.1, ?_⟩
  · have hwidth : s+1 < 2^V := by nlinarith only [hwide, hst]
    simp [S₂, movedR, hsym, h87, List.map_reverse, haloLengthCandidatePairs_bits hst hA hwidth]
  · intro r
    have h87r : originReg r ≠ (87 : Fin 117) := by intro he; have hh := originReg_range r; rw [he] at hh; omega
    simp only [S₂, movedR, Function.update_apply]
    rw [ite_eq_right h87r]
    by_cases hracc : r = .acc
    · subst r; simp [tblRho]
    · rw [ite_eq_right (originReg_injective.ne hracc), hh₁ r]
      cases r <;> simp_all [tblRho]
  · intro k hk87 hk
    have hacc : k ≠ originReg .acc := (hk .acc).symm
    simp [S₂, movedR, hk87, hacc, hf₁.2.2.2 k hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
