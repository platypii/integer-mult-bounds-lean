module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthCandidatesCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginController

/-! Execute the fixed four-candidate discovery program and emit its binary
packet stream. No target row length or phase count is an input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def naturalLengthCandidatePackets (A V s t band : ℕ) : List (Fin (A+4)) :=
  (naturalLengthCandidates s t band).flatMap (binSyms V)

@[simp] theorem naturalLengthCandidatePackets_length (A V s t band : ℕ) :
    (naturalLengthCandidatePackets A V s t band).length = 4*V := by
  simp [naturalLengthCandidatePackets, naturalLengthCandidates, binSyms]
  omega

theorem naturalLengthCandidatePairs_bits {A V s t band : ℕ} (hst : s < t) (hA : 4 ≤ A)
    (hwidth : s+1 < 2^V) :
    ((naturalLengthCandidates s t band).flatMap (fun L => tblPairs A V L 0)).map
      (fun sym => bitSymbol (pairRe sym)) = naturalLengthCandidatePackets A V s t band := by
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro L hL
  exact tblPairs_real_bits hA ((naturalLengthCandidates_le hst band hL).trans_lt hwidth)

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def lengthCandidatesController : Pr P 117 Q A U :=
  .seq (tblCompile originReg (originInitCode ;; naturalLengthCandidatesCode))
    (moveR (originReg .acc) 87 (fun sym => bitSymbol (pairRe sym)))

theorem lengthCandidatesController_exec {V s t band : ℕ}
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hA : 4 ≤ A)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick)
      (originRawState A s t band 0))) :
    ∃ v' S' n, ∃ st' : TblSt 16 A, v'.user = v.user ∧ n ≤ 60*tblC V V+8*V+2 ∧
      Exec body lengthCandidatesController (mk v S) n (mk v' S') ∧
      S'.R 87 = naturalLengthCandidatePackets A V s t band ++ S.R 87 ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ i, st'.val i < 2^V) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 87 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  have hinit := originInitCode_do (A := A) (W := V) (w := V) (L := 0) hs hst hwide
  have hscan := naturalLengthCandidatesCode_do (W := V) (e := V) (originReadyState A s t band 0)
      (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState])
      (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState])
      (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState])
      (by simp [originReadyState, originRawState]) hs hst hwide
  have hc : TblDo A V V (originInitCode ;; naturalLengthCandidatesCode)
      (originRawState A s t band 0) (fun st' => st'.acc =
        ((naturalLengthCandidates s t band).flatMap (fun L => tblPairs A V L 0)).reverse) 60 :=
    hinit.seq (K₂ := 54) (fun st he => by
      subst he
      exact hscan.mono (fun st' hh => by simpa [originReadyState, originRawState] using hh) le_rfl)
  have hb := originRawState_bounded (A := A) (L := 0) (by omega) hst hband hwide
  obtain ⟨st', ⟨ha, hb'⟩, hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl (hc.bounded hb) hb
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hh₁, hf₁⟩ := hr v S hS
  have hsym : S₁.R (originReg .acc) =
      ((naturalLengthCandidates s t band).flatMap (fun L => tblPairs A V L 0)).reverse := by
    rw [hh₁ .acc]
    simpa [tblRho, originReadyState, originRawState] using ha
  have h87 : S₁.R 87 = S.R 87 := hf₁.2.2.2 87 (fun r he => by
    have hh := originReg_range r; rw [he] at hh; omega)
  have hlen : (S₁.R (originReg .acc)).length = 4*V := by
    rw [hsym]
    simp [naturalLengthCandidates, tblPairs]
    omega
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (originReg .acc) 87 (by decide)
    (fun sym => bitSymbol (pairRe sym)) v₁ S₁
  let S₂ : Stacks 117 A := { S₁ with R := (movedR S₁.R (originReg .acc) 87
    (fun sym => bitSymbol (pairRe sym)) (S₁.R (originReg .acc))) }
  refine ⟨v₂, S₂, n₁+(2*(4*V)+2), st', hu₂.trans hu₁, by omega,
    (Exec.seq he₁ he₂).cast (by rw [hlen]) rfl, ?_, ?_, hb', hf₁.1, hf₁.2.1, hf₁.2.2.1, ?_⟩
  · have hwidth : s+1 < 2^V := by nlinarith only [hwide, hst]
    simp [S₂, movedR, hsym, h87, List.map_reverse, naturalLengthCandidatePairs_bits hst hA hwidth]
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
