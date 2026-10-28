module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinalRoundFits

/-! Normalize the actual solver output tape, independently of its numerator witness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem finalRound_tape_exec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src,dst,tmp,cW,cS,cE,cD,sp,sg,cy].Nodup)
    (w q p j E k : ℕ) (hp : p ≤ q) (hw : q+E+5 ≤ w)
    (hk : p+E+5 ≤ k) (hsize : q-p+j+k ≤ w)
    (G : ZMod s → GaussianInt)
    (hG : ∀ i : ZMod s, ‖pairedCellRead q w (cstream A w (chirpLine s G)) i‖ ≤ 8*(2 : ℝ)^E)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (chirpLine s G)) (hdst : S.R dst = [])
    (hg : topShiftG tmp cW cS cE cD sp sg cy w (q-p+j) k S.R) :
    ∃ v', ∃ H : ZMod s → GaussianInt, v'.user = v.user ∧
      Exec body (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy))
        (mk v S) (1+(s*(topShiftWordCost w (q-p+j) k+1)+1)+(2*(s*k)+2))
        (mk v' {S with R := (Function.update S.R src (cstream A k (chirpLine s H)))}) ∧
      ∀ i : ZMod s, pairedCellRead p k (cstream A k (chirpLine s H)) i =
        rhoC p (((2 : ℂ)^j)⁻¹*pairedCellRead q w (cstream A w (chirpLine s G)) i) := by
  have hread (i : ZMod s) : pairedCellRead q w (cstream A w (chirpLine s G)) i =
      value q (symZ w (G i)) := by
    simpa only [List.append_nil] using pairedCellRead_signed (q := q) hA (show 1 ≤ w by omega) G [] i
  have hbound : ∀ i : ZMod s, ‖value q (symZ w (G i))‖ ≤ 8*(2 : ℝ)^E := by
    intro i
    rw [←hread i]
    exact hG i
  have hsource : S.R src = cstream A w (chirpLine s (fun i => symZ w (G i))) :=
    hsrc.trans (chirpLine_symZ A w s G).symm
  obtain ⟨v',hu,he,hd⟩ := finalRound_field_exec (body := body) hA hreg w q p j E k hp hw hk hsize
    (fun i => symZ w (G i)) hbound v S hsource hdst hg
  refine ⟨v',fun i => tdivN (q-p+j) (symZ w (G i)),hu,he,?_⟩
  intro i
  rw [hread i]
  exact hd i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
