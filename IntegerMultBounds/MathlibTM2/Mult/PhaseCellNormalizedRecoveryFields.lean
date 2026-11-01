module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryJobBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyFieldsInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExpandComplexFields

/-! The cached recovery jobs use exactly the normalized fields produced by the
existing packed input machine. Component expansion retains its established order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 276 Q A U}

def recoveryInputFields (p q : ℕ) (Fs : List (ZMod s → GaussianInt)) : List (ZMod s → GaussianInt) :=
  Fs.map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)

@[simp] theorem recoveryInputFields_length (p q : ℕ) (Fs : List (ZMod s → GaussianInt)) :
    (recoveryInputFields p q Fs).length = Fs.length := List.length_map _

theorem recoveryInputFields_bound (p q rhsExp : ℕ) (hpq : p+1 ≤ q)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    ∀ F ∈ recoveryInputFields p q Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^rhsExp := by
  intro F hmem i
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hmem
  exact packedBatch_shift_bound p q rhsExp hpq Fs hF G hG i

/-- The shifted flat input page is exactly the ordinary recovery job's field archive. -/
theorem recoveryInputFields_packet (p q a L : ℕ) (Fs : List (ZMod s → GaussianInt)) :
    ((Fs.map (packedInterval a L)).flatten).map (fun z => (2 : GaussianInt)^(q-p-1)*z) =
      ((recoveryInputFields p q Fs).map (packedInterval a L)).flatten := by
  rw [packedBatch_map]
  simp only [recoveryInputFields,List.map_map,Function.comp_def]

namespace GeneratedRecoveryJob
variable {p u l target rhsExp t a b V : ℕ} {α gap : ℝ} {C : ZMod s → GaussianInt}

noncomputable def ofNormalizedBounds
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    GeneratedRecoveryJob s := by
  let q := packedHaloPrecision p l s t u target rhsExp a b
  have hpq : p+1 ≤ q := by
    dsimp [q,packedHaloPrecision,executionPrecision,executionExponent,inputExponent,sourceExponent]
    omega
  exact ofBounds h (recoveryInputFields p q Fs) (recoveryInputFields_bound p q rhsExp hpq Fs hF)

theorem ofNormalizedBounds_fields
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    let r := ofNormalizedBounds h Fs hF
    r.problem.Fs = recoveryInputFields p r.problem.precision Fs ∧ r.problem.Fs.length = Fs.length := by
  exact ⟨rfl,List.length_map _⟩

noncomputable def ofComplexBounds
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    GeneratedRecoveryJob s :=
  ofNormalizedBounds h (complexComponentFields Fs) (complexComponentFields_norm_le p Fs hF)

theorem ofComplexBounds_fields
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    let r := ofComplexBounds h Fs hF
    r.problem.Fs = recoveryInputFields p r.problem.precision (complexComponentFields Fs) ∧
      r.problem.Fs.length = 2*Fs.length := by
  dsimp only [ofComplexBounds]
  have hh := ofNormalizedBounds_fields h (complexComponentFields Fs) (complexComponentFields_norm_le p Fs hF)
  exact ⟨hh.1,hh.2.trans (complexComponentFields_length Fs)⟩

end GeneratedRecoveryJob

/-- Reuse the executed normalization stage with the recovery field ABI in its
endpoint. The remaining queue and all generated conversion scratch restore. -/
theorem packedKeyRecoveryFields_exec (p q W N L a : ℕ) (hpq : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (Fs : List (ZMod s → GaussianInt)) (hN : Fs.length = N) (hfit : a+L ≤ s)
    (tail : List (Fin (A+4))) (v : HS 276 Q A U) (S : Stacks 276 A)
    (hq : (S.R 119).length = q) (hpHeader : (S.R 266).length = p)
    (hcommon : (S.R 265).length = W) (hreplicas : (S.R 264).length = N)
    (hpacket : (S.R 267).length = L*W)
    (hsrc : S.R 263 = cstream A W (Fs.map (packedInterval a L)).flatten++tail)
    (hblank : ∀ i ∈ ([110,268,269,270,271,272,273,274,275] : List (Fin 276)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedKeyInputCost p q W N L ∧
      Exec body packedKeyInput (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 263 tail) 110
          (cstream A (2*q+8) ((recoveryInputFields p q Fs).map (packedInterval a L)).flatten))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := packedKeyInput_exec (body := body) p q W N L hpq hW
    (Fs.map (packedInterval a L)).flatten (by simpa only [hN] using packedBatch_length a L Fs hfit)
    tail v S hq hpHeader hcommon hreplicas hpacket hsrc hblank
  rw [recoveryInputFields_packet] at he
  exact ⟨v',n,hu,hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
