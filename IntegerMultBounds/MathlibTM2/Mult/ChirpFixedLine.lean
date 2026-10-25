module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineControls
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardLine

/-! # One fixed 640-tape program for the forward line with retained setup -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Spec.SignedRingProduct

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

noncomputable def programWith (shared : Bool) (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) : Pr P 640 Q A U :=
  .seq (.seq (chirpGatherFromDimensionsMode shared gather raw) (.seq
    (.seq (chirpMakeXSetup gather processor output.mul output.mul_inj (by decide) hQ
      (producer 0) (producer 1) (producer 2) (producer 3) wordCounter (producer 4)
      (producer 5) (producer 6) (producer 7) (producer 8) (producer 9) (producer 10) (batch .srcX))
      (.seq (.seq (chirpS1DimensionSetup convolution correlationDimensions)
        (.seq (chirpBatchProduct setup ring host ringLayout (by decide) hQrp
          (batch .records) (batch .recordSaved) (batch .srcX) (batch .srcY)
          (batch .saved) (batch .acc) (batch .buf) (batch .savedBlock) (batch .tmp) extraction)
          (clearWords (List.ofFn correlationDimensions)))) (uclear (batch .srcX))))
    (uclear (processor .xs)))) (chirpOutputRun output (by decide) hQ)

/-- The original line generates its own advance schedule. -/
noncomputable def program (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) : Pr P 640 Q A U :=
  programWith false hQ hQrp

/-- Static allocation is fully discharged; only actual data and numerical conditions remain. -/
theorem program_exec {shared : Bool} (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (hA : 96 ≤ A)
    (W s t α p q l Γ m w : ℕ) [NeZero s] [NeZero t]
    (hs : 0 < s) (hst : s < t) (hm : 0 < m) (hα : 0 < α) (hq : 13 ≤ q)
    (hw : q + l + Γ + 5 ≤ w) (hpq : p ≤ q) (hwW : w ≤ W)
    (hscalar : ∀ i : Fin 6, (![s, t, m, w, q, l] : Fin 6 → ℕ) i < 2 ^ W)
    (hsize : s + 3 * m + 1 < 2 ^ W) (hvolume : (s + 3 * m + 1) * w < 2 ^ W)
    (htm : t + m < 2 ^ W) (hproduct : s * (t + m) < 2 ^ W)
    (hPfit : q + 1 < 2 ^ W) (hBfit : 4 * m < 2 ^ W) (hl : 7 * m ≤ 2 ^ l)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (v : HS 640 Q A U) (S : Stacks 640 A)
    (hG : S.R (processor .ys) = chirpBlockStream (chirpBlockCount t m)
      (fun n => chirpEntryStream A w (3 * m + 1)
        (fun a => chirpNegativeNumerator false s t α q m (n * m) a)))
    (hK : S.R (batch .srcY) = chirpBlockStream (chirpBlockCount t m)
      (fun n => chirpEntryStream A w (4 * m)
        (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (n * m) a)))
    (hready : Ready (fun r => S.R (processor r)) w q)
    (hproc : ∀ r ∈ [CR.xs, .xsv, .ysv, .acc, .out], S.R (processor r) = [])
    (hclean : CClean output.mul S)
    (hgather : tblHolds gather S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![s, t, m, w, 0, 0, 0, 0, 0, 0], []⟩))
    (hconv : tblHolds convolution S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![q, t, m, w, l, 0, 0, 0, 0, 0], []⟩))
    (hword : (S.R wordCounter).length = w) (hproducer : ∀ i, S.R (producer i) = [])
    (hring : RpClean host S) (hworkspace : ∀ k ∈ correlationEmpty, S.R k = [])
    (hdim : ∀ i, S.R (correlationDimensions i) = []) (hoperand : S.R (batch .srcX) = [])
    (hinput : S.R (raw .raw) = cstream A w (chirpLine s u))
    (hraw : ChirpRawReady shared s t m w raw S)
    (hE : ∀ e ∈ chirpOutputFactors s t α q Γ m, |(e : ℝ) / 2 ^ q| ≤ 2)
    (houtput : ChirpOutputState output S q w [] (chirpOutputFactors s t α q Γ m) (chirpNormalization q α))
    (houtdim : ∀ i, (S.R (output.dim i)).length = chirpOutputDimensionCount p q l Γ w t i)
    (houtwork : ∀ i : Fin 22, 9 ≤ i.val → S.R (output.bank i) = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ chirpRawCorrelationModeCost shared W w W w s t q l m w +
        chirpOutputCompleteCost (chirpBlockCount t m * m) p q l Γ w t ∧
      Exec body (programWith shared hQ hQrp) (mk v S) n
        (mk v' { S with R := (Function.update S.R (output.nr .out)
          (cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u))) }) := by
  have hfitG : ∀ i : Fin 10, (![s, t, m, w, 0, 0, 0, 0, 0, 0] : Fin 10 → ℕ) i < 2 ^ W := by
    intro i
    fin_cases i <;> first | exact hscalar 0 | exact hscalar 1 | exact hscalar 2 | exact hscalar 3 | simp
  have hfitC : ∀ i : Fin 10, (![q, t, m, w, l, 0, 0, 0, 0, 0] : Fin 10 → ℕ) i < 2 ^ W := by
    intro i
    fin_cases i <;> first | exact hscalar 4 | exact hscalar 1 | exact hscalar 2 | exact hscalar 3 | exact hscalar 5 | simp
  exact chirpForwardLine_exec (shared := shared) (body := body) (W := W) (e := w) (s := s) (t := t)
    (α := α) (q := q) (w := w) (m := m) (l := l) (dimW := W) (dimWidth := w) processor_inj processor_mul output.mul_inj (by decide) hQ hA
    gather_inj producer_registers gather_counters processor_counters multiplier_counters
    (List.replicate W tick) (List.replicate w tick) (by simp) (by simp) hwW
    ⟨![s, t, m, w, 0, 0, 0, 0, 0, 0], []⟩ rfl rfl rfl hs (by omega) hm hα hq (by omega)
    hsize hvolume (by intro i hi; fin_cases i <;> first | (simp at hi; done) | rfl) hfitG u hu
    (fun r => S.R (processor r)) hready (hproc .xs (by simp)) hG
    (hproc .xsv (by simp)) (hproc .ysv (by simp)) (hproc .acc (by simp)) (hproc .out (by simp))
    v S hclean (fun _ => rfl) hgather hword
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hproducer _)
    ring host ringLayout (by decide) hQrp setup (batch .records) (batch .recordSaved) (batch .srcY)
    (batch .saved) (batch .acc) (batch .buf) (batch .savedBlock) (batch .tmp) extraction batchLayout
    ⟨hring, hworkspace⟩ correlationDimensions_inj hdim workspace_dimensions
    (fun r _ i => private_dimensions r i)
    (fun i => (dimensions_operand i).1) (fun i => (dimensions_operand i).2.1)
    (fun i => (dimensions_operand i).2.2.1) convolution convolution_inj dimensions_bank
    (List.replicate W tick) (List.replicate w tick) (by simp) (by simp) hwW
    ⟨![q, t, m, w, l, 0, 0, 0, 0, 0], []⟩ rfl rfl rfl rfl rfl
    hPfit (by omega) hBfit (by intro i hi; fin_cases i <;> first | (simp at hi; done) | rfl) hfitC hconv
    (fun k hk => (workspace_operands k hk).1) (fun r _ => (private_operands r).1)
    dimensions_source extraction_operand hK kernel_operand hoperand hst hl
    raw raw_inj gather_raw raw_link rfl htm hproduct hinput hraw producer_input
    (fun i => (dimensions_operand i).2.2.2) dimensions_input
    (fun k hk => (workspace_operands k hk).2) (fun r _ => (private_operands r).2)
    output_input kernel_input output correlation_link p Γ hpq hw hE houtput houtdim houtwork

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
