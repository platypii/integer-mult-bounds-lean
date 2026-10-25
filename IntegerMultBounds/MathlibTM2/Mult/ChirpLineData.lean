module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpSelectedFixedLine
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupTransfers

/-! # The retained data interface of one forward line, independent of its raw input

A grouped caller may replace the raw-line tape and its high group ports while
retaining this interface. It contains tape facts, not an execution oracle.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

structure LineData (W s t α p q l Γ m w : ℕ) (S : Stacks 640 A) (shared : Bool := false) : Prop where
  G : S.R (processor .ys) = chirpBlockStream (chirpBlockCount t m)
      (fun n => chirpEntryStream A w (3 * m + 1)
        (fun a => chirpNegativeNumerator false s t α q m (n * m) a))
  K : S.R (batch .srcY) = chirpBlockStream (chirpBlockCount t m)
      (fun n => chirpEntryStream A w (4 * m)
        (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (n * m) a))
  ready : Ready (fun r => S.R (processor r)) w q
  proc : ∀ r ∈ [CR.xs, .xsv, .ysv, .acc, .out], S.R (processor r) = []
  clean : CClean output.mul S
  gather : tblHolds gather S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![s, t, m, w, 0, 0, 0, 0, 0, 0], []⟩)
  conv : tblHolds convolution S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![q, t, m, w, l, 0, 0, 0, 0, 0], []⟩)
  word : (S.R wordCounter).length = w
  producer : ∀ i, S.R (producer i) = []
  ring : RpClean host S
  workspace : ∀ k ∈ correlationEmpty, S.R k = []
  dim : ∀ i, S.R (correlationDimensions i) = []
  operand : S.R (batch .srcX) = []
  raw : ChirpRawReady shared s t m w raw S
  outputState : ChirpOutputState output S q w [] (chirpOutputFactors s t α q Γ m) (chirpNormalization q α)
  outdim : ∀ i, (S.R (output.dim i)).length = chirpOutputDimensionCount p q l Γ w t i
  outwork : ∀ i : Fin 22, 9 ≤ i.val → S.R (output.bank i) = []

abbrev SelectedLineData (s t α p : ℕ) (S : Stacks 640 A) (shared : Bool := false) : Prop :=
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  LineData W s t α p q l Γ m w S shared

abbrev LineRead (k : Fin 640) : Prop := k.val < 533 ∧ k ≠ raw .raw

/-- Arithmetic data lies below the raw workspace, apart from the producer ports. -/
abbrev LineCoreRead (k : Fin 640) : Prop := k.val < 500 ∨ (521 ≤ k.val ∧ k.val < 533)

private theorem core_read (k : Fin 640) (hk : LineCoreRead k) : LineRead k := by
  refine ⟨by rcases hk with hk | hk <;> omega, ?_⟩
  intro he
  have hv := congrArg Fin.val he
  change k.val = 505 at hv
  rcases hk with hk | hk <;> omega

private theorem read_of_lt500 (k : Fin 640) (hk : k.val < 500) : LineCoreRead k := Or.inl hk

private theorem processor_read (r : CR) : LineCoreRead (processor r) :=
  read_of_lt500 _ ((processor_range r).2.trans_le (by decide))
private theorem output_read (i : Fin 146) : LineCoreRead (outputTape i) :=
  read_of_lt500 _ (by change i.val < 500; omega)
private theorem bank_read (i : Fin 193) : LineCoreRead (bankTape i) :=
  read_of_lt500 _ ((bank_range i).2.trans_le (by decide))
private theorem product_read (i : Fin 117) : LineCoreRead (productTape i) :=
  read_of_lt500 _ (by simp only [productTape]; omega)
private theorem word_read : LineCoreRead wordCounter := by decide +kernel
private theorem dimension_read (i : Fin 7) : LineCoreRead (correlationDimensions i) := by
  fin_cases i <;> decide +kernel
private theorem producer_read (i : Fin 11) : LineCoreRead (producer i) := by
  right
  simp only [producer]
  omega
private theorem workspace_read : ∀ k ∈ correlationEmpty, LineCoreRead k := by
  have h : correlationEmpty.all (fun k => decide (LineCoreRead k)) = true := by decide +kernel
  intro k hk
  exact of_decide_eq_true (List.all_eq_true.mp h k hk)
private theorem raw_read (r : ChirpRawReg) (hr : r ≠ .raw) : LineRead (raw r) := by
  refine ⟨?_, raw_inj.ne hr⟩
  by_cases hd : r = .dst
  · subst r; rw [raw_link]; exact (processor_range .xs).2.trans_le (by decide)
  · have hc := (rawCode r).isLt
    simp only [raw, ite_eq_right hd]
    omega

/-- Transport arithmetic data and supply the new raw-control interface separately. -/
theorem LineData.transport {shared shared' : Bool} {W s t α p q l Γ m w : ℕ} {S S' : Stacks 640 A}
    (h : LineData W s t α p q l Γ m w S shared) (hL : S'.L = S.L)
    (hR : ∀ k, LineCoreRead k → S'.R k = S.R k)
    (hraw : ChirpRawReady shared' s t m w LinePlacement.raw S') : LineData W s t α p q l Γ m w S' shared' := by
  have hp := funext (fun r => hR _ (processor_read r))
  have hc : (fun r => S'.R (output.cr r)) = (fun r => S.R (output.cr r)) :=
    funext (fun r => hR _ (output_read (OutputPlacement.layout.cr r)))
  have hn : (fun r => S'.R (output.nr r)) = (fun r => S.R (output.nr r)) :=
    funext (fun r => hR _ (output_read (OutputPlacement.layout.nr r)))
  have hclean : CClean LinePlacement.output.mul S' := fun i => ⟨by rw [hL]; exact (h.clean i).1,
    (hR _ (output_read (OutputPlacement.layout.mul i))).trans (h.clean i).2⟩
  constructor
  · exact (hR _ (processor_read .ys)).trans h.G
  · exact (hR _ (product_read (Fixed.batchReg .srcY))).trans h.K
  · rw [hp]; exact h.ready
  · exact fun r hr => (congrFun hp r).trans (h.proc r hr)
  · exact hclean
  · exact fun r => (hR _ (bank_read (ForwardBankPlacement.gather r))).trans (h.gather r)
  · exact fun r => (hR _ (bank_read (ForwardBankPlacement.convolution r))).trans (h.conv r)
  · exact (congrArg List.length (hR _ word_read)).trans h.word
  · exact fun i => (hR _ (producer_read i)).trans (h.producer i)
  · exact ⟨fun i => by rw [hL]; exact h.ring.1 i,
      fun i hi => (hR _ (product_read (Fixed.hostReg i))).trans (h.ring.2 i hi)⟩
  · exact fun k hk => (hR k (workspace_read k hk)).trans (h.workspace k hk)
  · exact fun i => (hR _ (dimension_read i)).trans (h.dim i)
  · exact (hR _ (product_read (Fixed.batchReg .srcX))).trans h.operand
  · exact hraw
  · refine ⟨?_, ?_, hclean, (congrFun hc .xs).trans h.outputState.input,
      (congrFun hc .ys).trans h.outputState.factors, (congrFun hn .ys).trans h.outputState.normalization,
      fun r hr => (congrFun hc r).trans (h.outputState.cr_empty r hr),
      fun r hr => (congrFun hn r).trans (h.outputState.nr_empty r hr)⟩
    · rw [hc]; exact h.outputState.cr_ready
    · rw [hn]; exact h.outputState.nr_ready
  · exact fun i => (congrArg List.length (hR _ (output_read (OutputPlacement.layout.dim i)))).trans (h.outdim i)
  · exact fun i hi => (hR _ (output_read (OutputPlacement.layout.bank i))).trans (h.outwork i hi)

/-- Updating the raw input and high group ports preserves every retained line requirement. -/
theorem LineData.frame {shared : Bool} {W s t α p q l Γ m w : ℕ} {S S' : Stacks 640 A}
    (h : LineData W s t α p q l Γ m w S shared) (hL : S'.L = S.L)
    (hR : ∀ k, LineRead k → S'.R k = S.R k) : LineData W s t α p q l Γ m w S' shared := by
  apply h.transport hL (fun k hk => hR k (core_read k hk))
  cases shared with
  | false => exact fun r hr hd => (hR _ (raw_read r hr)).trans (h.raw r hr hd)
  | true =>
      refine ⟨(congrArg List.length (hR _ (raw_read .count (by decide)))).trans h.raw.1,
        (hR _ (raw_read .control (by decide))).trans h.raw.2.1, ?_⟩
      exact fun r hr hd hn hc => (hR _ (raw_read r hr)).trans (h.raw.2.2 r hr hd hn hc)

/-- Staging a new input line preserves the shared prepared data. -/
theorem LineData.stage {shared : Bool} {W s t α p q l Γ m w : ℕ} {S : Stacks 640 A}
    (h : LineData W s t α p q l Γ m w S shared) (xs rest : List (Fin (A + 4))) :
    LineData W s t α p q l Γ m w { S with R := stageLineR xs rest S.R } shared := by
  apply h.frame (S' := { S with R := stageLineR xs rest S.R }) rfl
  intro k hk
  apply stageLineR_off _ _ _ _ _ _ hk.2
  · intro he; have hv := congrArg Fin.val he
    change k.val = 540 at hv
    omega
  · intro he; have hv := congrArg Fin.val he
    change k.val = 541 at hv
    omega

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

/-- Execute the actual selected line from the retained data and its newly staged input. -/
theorem SelectedLineData.exec {shared : Bool} (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (hA : 96 ≤ A)
    (s t α p : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
    ∀ (u : ZMod s → GaussianInt) (_hu : ∀ j, ‖value q (u j)‖ ≤ 1)
      (v : HS 640 Q A U) (S : Stacks 640 A),
      SelectedLineData s t α p S shared → S.R (raw .raw) = cstream A w (chirpLine s u) →
      ∃ v' n, v'.user = v.user ∧
        n ≤ chirpRawCorrelationModeCost shared W w W w s t q l m w +
          chirpOutputCompleteCost (chirpBlockCount t m * m) p q l Γ w t ∧
        Exec body (programWith shared hQ hQrp) (mk v S) n
          (mk v' { S with R := (Function.update S.R (output.nr .out)
            (cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u))) }) := by
  dsimp only
  intro u hu v S h hi
  exact selected_program_exec (shared := shared) hQ hQrp hA s t α p hst hα hαp u hu v S
    h.G h.K h.ready h.proc h.clean h.gather h.conv h.word h.producer h.ring
    h.workspace h.dim h.operand hi h.raw h.outputState h.outdim h.outwork

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
