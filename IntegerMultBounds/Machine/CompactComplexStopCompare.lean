import IntegerMultBounds.Machine.CompactComplexStopThreshold

/-! Runtime stop comparison from a retained canonical remaining-exponent word
and the physically generated threshold word. The zero-leaf test reads the
actual first exponent cell; no branch decision is supplied by the caller. -/
namespace IntegerMultBounds.Machine.CompactComplexStopCompare
noncomputable section
variable {q : ℕ}
open BinaryDescriptorCompare (bank)

def result (es rs : List Bool) : ℤ → Fin (q+4) :=
  Function.update (fun _ => blank) 0
    (bitSymbol (decide (Counter.value es=0 ∨ Counter.value es<Counter.value rs)))

def output (es rs : List Bool) : Tapes 3 q := bank es rs (result es rs) 1 1 0

def action (sy : Fin 3 → Fin (q+4)) (i : Fin 3) : Fin (q+4) × Move :=
  (if i=2 then bitSymbol ((sy 0==blank) || (sy 2==bitSymbol true)) else sy i, .stay)

def leafProgram : Program 3 2 q := DescriptorStackControl.once (by decide) action

def program := seq (BinaryDescriptorCompare.program (q := q)) leafProgram

private theorem canonical_zero (es : List Bool) (hc : GrowingCounterData.Canonical es) :
    Counter.value es=0 ↔ es=[] := by
  constructor
  · intro hz
    have hw := GrowingCounterData.canonical_width es hc
    rw [hz] at hw
    simp at hw
    cases es with
    | nil => rfl
    | cons b es =>
      cases es with
      | nil => cases b <;> simp_all [GrowingCounterData.Canonical,Counter.value]
      | cons c cs => simp at hw
  · rintro rfl; rfl

private theorem head_empty (es : List Bool) :
    (BinaryDescriptorStack.descriptor (a := q) es 1==blank)=decide (es=[]) := by
  cases es with
  | nil => simp [BinaryDescriptorStack.descriptor,BinaryDescriptorStack.empty,putWord,blank]
  | cons b es =>
    rw [BinaryDescriptorStack.descriptor,List.map_cons,putWord_head]
    cases b <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem leaf_runs (es rs : List Bool) (hc : GrowingCounterData.Canonical es) :
    HoareTime (leafProgram (q := q)) (fun v => v=BinaryDescriptorCompare.output es rs)
      (fun v => v=output es rs) 1 := by
  have h := DescriptorStackControl.once_hoare (by decide : 0<3) action
    (BinaryDescriptorCompare.output (q := q) es rs)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i
    simp only [action,Move.offset,add_zero]
    rfl
  · funext i z
    dsimp only [action,output,bank,BinaryDescriptorCompare.output,BinaryCompare.cfg,Config.tapes]
    fin_cases i
    · simp only [Fin.isValue,Fin.zero_eta,ite_true,ite_false,Fin.reduceEq]
      split_ifs with hz <;> simp_all
    · split_ifs with hz <;> simp_all
    · by_cases hz : z=0
      · subst z
        have hb (b : Bool) : (bitSymbol (a := q) b == bitSymbol true)=b := by
          cases b <;> simp [bitSymbol,Fin.ext_iff]
        simp [BinaryDescriptorCompare.result,result,head_empty,canonical_zero es hc,hb]
      · simp [BinaryDescriptorCompare.result,result,hz]

theorem runs (es rs : List Bool) (hc : GrowingCounterData.Canonical es) :
    HoareTime (program (q := q)) (fun v => v=BinaryDescriptorCompare.input es rs)
      (fun v => v=output es rs) (BinaryDescriptorCompare.cost es rs+2) :=
  (BinaryDescriptorCompare.compare_hoare es rs).seq (leaf_runs es rs hc)

theorem runs_linear (es rs : List Bool) (hc : GrowingCounterData.Canonical es) :
    HoareTime (program (q := q)) (fun v => v=BinaryDescriptorCompare.input es rs)
      (fun v => v=output es rs) (2*(es.length+rs.length)+13) :=
  (BinaryDescriptorCompare.compare_linear es rs).seq (leaf_runs es rs hc)

/-- The flag equals the manuscript stop decision using the generated threshold. -/
theorem flag_actual (D e : ℕ) (es : List Bool)
    (he : Counter.value es=e) :
    result (q := q) es (FixedBasePowerUntil.counter (CompactComplexStopThreshold.threshold D)) 0 =
      bitSymbol (Networks.ComplexRecursiveCallSchema.stopped D e) := by
  simp only [result,Function.update_self,he,FixedBasePowerUntil.counter_value]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,CompactComplexStopThreshold.stopped_iff]

end
end IntegerMultBounds.Machine.CompactComplexStopCompare
