import IntegerMultBounds.Machine.FlatAffineScaling
import IntegerMultBounds.Machine.StaticMarkerInit

/-! A blank-workspace entry point for actual coefficient scaling. The fixed
coefficient determines only finite tape wiring and a one-step marker template.
All residue banks, piece buffers, intermediate payloads and sign scratch are
chosen blank; existing execution physically synthesizes every residue/count. -/
namespace IntegerMultBounds.Machine.FlatAffineScalingBootstrap
open Networks
open CountedCopyReuse (empty binary)
open SignedScalingPrepared (Setup)
open ActualAffineScaling (modulus negative)

private def blankBank (c : ℕ) : Tapes c 0 := ⟨fun _ => 0,fun _ _ => blank⟩

def setup (c : ℕ) (bs qs : List Bool) : Setup c where
  background := fun _ _ => blank
  origins := fun _ => 0
  blockBits := bs
  countBits := qs
  modulus := blankBank c
  current := blankBank c

def scratch : SignedScalingDimensions.Scratch := ⟨fun _ => blank,0⟩

theorem setup_valid (c Q B : ℕ) (bs qs : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    (setup c bs qs).Valid Q B := ⟨hb,hq,cb,cq,by intros; rfl⟩

/-- The dimension-independent shape of the complete initial tape bank. -/
def bank (a d : ℕ) (neg : Bool) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :
    Tapes (SignedScalingDimensionsStream.TapeCount a d) 0 :=
  SignedScalingDimensionsStream.input neg (setup a bs qs) (setup d bs qs) scratch 0 0 ns
    source 0 (fun _ => blank) 0 (fun _ => blank) 0 dest 0 (fun _ _ => [])

/-- Only the fixed coefficient/sign enters the transition-table template. -/
def template (a d : ℕ) (neg : Bool) := bank a d neg [] [] [] (fun _ => blank) (fun _ => blank)

private theorem binary_zero (bs : List Bool) : binary bs 0 = separator := by
  rw [binary,putBits_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem bank_heads (a d : ℕ) (neg : Bool) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :
    (bank a d neg bs qs ns source dest).head = (template a d neg).head := by
  change StaticMarkerInit.HeadEq _ _
  unfold template bank SignedScalingDimensionsStream.input SignedScalingDimensions.input
  cases neg <;> repeat' apply StaticMarkerInit.HeadEq.append
  all_goals rfl

private theorem template_heads (a d : ℕ) (neg : Bool) :
    ∀ i, (template a d neg).head i = 0 ∨ (template a d neg).head i = 1 := by
  change StaticMarkerInit.HeadPos (template a d neg)
  unfold template bank SignedScalingDimensionsStream.input SignedScalingDimensions.input
  cases neg <;> repeat' apply StaticMarkerInit.HeadPos.append
  all_goals
    intro i
    first | exact Or.inl rfl | exact Or.inr rfl | (fin_cases i <;> first | exact Or.inl rfl | exact Or.inr rfl)

private theorem template_markers (a d : ℕ) (neg : Bool) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :
    StaticMarkerInit.MarkerRel (template a d neg) (bank a d neg bs qs ns source dest) := by
  unfold template bank SignedScalingDimensionsStream.input SignedScalingDimensions.input
  cases neg <;> repeat' apply StaticMarkerInit.MarkerRel.append
  all_goals
    intro i hi
    first
    | exact hi
    | fin_cases i <;> first
      | rfl
      | exact binary_zero _
      | exact False.elim ((by decide : (blank : Fin 4) ≠ separator) hi)

noncomputable section
variable {P B b : ℕ}

private theorem flat_input_eq {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :
    FlatAffineScaling.input hr a ns (setup r.num.natAbs bs qs) (setup r.den bs qs) scratch
      source 0 (fun _ => blank) 0 (fun _ => blank) 0 dest 0 =
    bank r.num.natAbs r.den (negative r) bs qs ns (putWord source 0 (List.ofFn a)) dest := by
  unfold FlatAffineScaling.input ActualAffineScalingStream.input SignedScalingDimensionsStream.input bank
  rw [FlatAffineScaling.source_eq]
  have he (Q : ℕ) : ScalingExecution.inputWord Q (fun _ => []) = [] := by simp [ScalingExecution.inputWord]
  change bank r.num.natAbs r.den (negative r) bs qs ns
    (putWord (putWord source 0 (List.ofFn a)) 0 (ScalingExecution.inputWord (modulus b) (fun _ => []))) dest =
    bank r.num.natAbs r.den (negative r) bs qs ns (putWord source 0 (List.ofFn a)) dest
  rw [he]
  rfl

/-- Fixed marker bootstrap for an actual network coefficient. -/
def markerProgram {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) :=
  StaticMarkerInit.program (template r.num.natAbs r.den (negative r))
    (ActualAffineScalingStream.program hr).tapes_pos

def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) :=
  seq (markerProgram hr) (ActualAffineScalingStream.program hr)

/-- Marker-free dimensional words and payloads; all generated storage and
residue cells are blank. Every physical head starts at zero. -/
def input {r : ℚ} (_hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :=
  StaticMarkerInit.raw (template r.num.natAbs r.den (negative r))
    (bank r.num.natAbs r.den (negative r) bs qs ns (putWord source 0 (List.ofFn a)) dest)

def output {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :=
  FlatAffineScaling.output hr a ns (setup r.num.natAbs bs qs) (setup r.den bs qs) scratch
    source 0 (fun _ => blank) 0 (fun _ => blank) 0 dest 0

/-- Bootstrap input contains the literal physical array, without address labels. -/
theorem source_tape {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :
    (input hr a bs qs ns source dest).tape (FlatAffineScaling.sourceSlot r) = putWord source 0 (List.ofFn a) := by
  have hh := FlatAffineScaling.source_tape hr a ns (setup r.num.natAbs bs qs) (setup r.den bs qs) scratch
    source 0 (fun _ => blank) 0 (fun _ => blank) 0 dest 0
  rw [flat_input_eq] at hh
  have hm : (template r.num.natAbs r.den (negative r)).tape (FlatAffineScaling.sourceSlot r) 0 ≠ separator := by
    have ht := FlatAffineScaling.source_tape (P := 0) (B := 0) (b := 0) hr
      (fun i => Fin.elim0 i) [] (setup r.num.natAbs [] []) (setup r.den [] []) scratch
      (fun _ => blank) 0 (fun _ => blank) 0 (fun _ => blank) 0 (fun _ => blank) 0
    rw [flat_input_eq] at ht
    simp only [List.ofFn_zero,putWord] at ht
    change (template r.num.natAbs r.den (negative r)).tape (FlatAffineScaling.sourceSlot r) = (fun _ => blank) at ht
    rw [ht]
    decide
  simpa only [input,StaticMarkerInit.raw,hm,ite_false] using hh

/-- Exact creation of the scaling machine's full initial bank in one transition. -/
theorem bootstrap_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :
    HoareTime (markerProgram hr)
      (fun v => v = input hr a bs qs ns source dest)
      (fun v => v = FlatAffineScaling.input hr a ns (setup r.num.natAbs bs qs) (setup r.den bs qs) scratch
        source 0 (fun _ => blank) 0 (fun _ => blank) 0 dest 0) 1 := by
  rw [flat_input_eq]
  exact StaticMarkerInit.initialize_hoare _ _ _ (bank_heads _ _ _ _ _ _ _ _)
    (template_heads _ _ _) (template_markers _ _ _ _ _ _ _ _)

/-- All scratch validity and initial residue conditions are discharged by the
constructed blank setup. Only canonical dimension values remain assumptions. -/
theorem realizes_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (hB : 0 < B) (hP : 0 < P)
    (bs qs ns : List Bool) (hb : Counter.value bs = B) (hq : Counter.value qs = modulus b)
    (hn : Counter.value ns = P) (cb : GrowingCounterData.Canonical bs)
    (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns)
    (source dest : ℤ → Fin 4) :
    HoareTime (program hr)
      (fun v => v = input hr a bs qs ns source dest)
      (fun v => v = output hr a bs qs ns source dest ∧
        ∀ (i : Fin P) (y : Fin (modulus b)) (j : Fin B),
        v.tape (ActualAffineScalingStream.destinationSlot r)
          (((i.val*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b))).val*B+j.val : ℕ) : ℤ)) =
          a (FiberLayoutData.index i y j))
      (ActualAffineScalingStream.nonemptyConstant r*(P*(modulus b*B))+251) := by
  have hs := FlatAffineScaling.realizes_hoare hr a hB hP ns hn cn
    (setup r.num.natAbs bs qs) (setup r.den bs qs) scratch
    (setup_valid _ _ _ bs qs hb hq cb cq) (setup_valid _ _ _ bs qs hb hq cb cq)
    (by intros; rfl) source 0 (fun _ => blank) 0 (fun _ => blank) 0 dest 0
    (by intros; rfl) (by intros; rfl)
  have hh := (bootstrap_hoare hr a bs qs ns source dest).seq hs
  apply hh.consequence (fun _ h => h) _ (by omega)
  intro v hv
  simpa only [output,zero_add] using hv

end
end IntegerMultBounds.Machine.FlatAffineScalingBootstrap
