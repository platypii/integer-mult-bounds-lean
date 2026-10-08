import IntegerMultBounds.Machine.FlatAffineScalingPayload
import IntegerMultBounds.Machine.BinaryDescriptorInstallRaw

/-! Fixed physical descriptor positions in the marker-free affine scaling input. -/
namespace IntegerMultBounds.Machine.FlatAffineScalingInputLayout

inductive Kind where
  | work | payload | block | count | prefix
  deriving DecidableEq

private def join {m n : ℕ} (x : Fin m → Kind) (y : Fin n → Kind) : Fin (m+n) → Kind :=
  Fin.addCases x y

/-- Coefficient-dependent workspace contains just one B and one Q input. -/
def coefficientKinds (c : ℕ) (source : Kind) : Fin (ScalingPreparedExecution.TapeCount c) → Kind :=
  let init : Fin (1+c+2) → Kind := join (join (fun _ : Fin 1 => .work) (fun _ : Fin c => .work)) ![.work,.block]
  let synthesis : Fin (1+c+2+c+c+2) → Kind :=
    join (join (join init (fun _ : Fin c => .work)) (fun _ : Fin c => .work)) ![.work,.count]
  join synthesis (join (join ![source,.work,.work,.work] (fun _ : Fin c => .work)) ![.work,.work])

/-- Exactly twelve fixed descriptor destinations; payload occupies a separate slot. -/
def kinds (a d : ℕ) : Fin (SignedScalingDimensionsStream.TapeCount a d) → Kind :=
  join (join (join
    (join (join (coefficientKinds a .payload) (coefficientKinds d .work)) ![.work,.work,.block,.work,.count])
    (join ![.work,.work,.work,.work,.work,.block,.work,.count,.work,.work,.work]
      ![.work,.work,.work,.work,.block,.work]))
    ![.work,.work,.block,.work,.count]) ![.work,.prefix]

def word (source : ℤ → Fin 4) (bs qs ns : List Bool) : Kind → ℤ → Fin 4
  | .work => fun _ => blank
  | .payload => source
  | .block => BinaryDescriptorInstallRaw.rawWord 0 bs
  | .count => BinaryDescriptorInstallRaw.rawWord 0 qs
  | .prefix => BinaryDescriptorInstallRaw.rawWord 0 ns

/-- All metadata tape heads are at zero before marker initialization. -/
def bank (a d : ℕ) (source : ℤ → Fin 4) (bs qs ns : List Bool) :
    Tapes (SignedScalingDimensionsStream.TapeCount a d) 0 :=
  ⟨fun _ => 0,fun i => word source bs qs ns (kinds a d i)⟩

private theorem raw_binary (xs : List Bool) :
    Function.update (CountedCopyReuse.binary xs) 0 blank = BinaryDescriptorInstallRaw.rawWord 0 xs := by
  funext z
  by_cases hz : z = 0
  · simp [hz,BinaryDescriptorInstallRaw.rawWord]
  · simp [hz,BinaryDescriptorInstallRaw.rawWord,RadixZeroFill.encodedBinary,RadixToBinary.binaryEncoding,
      CountedCopyReuse.binary]

private theorem raw_empty : Function.update CountedCopyReuse.empty 0 blank = (fun _ => blank) := by
  funext z
  by_cases hz : z = 0 <;> simp [hz,CountedCopyReuse.empty]

private def Shape {t : ℕ} (template target : Tapes t 0) (ks : Fin t → Kind)
    (source : ℤ → Fin 4) (bs qs ns : List Bool) : Prop :=
  ∀ i, (StaticMarkerInit.raw template target).tape i = word source bs qs ns (ks i)

private theorem Shape.append {m n : ℕ} {v w : Tapes m 0} {v' w' : Tapes n 0}
    {ks : Fin m → Kind} {ks' : Fin n → Kind} {source : ℤ → Fin 4} {bs qs ns : List Bool}
    (h : Shape v w ks source bs qs ns) (h' : Shape v' w' ks' source bs qs ns) :
    Shape (v.append v') (w.append w') (join ks ks') source bs qs ns := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [StaticMarkerInit.raw,Tapes.append,join,Fin.addCases_left] using h i
  | right i => simpa only [StaticMarkerInit.raw,Tapes.append,join,Fin.addCases_right] using h' i

private def coefficientBank (active : Bool) (c : ℕ) (source : ℤ → Fin 4) (bs qs : List Bool) :
    Tapes (ScalingPreparedExecution.TapeCount c) 0 :=
  (ScalingDescriptors.initial bs qs ⟨fun _ => 0,fun _ _ => blank⟩ ⟨fun _ => 0,fun _ _ => blank⟩).append
    (((CountedCopyReuse.bank source (fun _ => blank) CountedCopyReuse.empty (fun _ => blank) 0 0 1 0).append
      (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes c 0)).append
      (CountedLoopReuse.controls CountedCopyReuse.empty
        (if active then fun _ => blank else CountedCopyReuse.empty) 0 0))

private theorem coefficient_shape (active : Bool) (c : ℕ) (source : ℤ → Fin 4) (bs qs ns : List Bool) :
    Shape (coefficientBank active c (fun _ => blank) [] []) (coefficientBank active c (if active then source else fun _ => blank) bs qs)
      (coefficientKinds c (if active then .payload else .work)) source bs qs ns := by
  cases active <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals unfold coefficientBank coefficientKinds
  all_goals repeat' apply Shape.append
  all_goals
    intro i
    first
    | rfl
    | (fin_cases i <;> first | rfl | exact raw_binary _ | exact raw_empty)

private theorem span_shape (source : ℤ → Fin 4) (bs qs ns : List Bool) :
    Shape (CountedSpanSeek.bank CountedCopyReuse.empty 0 [] [])
      (CountedSpanSeek.bank CountedCopyReuse.empty 0 bs qs)
      ![.work,.work,.block,.work,.count] source bs qs ns := by
  intro i
  fin_cases i <;> first | rfl | exact raw_binary _ | exact raw_empty

private theorem negation_shape (source : ℤ → Fin 4) (bs qs ns : List Bool) :
    Shape (NegationDescriptors.initial [] []) (NegationDescriptors.initial bs qs)
      ![.work,.work,.work,.work,.work,.block,.work,.count,.work,.work,.work] source bs qs ns := by
  intro i
  fin_cases i <;> rfl

private theorem sign_shape (neg : Bool) (source : ℤ → Fin 4) (bs qs ns : List Bool) :
    Shape (⟨![0,0,0,1,1,1],![CountedCopyReuse.empty,(if neg then fun _ => blank else CountedCopyReuse.empty),fun _ => blank,
        CountedCopyReuse.empty,CountedCopyReuse.binary [],CountedCopyReuse.empty]⟩ : Tapes 6 0)
      ⟨![0,0,0,1,1,1],![CountedCopyReuse.empty,(if neg then fun _ => blank else CountedCopyReuse.empty),fun _ => blank,
        CountedCopyReuse.empty,CountedCopyReuse.binary bs,CountedCopyReuse.empty]⟩
      ![.work,.work,.work,.work,.block,.work] source bs qs ns := by
  intro i
  cases neg <;> fin_cases i <;> first | rfl | exact raw_binary _ | exact raw_empty

private theorem prefix_shape (source : ℤ → Fin 4) (bs qs ns : List Bool) :
    Shape (CountedLoopReuse.controls CountedCopyReuse.empty (CountedCopyReuse.binary []) 1 1)
      (CountedLoopReuse.controls CountedCopyReuse.empty (CountedCopyReuse.binary ns) 1 1)
      ![.work,.prefix] source bs qs ns := by
  intro i
  fin_cases i <;> first | rfl | exact raw_binary _ | exact raw_empty

/-- Exact full raw bank, before installing the fixed marker template. -/
theorem raw_bank (a d : ℕ) (neg : Bool) (source : ℤ → Fin 4) (bs qs ns : List Bool) :
    StaticMarkerInit.raw (FlatAffineScalingBootstrap.template a d neg)
      (FlatAffineScalingBootstrap.bank a d neg bs qs ns source (fun _ => blank)) = bank a d source bs qs ns := by
  apply congrArg₂ Tapes.mk
  · rfl
  · apply funext
    change Shape _ _ _ source bs qs ns
    unfold kinds
    apply Shape.append
    · apply Shape.append
      · apply Shape.append
        · apply Shape.append
          · apply Shape.append
            · exact coefficient_shape true a source bs qs ns
            · cases neg <;> exact coefficient_shape false d source bs qs ns
          · exact span_shape source bs qs ns
        · apply Shape.append
          · exact negation_shape source bs qs ns
          · cases neg <;> first | exact sign_shape false source bs qs ns | exact sign_shape true source bs qs ns
      · exact span_shape source bs qs ns
    · exact prefix_shape source bs qs ns

open Networks
open ActualAffineScaling (modulus)

/-- The actual ready scaler receives precisely this fixed marker-free layout. -/
theorem ready_input {P B b : ℕ} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) :
    FlatAffineScalingReady.input hr a bs qs ns (fun _ => blank) (fun _ => blank) =
      bank r.num.natAbs r.den (putWord (fun _ => blank) 0 (List.ofFn a)) bs qs ns :=
  raw_bank _ _ _ _ _ _ _

/-- Alphabet lifting changes symbols only, preserving every physical slot. -/
theorem payload_input {P B b radix : ℕ} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) :
    FlatAffineScalingPayload.input (radix := radix) hr a bs qs ns =
      Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
        (bank r.num.natAbs r.den (putWord (fun _ => blank) 0 (List.ofFn a)) bs qs ns) := by
  unfold FlatAffineScalingPayload.input
  rw [ready_input]


end IntegerMultBounds.Machine.FlatAffineScalingInputLayout
