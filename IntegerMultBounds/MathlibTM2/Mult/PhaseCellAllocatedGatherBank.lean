module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawGeometryGatherReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassBanks

/-! Append one private routing bank to a numerical class bank. Only the router's
source is redirected to the numerical supplier source; all other ports are private. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
open PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T K : ℕ}

def extendedBank (bank : ComputedClassBank → Fin T) : ComputedClassBank → Fin (T+PackedTranspose.tapeCount) :=
  fun k => Fin.castAdd PackedTranspose.tapeCount (bank k)

theorem extendedBank_injective (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank) :
    Function.Injective (extendedBank bank) := by
  intro i j he
  apply hinj
  apply Fin.ext
  exact congrArg (fun k : Fin (T+PackedTranspose.tapeCount) => k.val) he

theorem prefix_ne_routing (k : Fin T) (i : Fin PackedTranspose.tapeCount) :
    (Fin.castAdd PackedTranspose.tapeCount k : Fin (T+PackedTranspose.tapeCount)) ≠ Fin.natAdd T i := by
  intro he
  have hv := congrArg (fun j : Fin (T+PackedTranspose.tapeCount) => j.val) he
  have hk := k.isLt
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

def gatherPlacement (bank : ComputedClassBank → Fin T) : Fin PackedTranspose.tapeCount → Fin (T+PackedTranspose.tapeCount) :=
  redirectRegister (Fin.natAdd T) (extra 1) (control (extendedBank bank) .source)

theorem gatherPlacement_injective (bank : ComputedClassBank → Fin T) : Function.Injective (gatherPlacement bank) := by
  apply redirectRegister_injective
  · intro i j he
    apply Fin.ext
    have hv := congrArg (fun k : Fin (T+PackedTranspose.tapeCount) => k.val) he
    simp only [Fin.val_natAdd] at hv
    omega
  · intro i
    exact (prefix_ne_routing (bank (.control .source)) i).symm

@[simp] theorem gatherPlacement_source (bank : ComputedClassBank → Fin T) :
    gatherPlacement bank (extra 1) = control (extendedBank bank) .source := redirectRegister_owned _ _ _

theorem gatherPlacement_private (bank : ComputedClassBank → Fin T) (i : Fin PackedTranspose.tapeCount)
    (hi : i ≠ extra 1) : gatherPlacement bank i = Fin.natAdd T i := redirectRegister_off _ _ _ _ hi

@[simp] theorem gatherPlacement_header (bank : ComputedClassBank → Fin T) (i : Fin 117) :
    gatherPlacement bank (headerReg i) = Fin.natAdd T (headerReg i) := gatherPlacement_private bank _ (base_extra _ 1)

theorem gatherPlacement_meets_bank (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (i : Fin PackedTranspose.tapeCount) (k : ComputedClassBank) :
    gatherPlacement bank i = extendedBank bank k ↔ i = extra 1 ∧ k = .control .source := by
  by_cases hi : i = extra 1
  · subst i
    simp only [gatherPlacement_source,control,(extendedBank_injective bank hinj).eq_iff,true_and]
    exact eq_comm
  · rw [gatherPlacement_private bank i hi]
    have hoff := (prefix_ne_routing (bank k) i).symm
    simp only [extendedBank] at *
    exact iff_of_false hoff (by simp [hi])

theorem allocatedGeometryReady (bank : ComputedClassBank → Fin T)
    (V s a width radius L w : ℕ) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K))
    (hs : S.R (Fin.natAdd T (headerReg 32)) = binSyms V s)
    (hw : S.R (Fin.natAdd T (headerReg 33)) = binSyms V width)
    (hr : S.R (Fin.natAdd T (headerReg 34)) = binSyms V radius)
    (hL : S.R (Fin.natAdd T (headerReg 35)) = binSyms V L)
    (h37 : (S.R (Fin.natAdd T (headerReg 37))).length = V)
    (h115 : (S.R (Fin.natAdd T (headerReg 115))).length = V)
    (h87 : (S.R (Fin.natAdd T (headerReg 87))).length = w)
    (hrep : (S.R (Fin.natAdd T replicaCount)).length = 2^a)
    (hblank : ∀ i, i ∉ geometryLivePorts → S.R (Fin.natAdd T i) = [])
    (hleft : ∀ i, S.L (Fin.natAdd T i) = [])
    (hsourceLeft : S.L (control (extendedBank bank) .source) = []) :
    GeometryReady (gatherPlacement bank) V s a width radius L w S := by
  apply geometryReady_of_raw_placed
  · simpa only [gatherPlacement_header] using hs
  · simpa only [gatherPlacement_header] using hw
  · simpa only [gatherPlacement_header] using hr
  · simpa only [gatherPlacement_header] using hL
  · simpa only [gatherPlacement_header] using h37
  · simpa only [gatherPlacement_header] using h115
  · simpa only [gatherPlacement_header] using h87
  · rw [gatherPlacement_private bank replicaCount (base_extra _ 1)]
    exact hrep
  · intro i hi
    have hne : i ≠ extra 1 := by intro he; subst i; simp [geometryLivePorts] at hi
    rw [gatherPlacement_private bank i hne]
    exact hblank i hi
  · intro i
    by_cases hi : i = extra 1
    · subst i; simpa only [gatherPlacement_source] using hsourceLeft
    · rw [gatherPlacement_private bank i hi]
      exact hleft i

/-- The numerical supplier source is the actual output of the allocated router;
all other caller storage and the private suffix are restored. -/
theorem allocatedGeometryGather_exec_within {Q : ℕ} {P U : Type}
    (bank : ComputedClassBank → Fin T)
    (body : P → Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (V s a width radius L w : ℕ)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hA : 4 ≤ prime+K) (hV : 0 < V) (hpacket : 0 < L*w)
    (hbits : a+Nat.clog 2 (IntegerMultBounds.NLogN.PhaseCellMatrix.coreGatherIndices s width radius L).length < V)
    (hfit : (L*w)*2^(a+Nat.clog 2 (IntegerMultBounds.NLogN.PhaseCellMatrix.coreGatherIndices s width radius L).length) < 2^V)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a)
    (v : HS (T+PackedTranspose.tapeCount) Q (prime+K) U) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K))
    (hs : S.R (Fin.natAdd T (headerReg 32)) = binSyms V s)
    (hw : S.R (Fin.natAdd T (headerReg 33)) = binSyms V width)
    (hr : S.R (Fin.natAdd T (headerReg 34)) = binSyms V radius)
    (hL : S.R (Fin.natAdd T (headerReg 35)) = binSyms V L)
    (h37 : (S.R (Fin.natAdd T (headerReg 37))).length = V)
    (h115 : (S.R (Fin.natAdd T (headerReg 115))).length = V)
    (h87 : (S.R (Fin.natAdd T (headerReg 87))).length = w)
    (hrep : (S.R (Fin.natAdd T replicaCount)).length = 2^a)
    (hblank : ∀ i, i ∉ geometryLivePorts → S.R (Fin.natAdd T i) = [])
    (hleft : ∀ i, S.L (Fin.natAdd T i) = [])
    (hsourceLeft : S.L (control (extendedBank bank) .source) = [])
    (hsource : S.R (control (extendedBank bank) .source) = cstream (prime+K) w
      (coreGatherPayload width radius L Fs)) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ geometryGatherTimeCost hstates V s a width radius L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        geometryGatherStockAllowance hstates V s a width radius L w) depth
        (embProg (gatherPlacement bank) Empty.elim (geometryGatherProgram (P := Empty) hstates)) (mk v S) n
        (mk v' {S with R := (Function.update S.R (control (extendedBank bank) .source)
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  have hready := allocatedGeometryReady bank V s a width radius L w S
    hs hw hr hL h37 h115 h87 hrep hblank hleft hsourceLeft
  simpa only [gatherPlacement_source] using hready.exec body (gatherPlacement_injective bank)
    hstates hwidth hwide hLfit hA hV hpacket hbits hfit Fs hreplicas
    (by simpa only [gatherPlacement_source] using hsource) v depth

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
