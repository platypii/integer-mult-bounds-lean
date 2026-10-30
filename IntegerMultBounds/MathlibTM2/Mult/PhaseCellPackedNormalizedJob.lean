module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedFactoryDescriptorStep

/-! Mathematical jobs for one fixed packed descriptor machine. Job records
contain ordinary input data and mathematical bounds, never execution premises. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

structure PackedNormalizedJob (A s : ℕ) [NeZero s] where
  p : ℕ
  u : ℕ
  l : ℕ
  targetOut : ℕ
  t : ℕ
  a : ℕ
  b : ℕ
  V : ℕ
  Bcore : ℕ
  q : ℕ
  W : ℕ
  coreWidth : ℕ
  k : ℕ
  radius : ℕ
  localityTarget : ℕ
  α : ℝ
  gap : ℝ
  C : ZMod s → GaussianInt
  Fs : List (ZMod s → GaussianInt)
  Y : (ZMod s → GaussianInt) → ZMod s → ℝ
  bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
    (target := targetOut+1) (rhsExp := 2) (a := a) (b := b) (V := V) α gap C
  hsCore : s < 2^Bcore
  hqSizing : q = executionPrecision p l
    (boundaryHaloTarget p u (boundaryRecoveryTarget p (targetOut+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2
  hpq : p+1 ≤ q
  hW : 2*q+8 ≤ W
  hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1
  haEq : a = coreStart coreWidth k-radius
  hbEq : b = coreStart coreWidth k+coreLength s coreWidth k+radius
  hleft : radius ≤ coreStart coreWidth k
  hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s
  hcoeff : ∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u (PhaseCellBand.width p u) (a+j),
    Fits (2*q+8) z ∧ z.im = 0
  hvaluesFit : ∀ i : Fin 8, ![p,u,l,targetOut,s,t,a,b] i < 2^Bcore
  hbandRoom : 64*(p+1)+u < 2^Bcore
  hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^Bcore
  hprecisionRoom : inversePrecisionRoom p l targetOut
    (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u) < 2^Bcore
  hhalo : haloVertices s a b = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo
  hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
    (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re)

namespace PackedNormalizedJob
variable {A s Q T : ℕ} [NeZero s] {U : Type}

def emptyHost : Stacks 242 A := ⟨[],[],fun _ => [],fun _ => []⟩

noncomputable def words (r : PackedNormalizedJob A s) : Fin 325 → List (Fin (A+4)) :=
  packedNormalizedFactoryPacketWords emptyHost r.Bcore r.V r.p r.u r.l r.targetOut s r.t r.a r.b
    r.coreWidth r.k r.radius r.W r.Fs

noncomputable def initial (r : PackedNormalizedJob A s) : Stacks 325 A :=
  packedNormalizedFactoryInput emptyHost r.Bcore r.V r.p r.u r.l r.targetOut s r.t r.a r.b
    r.coreWidth r.k r.radius r.W r.Fs

/-- The initial private stock is exactly the total ordinary word volume. -/
theorem initialStock (r : PackedNormalizedJob A s) :
    registerBankStock r.initial = ∑ i, (r.words i).length := by
  rw [registerBankStock_eq_right_sum r.initial
    (packedNormalizedFactoryInput_left emptyHost r.Bcore r.V r.p r.u r.l r.targetOut s r.t r.a r.b
      r.coreWidth r.k r.radius r.W r.Fs)]
  exact congrArg (fun R : Fin 325 → List (Fin (A+4)) => ∑ i, (R i).length)
    (packedNormalizedFactoryInput_words emptyHost r.Bcore r.V r.p r.u r.l r.targetOut s r.t r.a r.b
      r.coreWidth r.k r.radius r.W r.Fs)

noncomputable def kernelTime (r : PackedNormalizedJob A s) : ℕ :=
  packedKeyNormalizedBatchCost r.Bcore r.p r.q r.W r.u r.l s r.t r.a r.b r.V
    (boundaryRecoveryTarget r.p (r.targetOut+1)) (r.targetOut+1) 2 r.targetOut r.coreWidth r.k r.radius r.Fs.length

noncomputable def workspace (r : PackedNormalizedJob A s) : ℕ :=
  packedKeyNormalizedWorkspace r.Bcore r.p r.q r.W r.u r.l s r.t r.a r.b r.V
    (boundaryRecoveryTarget r.p (r.targetOut+1)) (r.targetOut+1) 2 r.targetOut r.coreWidth r.k r.radius r.Fs.length

def persistent (r : PackedNormalizedJob A s) : ℕ := (2*r.Fs.length)*((r.b-r.a)*(2*r.q+8))+r.V

noncomputable def cleanup (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (r : PackedNormalizedJob A s) : ℕ :=
  6*((∑ i, (r.words i).length)+r.persistent+
    (mnProgPush (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) hR hQ)+1)*r.workspace)+1956

noncomputable def stepTime (work : Fin 325 → Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (r : PackedNormalizedJob A s) : ℕ :=
  takeDescriptorBankCost (placedDescriptorFields work r.words)+r.kernelTime+r.cleanup (U := U) hR hQ

noncomputable def stepStock (work : Fin 325 → Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (r : PackedNormalizedJob A s) : ℕ :=
  takeDescriptorBankCost (placedDescriptorFields work r.words)+(r.persistent+r.workspace)+r.cleanup (U := U) hR hQ

noncomputable def output (r : PackedNormalizedJob A s) (word : List (Fin (A+4))) : Prop :=
  PackedNormalizedOutput r.p r.W r.targetOut r.coreWidth r.k r.localityTarget r.Fs r.Y word

/-- Published symbols are determined by replica count, owned core and word width. -/
def outputVolume (r : PackedNormalizedJob A s) : ℕ :=
  r.Fs.length * coreLength s r.coreWidth r.k * r.W

theorem output_length (r : PackedNormalizedJob A s) {word : List (Fin (A+4))}
    (h : r.output word) : word.length = r.outputVolume := by
  obtain ⟨Gs,hGs,rfl,_⟩ := h
  simp only [List.length_flatten,List.map_map,Function.comp_def,length_cstream,ownedCoreWords_length,
    List.map_const',List.sum_replicate,hGs,outputVolume,nsmul_eq_mul,Nat.cast_id,Nat.mul_assoc]

theorem outputs_length {records : List (PackedNormalizedJob A s)}
    {outputs : List (List (Fin (A+4)))} (h : List.Forall₂ output records outputs) :
    outputs.flatten.length = (records.map outputVolume).sum := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.flatten_cons,List.length_append,List.map_cons,List.sum_cons,
      output_length _ h,ih]

end PackedNormalizedJob
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
