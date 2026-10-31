module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall
public import IntegerMultBounds.MathlibTM2.M8.Machine.RootExecutionWithin
public import IntegerMultBounds.Machine.HoareWithinFrame

/-! A physical arbitrary-offset slice call shares the root workspace across
header setup, recursive execution and occupied-header restoration. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCallWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open CallReady (Ready)
open Shared50RecursiveNodeSemantics (encoded)
open NodeLayout (wires)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)

open ArbitrarySliceCall

theorem root_slice (depth : ℕ) (v : Descriptor) (t b : ℕ) (hfit : t+b ≤ v.width)
    (shape : Depth.Shape depth (ArbitraryWidthPieces.slice prime v t b))
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers (ArbitraryWidthPieces.slice prime v t b) hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(RootExecutionWithin.coefficient*volume prime v : ℕ) ≤
      (rootBank (data x) hs f p node scalar st).head j ∧
      (rootBank (data x) hs f p node scalar st).head j+(RootExecutionWithin.coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin Implementation.program
      (fun z => z = rootBank (data x) hs f p node scalar st)
      (fun z => z = rootBank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs f p node scalar st)
      (RootExecution.rootBudget depth (volume prime v)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  intro input hinput
  subst input
  have hin := data_toSlice t b hfit x
  have hout := data_return t b hfit x
  have hm : ∀ j, lo+(RootExecutionWithin.coefficient*volume prime (ArbitraryWidthPieces.slice prime v t b) : ℕ) ≤
      (rootBank (data (ArbitraryWidthSliceTranspose.toSlice t b hfit x)) hs f p node scalar st).head j ∧
      (rootBank (data (ArbitraryWidthSliceTranspose.toSlice t b hfit x)) hs f p node scalar st).head j+
        (RootExecutionWithin.coefficient*volume prime (ArbitraryWidthPieces.slice prime v t b) : ℕ) ≤ hi := by
    rw [hin,ArbitraryWidthPieces.slice_volume prime v t b hfit]
    exact hmargin
  obtain ⟨n,hn,c,hr,hh,hp⟩ := RootExecutionWithin.run_within _ shape hs hv f p node scalar st ready
    (ArbitraryWidthSliceTranspose.toSlice t b hfit x) lo hi hm
  change RunWithin Implementation.program _ n
    ((rootBank (data (ArbitraryWidthSliceTranspose.toSlice t b hfit x)) hs f p node scalar st).start _) c at hr
  change c.tapes = rootBank (data (Shared50RecursiveNodeRows.transpose (one_dvd _)
    (ArbitraryWidthSliceTranspose.toSlice t b hfit x))) hs f p node scalar st at hp
  rw [hin] at hr
  rw [hout] at hp
  refine ⟨n,?_,c,hr,hh,hp⟩
  simpa only [RootExecutionWithin.budget,RootExecution.rootBudget,RootExecution.rootOverhead,
    ArbitraryWidthPieces.slice_volume prime v t b hfit] using hn

omit [Net] in
private theorem append_head_congr {s u a : ℕ} (v w : Tapes s a) (extra extra' : Tapes u a)
    (h : v.head = w.head) (he : extra.head = extra'.head) :
    (v.append extra).head = (w.append extra').head := by
  change (Fin.addCases (m := s) (n := u) v.head extra.head : Fin (s+u) → ℤ) =
    (Fin.addCases (m := s) (n := u) w.head extra'.head : Fin (s+u) → ℤ)
  rw [h,he]

private theorem raw_data_head_eq {v v' : Descriptor} (n : ℕ)
    (x : Fin (volume prime v) → ZMod 2) (y : Fin (volume prime v') → ZMod 2)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    (raw (Shared50RecursiveBank.bank (data x) hs f p node scalar (SharedBank.empty 0 prime) st) n).head =
      (raw (Shared50RecursiveBank.bank (data y) hs f p node scalar (SharedBank.empty 0 prime) st) n).head := by
  unfold data
  rw [CallReady.source_roles,CallReady.source_roles]
  rfl

/-- Payload changes leave every parked root and frame head fixed. -/
theorem bank_offset_head_eq {v v' : Descriptor}
    (x : Fin (volume prime v) → ZMod 2) (y : Fin (volume prime v') → ZMod 2)
    (hs : Fin 6 → List Bool) (ts bs us cs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :
    (bank (data x) hs ts bs f p node scalar st frame).head =
      (bank (data y) hs us cs f p node scalar st frame).head := by
  exact append_head_congr (rootBank (data x) hs f p node scalar st)
    (rootBank (data y) hs f p node scalar st) (SliceHeaderPlacement.tail ts bs frame)
    (SliceHeaderPlacement.tail us cs frame)
    (raw_data_head_eq rootCount x y hs f p node scalar st) rfl

/-- Payload changes leave every parked root and frame head fixed. -/
theorem bank_head_eq {v v' : Descriptor}
    (x : Fin (volume prime v) → ZMod 2) (y : Fin (volume prime v') → ZMod 2)
    (hs : Fin 6 → List Bool) (ts bs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) :
    (bank (data x) hs ts bs f p node scalar st frame).head =
      (bank (data y) hs ts bs f p node scalar st frame).head := by
  exact bank_offset_head_eq x y hs ts bs ts bs f p node scalar st frame

/-- Both physical header phases fit beside one root reserve. -/
def coefficient : ℕ := RootExecutionWithin.coefficient+1030

theorem call_within (depth : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (ts bs : List Bool) (t b : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (hfit : t+b ≤ v.width) (hw : b = Machine.width^depth)
    (hr : roleCount^depth ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime v : ℕ) ≤
      (bank (data x) hs ts bs f p node scalar st frame).head j ∧
      (bank (data x) hs ts bs f p node scalar st frame).head j+(coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin program (fun z => z = bank (data x) hs ts bs f p node scalar st frame)
      (fun z => z = bank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs ts bs f p node scalar st frame)
      (RootExecution.rootBudget depth (volume prime v)+1030*volume prime v) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let child := ArbitrarySliceDimensions.headers (q := prime) hs bs v t b
  let saved := RecursiveViewFrame.savedStack hs frame
  have hc : RecursiveDimensionBank.Headers (ArbitraryWidthPieces.slice prime v t b) child :=
    ArbitrarySliceDimensions.headers_valid hs bs v t b hv hb cb
  have hshape : Depth.Shape depth (ArbitraryWidthPieces.slice prime v t b) :=
    ⟨ArbitraryWidthPieces.slice_positive _ Shared50ModularControl.prime_prime.pos v hp t b,hw,hr⟩
  obtain ⟨hprep,hrestore⟩ := header_contracts v hs ts bs t b hp hv ht hb ct cb hfit
    f p node scalar st frame hfree (data x) (data (ArbitraryWidthSliceTranspose.array t b hfit x))
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hbudget : 900*volume prime v+RootExecutionWithin.coefficient*volume prime v ≤
      coefficient*volume prime v := by
    dsimp only [coefficient]
    nlinarith only [hV]
  have hprepared : ∀ j, lo+(RootExecutionWithin.coefficient*volume prime v : ℕ) ≤
      (bank (data x) child ts bs f p node scalar st saved).head j ∧
      (bank (data x) child ts bs f p node scalar st saved).head j+
        (RootExecutionWithin.coefficient*volume prime v : ℕ) ≤ hi := by
    intro j
    have hh := hprep.head_change j
    have hm := hmargin j
    dsimp only [child,saved] at ⊢
    omega
  have hwp := HoareWithin.of_time_heads hprep lo hi (by
    rintro input rfl j
    have hm := hmargin j
    omega)
  have hwr := HoareWithin.of_time_post_heads hrestore lo hi (by
    rintro output rfl j
    rw [bank_head_eq (ArbitraryWidthSliceTranspose.array t b hfit x) x hs ts bs f p node scalar st frame]
    have hm := hmargin j
    have hb : 2*(128*volume prime v) ≤ coefficient*volume prime v := by
      dsimp only [coefficient]
      nlinarith only [hV]
    omega)
  have hroot := HoareWithin.extend_heads_eq (SliceHeaderPlacement.tail ts bs saved) lo hi
    (root_slice depth v t b hfit hshape child hc f p node scalar st ready x lo hi (by
      intro j
      have hh := hprepared (Fin.castAdd 12 j)
      simpa only [bank,Tapes.append,Fin.addCases_left] using hh))
    (by
      intro j
      have hh := hprepared (Fin.natAdd rootCount j)
      simp only [bank,Tapes.append,Fin.addCases_right] at hh
      omega)
  exact ((hwp.seq hroot).seq hwr).consequence (fun _ h => h) (fun _ h => h) (by omega) (fun _ h => h)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCallWithin
