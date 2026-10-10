import IntegerMultBounds.Machine.NativeSignedGapHeadersReturn
import IntegerMultBounds.Machine.CompactNativeReturnGapBudget

/-! Paid precision return at the native caller's actual source43. Nine appended
slots hold the stream length, two true denominator descriptors and clean work.
All other native66 tapes stay fixed. Recursive production/stack restoration of
the true denominator descriptors is an explicit remaining obligation. -/
namespace IntegerMultBounds.Machine.CompactNativeGapHeadersReturn
noncomputable section
open SharedPlacementAlphabet (setTape)
open NativeSignedGapHeadersReturn (cost)
open RadixSignedShiftRight (Word)
open NativeSignedReturnStream (volume)

def slots : Fin 10 → Fin 75 := fun i => if i.val=0 then 43 else ⟨65+i.val,by have := i.isLt; omega⟩
theorem slots_injective : Function.Injective slots := by
  intro i j h
  have hv := congrArg Fin.val h
  unfold slots at hv
  split_ifs at hv <;> simp_all only
  all_goals apply Fin.ext; omega

def placement : Fin (10+65) ≃ Fin 75 := InjectivePlacement.placement slots slots_injective rfl
def program := Placement.placed NativeSignedGapHeadersReturn.program placement

def extras (small : Tapes 10 2) : Tapes 9 2 :=
  ⟨fun i => small.head ⟨i.val+1,by have := i.isLt; omega⟩,
   fun i => small.tape ⟨i.val+1,by have := i.isLt; omega⟩⟩
def install (old : Tapes 66 2) (small : Tapes 10 2) :=
  (setTape old (43:Fin 66) (small.tape 0) (small.head 0)).append (extras small)
def input (old : Tapes 66 2) (ws : List Word) (current target : ℕ) (ls : List Bool) :=
  install old (NativeSignedGapHeadersReturn.input ws current target ls)
def output (old : Tapes 66 2) (ws : List Word) (current target : ℕ) (ls : List Bool) :=
  install old (NativeSignedGapHeadersReturn.output ws current target ls)

private theorem active_install (old : Tapes 66 2) (small : Tapes 10 2) :
    Placement.active placement (install old small)=small := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [placement,InjectivePlacement.active_slot]
  all_goals fin_cases i <;> rfl

private theorem replace_install (old : Tapes 66 2) (small result : Tapes 10 2) :
    Placement.replace placement (install old small) result=install old result := by
  apply Placement.Tapes.ext' <;> intro i
  all_goals by_cases hi : ∃ j,slots j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [placement,InjectivePlacement.replace_head_slot]
    simpa only [Placement.active,placement,InjectivePlacement.active_slot] using
      congrArg (fun v => v.head j) (active_install old result).symm
  · rw [placement,InjectivePlacement.replace_head_other _ _ _ _ _ _ (by intro j he; exact hi ⟨j,he⟩)]
    unfold install
    have hb : i.val<66 := by
      by_contra h
      have hv : (66 : ℕ) ≤ i.val := by omega
      have hx : slots ⟨i.val-65,by have := i.isLt; omega⟩=i := by
        unfold slots
        simp only [show i.val-65≠0 by omega,ite_false]
        apply Fin.ext
        simp
        omega
      exact hi ⟨_,hx⟩
    have hn : i.val≠43 := by intro h; exact hi ⟨0,Fin.ext h.symm⟩
    simp [Tapes.append,Fin.addCases,hb,setTape,Fin.ext_iff,hn]
  · obtain ⟨j,rfl⟩ := hi
    rw [placement,InjectivePlacement.replace_tape_slot]
    simpa only [Placement.active,placement,InjectivePlacement.active_slot] using
      congrArg (fun v => v.tape j) (active_install old result).symm
  · rw [placement,InjectivePlacement.replace_tape_other _ _ _ _ _ _ (by intro j he; exact hi ⟨j,he⟩)]
    unfold install
    have hb : i.val<66 := by
      by_contra h
      have hv : (66 : ℕ) ≤ i.val := by omega
      have hx : slots ⟨i.val-65,by have := i.isLt; omega⟩=i := by
        unfold slots
        simp only [show i.val-65≠0 by omega,ite_false]
        apply Fin.ext
        simp
        omega
      exact hi ⟨_,hx⟩
    have hn : i.val≠43 := by intro h; exact hi ⟨0,Fin.ext h.symm⟩
    simp [Tapes.append,Fin.addCases,hb,setTape,Fin.ext_iff,hn]

theorem runs (old : Tapes 66 2) (ws : List Word) (current target : ℕ) (hle : target≤current)
    (hd : ∀ w∈ws,current-target≤w.length) (hn : ws≠[]) (ls : List Bool)
    (hlen : Counter.value ls=volume ws) (hl : GrowingCounterData.Canonical ls) :
    HoareTime program (fun v => v=input old ws current target ls)
      (fun v => v=output old ws current target ls) (cost ws current target) := by
  have h := NativeSignedGapHeadersReturn.runs_at placement (input old ws current target ls)
    ws current target hle hd hn ls hlen hl (active_install _ _)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  exact replace_install _ _ _

open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry CompactRecursiveDependencyBudget
open CompactSpectatorVisitGeometry (Array)
open CompactNativeReturnGapBudget (precision gap)
open NativeSignedReturnPrecision (fields)

private theorem field_le_volume (ws : List Word) (w : Word) (hw : w∈ws) : w.length≤volume ws := by
  induction ws with
  | nil => simp at hw
  | cons x xs ih =>
    simp only [List.mem_cons] at hw
    simp only [volume,NativeSignedReturnStream.encode_cons,List.length_append,
      DelimitedRadixRecord.field_length]
    rcases hw with rfl|hw
    · omega
    · have hh := ih hw
      unfold volume at hh
      omega

/-- Actual path budgets pay the generated gap and both precision descriptors;
there is no gap-times-stream-volume cost or supplied gap header. -/
theorem array_runs {left k levels frames returned : ℕ} (old : Tapes 66 2) (s : Shape)
    (path : Path s.active left k levels frames returned) (p C q g axes target rows ell : ℕ)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤s.chunk)
    (haxes : axes≤2*s.bits) (htarget : target≤precision p levels frames returned g axes)
    (f : Array s rows ell) (hw : CompactSpectatorInheritedGrid.Width s rows ell q f)
    (hrows : 0<rows) (ls : List Bool)
    (hlen : Counter.value ls=volume (fields (List.ofFn f))) (hl : GrowingCounterData.Canonical ls) :
    HoareTime program
      (fun v => v=input old (fields (List.ofFn f)) (precision p levels frames returned g axes) target ls)
      (fun v => v=output old (fields (List.ofFn f)) (precision p levels frames returned g axes) target ls)
      (137*volume (fields (List.ofFn f))+359) := by
  have hfield := CompactNativeReturnGapBudget.array_width s rows ell q f hw
  have hd := CompactNativeReturnGapBudget.gap_le_field s path p C q g axes target hC hp hchunk haxes
  have hfg : ∀ w∈fields (List.ofFn f),precision p levels frames returned g axes-target≤w.length := by
    intro w h
    obtain ⟨z,hz,hmem⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with rfl|rfl
    · rw [(hfield z hz).1]; exact hd
    · rw [(hfield z hz).2]; exact hd
  have hs : 0<ButterflySpectatorGeometry.Size rows s.bits (2^ell) :=
    Nat.mul_pos hrows (Nat.mul_pos (by positivity) (by positivity))
  have hc : f ⟨0,hs⟩∈List.ofFn f := List.mem_ofFn.mpr ⟨⟨0,hs⟩,rfl⟩
  have hm : (f ⟨0,hs⟩).1∈fields (List.ofFn f) := List.mem_flatMap.mpr ⟨_,hc,by simp⟩
  have hn : fields (List.ofFn f)≠[] := by intro he; rw [he] at hm; exact List.not_mem_nil hm
  have hb := CompactNativeReturnGapBudget.precision_le_half s path p C q g axes hC hp hchunk haxes
  have hv := field_le_volume _ _ hm
  rw [(hfield _ hc).1] at hv
  have hcost := NativeSignedGapHeadersReturn.cost_le (fields (List.ofFn f))
    (precision p levels frames returned g axes) target htarget
  apply (runs old _ _ target htarget hfg hn ls hlen hl).consequence (fun _ h => h) (fun _ h => h)
  omega

/-- Every native66 tape outside source43 remains literally unchanged. -/
theorem native_frame (old : Tapes 66 2) (small : Tapes 10 2) (i : Fin 66) (hi : i≠43) :
    (install old small).head (Fin.castAdd 9 i)=old.head i ∧
    (install old small).tape (Fin.castAdd 9 i)=old.tape i := by
  simp [install,Tapes.append,setTape,hi]

theorem array_input_source (old : Tapes 66 2) (s : Shape) (rows ell current target : ℕ)
    (f : Array s rows ell) (ls : List Bool) :
    (input old (fields (List.ofFn f)) current target ls).head 43=0 ∧
    (input old (fields (List.ofFn f)) current target ls).tape 43=CompactSpectatorLeafAxis.word f := by
  constructor
  · rfl
  · change NativeSignedGapReturn.word (fields (List.ofFn f))=CompactSpectatorLeafAxis.word f
    exact CompactNativeReturnGapBudget.array_serialization s rows ell f

theorem array_output_source {left k levels frames returned : ℕ} (old : Tapes 66 2) (s : Shape)
    (path : Path s.active left k levels frames returned) (p C q g axes target rows ell : ℕ)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤s.chunk)
    (haxes : axes≤2*s.bits) (f : Array s rows ell)
    (hw : CompactSpectatorInheritedGrid.Width s rows ell q f) (ls : List Bool) :
    (output old (fields (List.ofFn f)) (precision p levels frames returned g axes) target ls).tape 43=
      putWord (fun _ => blank) 0 ((NativeSignedReturnPrecision.returned (List.ofFn f)
        (gap p levels frames returned g axes target)).flatMap
          (fun c => DelimitedRadixRecord.complex c.1 c.2)) := by
  exact NativeSignedGapReturn.output_serialization (List.ofFn f) (CompactSpectatorInheritedGrid.half s q)
    (gap p levels frames returned g axes target)
    (CompactNativeReturnGapBudget.gap_le_field s path p C q g axes target hC hp hchunk haxes)
    (CompactNativeReturnGapBudget.array_width s rows ell q f hw)
    (RecursiveChildQuotientsConstant.bits (gap p levels frames returned g axes target)) ls

end
end IntegerMultBounds.Machine.CompactNativeGapHeadersReturn
