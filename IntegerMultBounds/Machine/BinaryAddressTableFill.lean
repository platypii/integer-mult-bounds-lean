import IntegerMultBounds.Machine.BinaryAddressTableStep
import IntegerMultBounds.Machine.FixedBasePowerDescriptor

/-! Physical initialization of a fixed-width zero counter from its original
binary width descriptor. The mutable loop clock starts and returns blank. -/
namespace IntegerMultBounds.Machine.BinaryAddressTableFill
open CountedCopyReuse (empty binary)
open SharedPlacementAlphabet (setTape)
open BinaryAddressTableStep (bits_word binary_word)
noncomputable section

def write : Program 1 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun st _ => if st=0 then some (1,fun _ => (bitSymbol false,.right)) else none

def filled (n : ℕ) : Tapes 1 0 :=
  ⟨fun _ => 1+n,fun _ => binary (List.replicate n false)⟩

theorem write_hoare (n : ℕ) : HoareTime write
    (fun z => z=filled n) (fun z => z=filled (n+1)) 1 := by
  have he : Function.update (binary (List.replicate n false)) (1+n) (bitSymbol false) =
      binary (List.replicate (n+1) false) := by
    rw [List.replicate_add,List.replicate_one]
    simp only [binary,bits_word,List.map_append,List.map_replicate,List.map_cons,List.map_nil]
    simpa only [List.length_replicate,putWord] using
      putWord_append_forward empty 1 (List.replicate n (bitSymbol false)) [bitSymbol false]
  rintro z rfl
  refine ⟨1,⟨1,(filled (n+1)).head,(filled (n+1)).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,write,Tapes.start,ite_true,filled,Move.offset]
    congr 1
    congr 1
    funext i z
    simpa only [Function.update_apply] using congrFun he z
  · simp [step,write]

def oneInit (slot : Fin 3) := Placement.placed (RecursiveChildQuotientsConstant.program (a := 0) 0)
  (FiniteReturnStackAt.placement slot)
def setup := seq (oneInit 0) (oneInit 1)
def loop := CountedLoopReuse.program write
def rewind := extend (MarkedControlStreamReset.rewind (a := 0)) 2
def cleanup := BinaryDescriptorCleanupList.oneProgram (a := 0) (1 : Fin 3)
def program := seq (seq (seq setup loop) rewind) cleanup

def input (ws : List Bool) : Tapes 3 0 :=
  ⟨![0,0,1],![(fun _ => blank),(fun _ => blank),binary ws]⟩
def ready (ws : List Bool) (n : ℕ) :=
  CountedLoopReuse.bank (filled n) empty (binary ws) 1 1
def output (ws : List Bool) (w : ℕ) : Tapes 3 0 :=
  ⟨![1,0,1],![binary (List.replicate w false),(fun _ => blank),binary ws]⟩

theorem initializes (slot : Fin 3) (v : Tapes 3 0) (ht : v.tape slot=fun _ => blank) (hh : v.head slot=0) :
    HoareTime (oneInit slot) (fun z => z=v) (fun z => z=setTape v slot empty 1) 6 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := 0) 0)
    (FiniteReturnStackAt.placement slot) v (by rw [FiniteReturnStackAt.active_bank,ht,hh])
  apply h.consequence (fun _ h => h) _ (by decide)
  rintro z ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem setup_hoare (ws : List Bool) : HoareTime setup
    (fun z => z=input ws) (fun z => z=ready ws 0) 13 := by
  have h0  := initializes 0 (input ws) rfl rfl
  have h1  := initializes 1 (setTape (input ws) 0 empty 1) rfl rfl
  have he : setTape (setTape (input ws) 0 empty 1) 1 empty 1=ready ws 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h1
  exact h0.seq h1

theorem runs (ws : List Bool) (w : ℕ) (hw : Counter.value ws=w) :
    HoareTime program (fun z => z=input ws) (fun z => z=output ws w)
      (8*w+7*ws.length+39) := by
  have hl := CountedLoopReuse.loop_hoare write ws w filled (fun _ => 1) hw (fun i _ => write_hoare i)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one] at hl
  have hr := hoare_extend_eq (MarkedControlStreamReset.rewinds
    ((List.replicate w false).map (bitSymbol (a := 0)))
    (by intro x hx; obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx; cases b <;> decide))
    (CountedLoopReuse.controls empty (binary ws) 1 1)
  simp only [List.length_map,List.length_replicate,←binary_word] at hr
  let v : Tapes 3 0 := ⟨![1,1,1],![binary (List.replicate w false),empty,binary ws]⟩
  have he' : (MarkedWordCleanup.one (binary (List.replicate w false)) 1).append
      (CountedLoopReuse.controls empty (binary ws) 1 1) = v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he'] at hr
  have hr' : HoareTime rewind (fun z => z=ready ws w) (fun z => z=v) (w+3) := hr
  have hc := BinaryDescriptorCleanupList.one_hoare (1 : Fin 3) v [] rfl rfl
  have he : setTape v 1 (fun _ => blank) 0=output ws w := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at hc
  exact ((((setup_hoare ws).seq hl).seq hr').seq hc).consequence
    (fun _ h => h) (fun _ h => h) (by simp only [List.length_nil]; omega)

end
end IntegerMultBounds.Machine.BinaryAddressTableFill
