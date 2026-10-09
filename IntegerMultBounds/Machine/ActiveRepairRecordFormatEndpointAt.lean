import IntegerMultBounds.Machine.ActiveRepairRecordFormatStream
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.ReturnOrigin

namespace IntegerMultBounds.Machine.ActiveRepairRecordFormatEndpointAt
noncomputable section
open SharedPlacementAlphabet

def one (f : ℤ → Fin 4) (p : ℤ) : Tapes 1 0 := ⟨fun _ => p,fun _ => f⟩
def mark : Program 1 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s _ => if s=0 then some (1,fun _ => (separator,.right)) else none

 theorem marks : HoareTime mark (fun v => v=one (fun _ => blank) 0)
    (fun v => v=one CountedCopyReuse.empty 1) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,fun _ => 1,fun _ => CountedCopyReuse.empty⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,mark,Tapes.start,one,ite_true,Move.offset]
    congr 1
  · simp [step,mark]

def atProgram {q : ℕ} (M : Program 1 q 0) (i : Fin 6) := Placement.placed M (FiniteReturnStackAt.placement i)
 theorem at_runs {q B : ℕ} (M : Program 1 q 0) (v : Tapes 6 0) (i : Fin 6)
    (f g : ℤ → Fin 4) (p r : ℤ) (ht : v.tape i=f) (hp : v.head i=p)
    (h0 : HoareTime M (fun w => w=one f p) (fun w => w=one g r) B) :
    HoareTime (atProgram M i) (fun w => w=v) (fun w => w=setTape v i g r) B := by
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement i) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hp]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]

end
end IntegerMultBounds.Machine.ActiveRepairRecordFormatEndpointAt
