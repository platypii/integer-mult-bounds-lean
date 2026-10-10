import IntegerMultBounds.Machine.TwoTapeAt
import IntegerMultBounds.Machine.DelimitedRadixRecord
import IntegerMultBounds.Machine.ExactFrame

/-! A fixed finite list reads literal fields from separate retained role
streams. Original symbols are retained, each source head advances exactly past
its separator, and private destinations receive actual marked radix controls. -/
namespace IntegerMultBounds.Machine.RadixFieldReadList
noncomputable section
open SharedPlacementAlphabet (setTape)
open DelimitedRadixRecord (Context)
variable {t q : ℕ}

structure Instruction (t : ℕ) where
  source : Fin t
  dest : Fin t
  distinct : source≠dest

def Disjoint (ops : List (Instruction t)) : Prop :=
  ∀ a∈ops,∀ b∈ops,a.dest≠b.source

def write (op : Instruction t) (ctx : Fin t → Context q) (v : Tapes t q) :=
  TwoTapeAt.result v op.source op.dest (ctx op.source).tape
    (MarkedRadixRefresh.source (ctx op.source).re)
    ((ctx op.source).start+(ctx op.source).re.length+1) 1

def result : List (Instruction t) → (Fin t → Context q) → Tapes t q → Tapes t q
  | [],_,v => v
  | op::ops,ctx,v => result ops ctx (write op ctx v)

def states : List (Instruction t) → ℕ
  | [] => 1
  | _::ops => 6+states ops

def program (ht : 0<t) : (ops : List (Instruction t)) → Program t (states ops) q
  | [] => skip t q ht
  | op::ops => seq (TwoTapeAt.program DelimitedRadixRead.program op.source op.dest op.distinct)
      (program ht ops)

def cost (ops : List (Instruction t)) (ctx : Fin t → Context q) :=
  (ops.map (fun op => 2*(ctx op.source).re.length+7)).sum

theorem runs (ht : 0<t) (ops : List (Instruction t)) (hd : Disjoint ops)
    (hu : (ops.map Instruction.source).Nodup) (hv : (ops.map Instruction.dest).Nodup)
    (ctx : Fin t → Context q) (v : Tapes t q)
    (hs : ∀ op∈ops,v.tape op.source=(ctx op.source).tape ∧ v.head op.source=(ctx op.source).start)
    (hb : ∀ op∈ops,v.tape op.dest=(fun _ => blank) ∧ v.head op.dest=0) :
    HoareTime (program ht ops) (fun w => w=v) (fun w => w=result ops ctx v) (cost ops ctx) := by
  induction ops generalizing v with
  | nil => exact skip_hoare ht v
  | cons op ops ih =>
    have hsrc := hs op List.mem_cons_self
    have hblank := hb op List.mem_cons_self
    have h0 := TwoTapeAt.runs DelimitedRadixRead.program op.source op.dest op.distinct v
      _ _ _ _ _ _ _ _ hsrc hblank (DelimitedRadixRecord.read_real (ctx op.source))
    have hus := List.nodup_cons.mp hu
    have hvs := List.nodup_cons.mp hv
    have htail := ih (fun a ha b hb => hd a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      hus.2 hvs.2 (write op ctx v)
      (by
        intro a ha
        have hn : a.source≠op.source := fun he => hus.1 (List.mem_map.mpr ⟨a,ha,he⟩)
        have hm : a.source≠op.dest := (hd op List.mem_cons_self a (List.mem_cons_of_mem _ ha)).symm
        simpa only [write,TwoTapeAt.result,setTape,Function.update_of_ne hn,Function.update_of_ne hm]
          using hs a (List.mem_cons_of_mem _ ha))
      (by
        intro a ha
        have hn : a.dest≠op.dest := fun he => hvs.1 (List.mem_map.mpr ⟨a,ha,he⟩)
        have hm : a.dest≠op.source := hd a (List.mem_cons_of_mem _ ha) op List.mem_cons_self
        simpa only [write,TwoTapeAt.result,setTape,Function.update_of_ne hn,Function.update_of_ne hm]
          using hb a (List.mem_cons_of_mem _ ha))
    exact (h0.seq htail).consequence (fun _ h => h) (fun _ h => h)
      (by simp only [cost,List.map_cons,List.sum_cons]; omega)

theorem result_frame (ops : List (Instruction t)) (ctx : Fin t → Context q) (v : Tapes t q)
    (i : Fin t) (hi : ∀ op∈ops,i≠op.source ∧ i≠op.dest) :
    (result ops ctx v).head i=v.head i ∧ (result ops ctx v).tape i=v.tape i := by
  induction ops generalizing v with
  | nil => exact ⟨rfl,rfl⟩
  | cons op ops ih =>
    have h0 := hi op List.mem_cons_self
    simpa only [result,write,TwoTapeAt.result,setTape,Function.update_of_ne h0.1,
      Function.update_of_ne h0.2] using ih (write op ctx v) (fun a ha => hi a (List.mem_cons_of_mem _ ha))

theorem result_source (ops : List (Instruction t)) (hd : Disjoint ops)
    (hu : (ops.map Instruction.source).Nodup) (ctx : Fin t → Context q) (v : Tapes t q)
    (op : Instruction t) (hop : op∈ops) :
    (result ops ctx v).head op.source=(ctx op.source).start+(ctx op.source).re.length+1 ∧
      (result ops ctx v).tape op.source=(ctx op.source).tape := by
  induction ops generalizing v with
  | nil => exact (List.not_mem_nil hop).elim
  | cons a ops ih =>
    have hh := List.nodup_cons.mp hu
    rcases List.mem_cons.mp hop with rfl | hop
    · have hf := result_frame ops ctx (write op ctx v) op.source (by
        intro a ha
        refine ⟨?_,(hd a (List.mem_cons_of_mem _ ha) op List.mem_cons_self).symm⟩
        intro he
        exact hh.1 (List.mem_map.mpr ⟨a,ha,he.symm⟩))
      simpa only [result,write,TwoTapeAt.result,setTape,Function.update_of_ne op.distinct,
        Function.update_self] using hf
    · exact ih (fun a ha b hb => hd a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        hh.2 (write a ctx v) hop

theorem result_dest (ops : List (Instruction t)) (hd : Disjoint ops)
    (hu : (ops.map Instruction.dest).Nodup) (ctx : Fin t → Context q) (v : Tapes t q)
    (op : Instruction t) (hop : op∈ops) :
    (result ops ctx v).head op.dest=1 ∧
      (result ops ctx v).tape op.dest=MarkedRadixRefresh.source (ctx op.source).re := by
  induction ops generalizing v with
  | nil => exact (List.not_mem_nil hop).elim
  | cons a ops ih =>
    have hh := List.nodup_cons.mp hu
    rcases List.mem_cons.mp hop with rfl | hop
    · have hf := result_frame ops ctx (write op ctx v) op.dest (by
        intro a ha
        refine ⟨hd op List.mem_cons_self a (List.mem_cons_of_mem _ ha),?_⟩
        intro he
        exact hh.1 (List.mem_map.mpr ⟨a,ha,he.symm⟩))
      simpa only [result,write,TwoTapeAt.result,setTape,Function.update_self] using hf
    · exact ih (fun a ha b hb => hd a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        hh.2 (write a ctx v) hop

end
end IntegerMultBounds.Machine.RadixFieldReadList
