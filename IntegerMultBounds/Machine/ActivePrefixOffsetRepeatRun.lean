import IntegerMultBounds.Machine.CountedControlWordRepeat
import IntegerMultBounds.Machine.Branch

/-! Repeat a physically present generated offset word for an arbitrary original
row count. The empty-source branch avoids iterating over zero-length rows;
no power-of-two condition is imposed on the runtime repetition descriptor. -/
namespace IntegerMultBounds.Machine.ActivePrefixOffsetRepeatRun
noncomputable section
open BinaryAddressOffsetRepeatData (copies)

def input (xs : List Bool) (rs : List Bool) := CountedControlWordRepeat.input xs (fun _ => blank) 0 rs
def output (xs : List Bool) (rs : List Bool) (rows : ℕ) := CountedControlWordRepeat.output xs (fun _ => blank) 0 rs rows

def emptyTest (sy : Fin 4 → Fin 4) : Bool := sy 0=blank

def program := branch emptyTest (skip 4 0 (by decide)) CountedControlWordRepeat.program

def cost (xs rs : List Bool) (rows : ℕ) := if xs=[] then 1 else rows*(3*xs.length+9)+7*rs.length+32

theorem copies_replicate (xs : List Bool) (rows : ℕ) : copies xs rows=(List.replicate rows xs).flatten := by
  induction rows with
  | zero => rfl
  | succ rows ih => simp [copies,List.replicate_add,ih]

theorem copies_nil (rows : ℕ) : copies ([] : List Bool) rows=[] := by
  rw [copies_replicate]
  simp

theorem test_empty (xs rs : List Bool) : emptyTest (input xs rs).reads=true ↔ xs=[] := by
  cases xs with
  | nil => simp [emptyTest,input,CountedControlWordRepeat.input,
      BinaryAddressOffsetRepeatCopy.bank,Tapes.reads,Copy.tapes,Copy.cfg,Config.tapes,Tapes.append,Fin.addCases,putWord,blank]
           rfl
  | cons b xs => cases b <;> simp [emptyTest,input,CountedControlWordRepeat.input,
      BinaryAddressOffsetRepeatCopy.bank,Tapes.reads,Copy.tapes,Copy.cfg,Config.tapes,Tapes.append,Fin.addCases,putWord_head,
      List.map_cons,bitSymbol,blank]

theorem runs (xs rs : List Bool) (rows : ℕ) (hv : Counter.value rs=rows) :
    HoareTime program (fun v => v=input xs rs) (fun v => v=output xs rs rows) (cost xs rs rows) := by
  by_cases hx : xs=[]
  · subst xs
    have he : output [] rs rows=input [] rs := by
      simp [output,input,CountedControlWordRepeat.output,copies_nil,putWord]
    rw [he]
    have ht := (test_empty [] rs).2 rfl
    have h := branch_hoare emptyTest
      ((skip_hoare (a := 0) (by decide : 0<4) (input [] rs)).consequence (fun _ h => h.1) (fun _ h => h) le_rfl)
      (show HoareTime CountedControlWordRepeat.program
        (fun v => v=input [] rs ∧ emptyTest v.reads=false) (fun v => v=input [] rs) 0 from by
          rintro v ⟨rfl,hv⟩; simp [ht] at hv)
    simpa [program,cost] using h
  · have ht : emptyTest (input xs rs).reads=false := by
      cases h : emptyTest (input xs rs).reads with
      | false => rfl
      | true => exact (hx ((test_empty xs rs).1 h)).elim
    have hr := CountedControlWordRepeat.runs xs (fun _ => blank) 0 rs rows hv rfl
    have h := branch_hoare emptyTest
      (show HoareTime (skip 4 0 (by decide))
        (fun v => v=input xs rs ∧ emptyTest v.reads=true) (fun v => v=output xs rs rows) 0 from by
          rintro v ⟨rfl,hv⟩; simp [ht] at hv)
      (hr.consequence (fun _ h => h.1) (fun _ h => h) le_rfl)
    refine h.consequence (fun _ h => h) (fun _ h => h) ?_
    simp only [cost,hx,ite_false,Nat.zero_max]
    omega

theorem cost_bound (xs rs : List Bool) (rows : ℕ) (hv : Counter.value rs=rows)
    (hc : GrowingCounterData.Canonical rs) : cost xs rs rows≤54*(rows*xs.length+1) := by
  by_cases hx : xs=[]
  · simp [cost,hx]
  · have hlen : 1≤xs.length := by cases xs <;> simp_all
    have hr := GrowingCounterData.canonical_width rs hc
    rw [hv] at hr
    have hl := Nat.log2_le_self rows
    have hrows : rows≤rows*xs.length := Nat.le_mul_of_pos_right _ hlen
    simp only [cost,hx,ite_false]
    nlinarith

theorem runs_linear (xs rs : List Bool) (rows : ℕ) (hv : Counter.value rs=rows)
    (hc : GrowingCounterData.Canonical rs) :
    HoareTime program (fun v => v=input xs rs) (fun v => v=output xs rs rows) (54*(rows*xs.length+1)) :=
  (runs xs rs rows hv).consequence (fun _ h => h) (fun _ h => h) (cost_bound xs rs rows hv hc)

end
end IntegerMultBounds.Machine.ActivePrefixOffsetRepeatRun
