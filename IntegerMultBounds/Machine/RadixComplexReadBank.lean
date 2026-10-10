import IntegerMultBounds.Machine.RadixComplexReadList
import IntegerMultBounds.Machine.RawLinearCombination

/-! Both component readers operate on fixed retained role ports. The selected
private component bank receives actual source digits; all role symbols, the
other component bank, and the entire arithmetic/output tail are framed. -/
namespace IntegerMultBounds.Machine.RadixComplexReadBank
noncomputable section
open DelimitedRadixRecord (Context)
open RadixLinearCombinationRefresh (controls)
open RadixComplexReadList (Instruction field start)
variable {c u q : ℕ}

abbrev count (c u : ℕ) := c+(c+(c+u))
def source (i : Fin c) : Fin (count c u) := Fin.castAdd (c+(c+u)) i
def dest (imaginary : Bool) (i : Fin c) : Fin (count c u) :=
  if imaginary then Fin.natAdd c (Fin.natAdd c (Fin.castAdd u i))
    else Fin.natAdd c (Fin.castAdd (c+u) i)

theorem dest_val (imaginary : Bool) (i : Fin c) :
    (dest (u:=u) imaginary i).val=(if imaginary then 2*c else c)+i.val := by
  cases imaginary with
  | false => rfl
  | true => simp [dest]; omega

def instruction (imaginary : Bool) (i : Fin c) : Instruction (count c u) :=
  ⟨source i,dest imaginary i,by
    intro h
    have hv := congrArg Fin.val h
    rw [dest_val] at hv
    have := i.isLt
    dsimp [source] at hv
    cases imaginary <;> simp at hv <;> omega⟩

def instructions (imaginary : Bool) : List (Instruction (count c u)) :=
  List.ofFn (instruction imaginary)

theorem source_unique (imaginary : Bool) :
    ((instructions (c:=c) (u:=u) imaginary).map Instruction.source).Nodup := by
  rw [instructions,List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro i j h
  have hv := congrArg Fin.val h
  exact Fin.ext hv

theorem dest_unique (imaginary : Bool) :
    ((instructions (c:=c) (u:=u) imaginary).map Instruction.dest).Nodup := by
  rw [instructions,List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro i j h
  have hv := congrArg Fin.val h
  change (dest imaginary i).val=(dest imaginary j).val at hv
  rw [dest_val,dest_val] at hv
  exact Fin.ext (by omega)

theorem disjoint (imaginary : Bool) :
    RadixComplexReadList.Disjoint (instructions (c:=c) (u:=u) imaginary) := by
  intro a ha b hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  intro h
  have hv := congrArg Fin.val h
  change (dest imaginary i).val=j.val at hv
  rw [dest_val] at hv
  have := j.isLt
  cases imaginary <;> simp at hv <;> omega

def globalContext (hc : 0<c) (ctx : Fin c → Context q) : Fin (count c u) → Context q :=
  Fin.addCases ctx (fun _ => ctx ⟨0,hc⟩)

theorem context_source (hc : 0<c) (ctx : Fin c → Context q) (i : Fin c) :
    globalContext (u:=u) hc ctx (source i)=ctx i := by simp [globalContext,source]

def bank (ctx : Fin c → Context q) (positions : Fin c → ℤ) (real imag : Tapes c q) (tail : Tapes u q) :=
  (⟨positions,fun i => (ctx i).tape⟩ : Tapes c q).append (real.append (imag.append tail))

def input (imaginary : Bool) (ctx : Fin c → Context q) (other : Tapes c q) (tail : Tapes u q) :=
  bank ctx (fun i => start imaginary (ctx i))
    (if imaginary then other else RadixLinearCombinationBootstrap.empty c)
    (if imaginary then RadixLinearCombinationBootstrap.empty c else other) tail

def output (imaginary : Bool) (ctx : Fin c → Context q) (xs : ℕ → List (Fin q))
    (other : Tapes c q) (tail : Tapes u q) :=
  bank ctx (fun i => start imaginary (ctx i)+(field imaginary (ctx i)).length+1)
    (if imaginary then other else controls xs) (if imaginary then controls xs else other) tail

def program (hc : 0<c) (imaginary : Bool) :=
  RadixComplexReadList.program (q:=q) (by unfold count; omega : 0<count c u)
    (instructions (c:=c) (u:=u) imaginary)

private theorem result_frame (imaginary : Bool) (hc : 0<c) (ctx : Fin c → Context q)
    (v : Tapes (count c u) q) (i : Fin (count c u))
    (hi : ∀ j,i≠source j ∧ i≠dest imaginary j) :
    (RadixComplexReadList.result imaginary (instructions imaginary) (globalContext hc ctx) v).head i=v.head i ∧
      (RadixComplexReadList.result imaginary (instructions imaginary) (globalContext hc ctx) v).tape i=v.tape i := by
  apply RadixComplexReadList.result_frame
  intro op hop
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hop
  exact hi j

private theorem result_eq (imaginary : Bool) (hc : 0<c) (ctx : Fin c → Context q)
    (xs : ℕ → List (Fin q)) (hxs : ∀ i,field imaginary (ctx i)=xs i.val)
    (other : Tapes c q) (tail : Tapes u q) :
    RadixComplexReadList.result imaginary (instructions imaginary) (globalContext hc ctx)
      (input imaginary ctx other tail)=output imaginary ctx xs other tail := by
  have hsrc (i : Fin c) := RadixComplexReadList.result_source imaginary (instructions imaginary)
    (disjoint imaginary) (source_unique imaginary) (globalContext hc ctx)
    (input imaginary ctx other tail) (instruction imaginary i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hdst (i : Fin c) := RadixComplexReadList.result_dest imaginary (instructions imaginary)
    (disjoint imaginary) (dest_unique imaginary) (globalContext hc ctx)
    (input imaginary ctx other tail) (instruction imaginary i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  simp only [instruction,context_source,hxs] at hsrc hdst
  apply Placement.Tapes.ext'
  all_goals
    intro i
    induction i using Fin.addCases (m:=c) (n:=c+(c+u)) with
    | left i =>
      first
        | simpa only [output,bank,Tapes.append,Fin.addCases_left,source,hxs] using (hsrc i).1
        | simpa only [output,bank,Tapes.append,Fin.addCases_left,source] using (hsrc i).2
    | right i =>
      induction i using Fin.addCases (m:=c) (n:=c+u) with
      | left i =>
        cases imaginary with
        | false =>
          first
            | simpa only [dest,Bool.false_eq_true,ite_false,output,bank,Tapes.append,Fin.addCases_right,
                Fin.addCases_left,controls] using (hdst i).1
            | simpa only [dest,Bool.false_eq_true,ite_false,output,bank,Tapes.append,Fin.addCases_right,
                Fin.addCases_left,controls] using (hdst i).2
        | true =>
          have hf := result_frame true hc ctx (input true ctx other tail)
            (Fin.natAdd c (Fin.castAdd (c+u) i)) (by
              intro j
              constructor <;> intro h <;> have hv := congrArg Fin.val h
              · have := j.isLt; dsimp [source] at hv; omega
              · have := i.isLt; dsimp [dest] at hv; omega)
          first
            | simpa only [input,output,bank,ite_true,Tapes.append,Fin.addCases_right,Fin.addCases_left] using hf.1
            | simpa only [input,output,bank,ite_true,Tapes.append,Fin.addCases_right,Fin.addCases_left] using hf.2
      | right i =>
        induction i using Fin.addCases (m:=c) (n:=u) with
        | left i =>
          cases imaginary with
          | true =>
            first
              | simpa only [dest,ite_true,output,bank,Tapes.append,Fin.addCases_right,Fin.addCases_left,controls] using (hdst i).1
              | simpa only [dest,ite_true,output,bank,Tapes.append,Fin.addCases_right,Fin.addCases_left,controls] using (hdst i).2
          | false =>
            have hf := result_frame false hc ctx (input false ctx other tail)
              (Fin.natAdd c (Fin.natAdd c (Fin.castAdd u i))) (by
                intro j
                constructor <;> intro h <;> have hv := congrArg Fin.val h
                · have := j.isLt; dsimp [source] at hv; omega
                · have := j.isLt; dsimp [dest] at hv; omega)
            first
              | simpa only [input,output,bank,Bool.false_eq_true,ite_false,Tapes.append,Fin.addCases_right,Fin.addCases_left] using hf.1
              | simpa only [input,output,bank,Bool.false_eq_true,ite_false,Tapes.append,Fin.addCases_right,Fin.addCases_left] using hf.2
        | right i =>
          have hf := result_frame imaginary hc ctx (input imaginary ctx other tail)
            (Fin.natAdd c (Fin.natAdd c (Fin.natAdd c i))) (by
              intro j
              constructor <;> intro h <;> have hv := congrArg Fin.val h
              · have := j.isLt; dsimp [source] at hv; omega
              · rw [dest_val] at hv; have := j.isLt; cases imaginary <;> simp at hv <;> omega)
          first
            | simpa only [input,output,bank,Tapes.append,Fin.addCases_right] using hf.1
            | simpa only [input,output,bank,Tapes.append,Fin.addCases_right] using hf.2

theorem runs (imaginary : Bool) (hc : 0<c) (ctx : Fin c → Context q)
    (xs : ℕ → List (Fin q)) (hxs : ∀ i,field imaginary (ctx i)=xs i.val)
    (other : Tapes c q) (tail : Tapes u q) :
    HoareTime (program (q:=q) (u:=u) hc imaginary) (fun v => v=input imaginary ctx other tail)
      (fun v => v=output imaginary ctx xs other tail)
      (RadixComplexReadList.cost imaginary (instructions (u:=u) imaginary) (globalContext hc ctx)) := by
  have h := RadixComplexReadList.runs imaginary (by unfold count; omega : 0<count c u)
    (instructions imaginary) (disjoint imaginary) (source_unique imaginary) (dest_unique imaginary)
    (globalContext hc ctx) (input imaginary ctx other tail)
    (by
      intro op hop
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
      simp [instruction,globalContext,source,input,bank,Tapes.append])
    (by
      intro op hop
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
      cases imaginary <;> simp [instruction,dest,input,bank,RadixLinearCombinationBootstrap.empty,Tapes.append])
  exact h.consequence (fun _ h => h) (fun _ h => h.trans (result_eq imaginary hc ctx xs hxs other tail)) le_rfl

end
end IntegerMultBounds.Machine.RadixComplexReadBank
