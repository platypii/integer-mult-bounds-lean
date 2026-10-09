import IntegerMultBounds.Machine.CompactComplexRootPieceDigit
import IntegerMultBounds.Machine.CompactComplexRootPiecePrefixes
import IntegerMultBounds.Machine.BinaryDescriptorQueueRewind

/-! A fixed outer root controller consumes the generated low-to-high digit
queue, generates all canonical exponent/left/width triples and invokes one
fixed callback per root piece. Its finite table has no digit-list, root-path,
loop-count or descriptor input. The callback's native execution is an explicit
interface for the still-separate recursive machine. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceController
noncomputable section
open ActiveRepairRankHeadersCommands (State bank put)
open CompactComplexRecursiveGeometry (arity expandDigits)
open CompactComplexRootPieceVisits (preceding)
open CompactComplexRootPiecePrefixes (count)
open RecursiveChildQuotientsConstant (bits)
variable {a q t : ℕ}

def ready (st : State) (e left : ℕ) := put (put (put st 1 e) 2 left) 3 (arity^e)
def state (st : State) (ds : List ℕ) (k : ℕ) := ready st k (preceding (ds.take k))
def queue (ds : List ℕ) : ℤ → Fin (a+4) :=
  putWord (fun _ => blank) 1 (CompactComplexRootDigits.fields ds)
def cursor (ds : List ℕ) (k : ℕ) : ℤ := 1+((ds.take k).map (fun d => (bits d).length+1)).sum

private theorem cursor_eq (ds : List ℕ) (k : ℕ) :
    cursor ds k=1+(CompactComplexRootDigits.fields (a := a) (ds.take k)).length := by
  simp [cursor,CompactComplexRootDigits.fields]
def input (st : State) (ds : List ℕ) (k : ℕ) (native : Tapes t a) : Tapes (43+(1+t)) a :=
  CompactComplexRootPieceDigit.input (state st ds k) (queue ds) (cursor ds k) native

def test (sy : Fin (43+(1+t)) → Fin (a+4)) : Bool :=
  decide (sy (Fin.natAdd 43 (Fin.castAdd t (0 : Fin 1)))≠blank)
def program (callback : Program (43+(1+t)) q a) :=
  whileLoop (CompactComplexRootPieceDigit.body callback arity).2 (test (t := t))

private theorem fields_append (pre post : List ℕ) :
    CompactComplexRootDigits.fields (a := a) (pre++post)=
      CompactComplexRootDigits.fields pre++CompactComplexRootDigits.fields post := by
  simp [CompactComplexRootDigits.fields]

private theorem queue_split (ds : List ℕ) (k : ℕ) :
    queue (a := a) ds=putWord
      (putWord (fun _ => blank) 1 (CompactComplexRootDigits.fields (ds.take k)))
      (cursor ds k) (CompactComplexRootDigits.fields (ds.drop k)) := by
  rw [cursor_eq (a := a),putWord_append_forward,← fields_append,List.take_append_drop,queue]

private theorem cursor_step (ds : List ℕ) (k : ℕ) (hk : k<ds.length) :
    cursor ds (k+1)=cursor ds k+(bits ds[k]).length+1 := by
  simp only [cursor,List.take_succ_eq_append_getElem hk,List.map_append,List.map_singleton,
    List.sum_append,List.sum_singleton,Nat.cast_add,Nat.cast_one]
  ring

private theorem queue_read (ds : List ℕ) (k : ℕ) :
    (input st ds k native).reads (Fin.natAdd 43 (Fin.castAdd t (0 : Fin 1)))=queue (a := a) ds (cursor ds k) := by
  simp only [input,CompactComplexRootPieceDigit.input,Tapes.reads,Tapes.append,
    Fin.addCases_right,Fin.addCases_left]
  rfl

private theorem field_tail (ds : List ℕ) (k : ℕ) (hk : k<ds.length) :
    ds.drop k=ds[k]::ds.drop (k+1) := List.drop_eq_getElem_cons hk

private theorem test_before (st : State) (ds : List ℕ) (k : ℕ)
    (native : Tapes t a) (hk : k<ds.length) : test (input st ds k native).reads=true := by
  unfold test
  rw [queue_read]
  have hl : (CompactComplexRootDigits.fields (a := a) (ds.take k)).length<
      (CompactComplexRootDigits.fields (a := a) ds).length := by
    have he := congrArg (fun d => (CompactComplexRootDigits.fields (a := a) d).length) (List.take_append_drop k ds)
    rw [fields_append,field_tail ds k hk] at he
    simp only [List.length_append] at he
    have hpos : 0<(CompactComplexRootDigits.fields (a := a) (ds[k]::ds.drop (k+1))).length := by
      change 0<(((bits ds[k]).map (bitSymbol (a := a))++[separator])++
        CompactComplexRootDigits.fields (ds.drop (k+1))).length
      simp only [List.length_append,List.length_map,List.length_singleton]
      omega
    omega
  have hm := ReturnOrigin.putWord_mem (fun _ => blank) 1 (CompactComplexRootDigits.fields (a := a) ds)
    (cursor ds k) (by rw [cursor_eq (a := a)]; constructor <;> omega)
  have hn := BinaryDescriptorQueueRewind.fields_nonblank ds _ hm
  simp only [decide_eq_true_eq]
  exact hn

private theorem test_end (st : State) (ds : List ℕ) (native : Tapes t a) :
    test (input st ds ds.length native).reads=false := by
  unfold test
  rw [queue_read]
  have he : queue (a := a) ds (cursor ds ds.length)=blank := by
    unfold queue
    rw [cursor_eq (a := a),List.take_length]
    exact putWord_outside _ _ _ _ (Or.inr (by omega))
  rw [he]
  simp

private theorem state_next (st : State) (ds : List ℕ) (k : ℕ) (hk : k<ds.length) :
    CompactComplexRootPieceDigit.finished (state st ds k) k (preceding (ds.take k))
      (arity^k) ds[k] arity=state st ds (k+1) := by
  unfold state
  rw [CompactComplexRootPiecePrefixes.left_step ds k hk]
  unfold ready CompactComplexRootPieceDigit.finished
  rw [pow_succ]
  funext i
  by_cases h1 : i=1
  · subst i; simp [put,Function.update]
  by_cases h2 : i=2
  · subst i; simp [put,Function.update]
  by_cases h3 : i=3
  · subst i; simp [put,Function.update]
  simp [put,Function.update,h1,h2,h3]

def bodyCost (st : State) (ds : List ℕ) (k : Fin ds.length) (callCost : ℕ → ℕ → ℕ) :=
  CompactComplexRootPieceDigit.digitCost (state st ds k.val) (preceding (ds.take k.val))
    (arity^k.val) ds[k.val] arity (callCost k.val)

/-- Every outer test is physical; the callback receives exactly the generated
canonical root numeric fields. All native/controller data is propagated by its paid
contract, while every generated clock is erased before the next field. -/
theorem runs (callback : Program (43+(1+t)) q a) (st : State) (ds : List ℕ)
    (h4 : st 4=none) (h22 : st 22=none) (h23 : st 23=none) (h24 : st 24=none)
    (native : ℕ → Tapes t a) (callCost : ℕ → ℕ → ℕ)
    (hc : ∀ k (hk : k<ds.length), ∀ j<ds[k], HoareTime callback
      (fun v => v=CompactComplexRootPieceClock.input (state st ds k)
        (preceding (ds.take k)+j*arity^k) (ds[k]-j)
        (FiniteReturnStack.bank (queue ds) (cursor ds (k+1))) (native (count (ds.take k)+j)))
      (fun v => v=CompactComplexRootPieceClock.input (state st ds k)
        (preceding (ds.take k)+j*arity^k) (ds[k]-j)
        (FiniteReturnStack.bank (queue ds) (cursor ds (k+1))) (native (count (ds.take k)+j+1)))
      (callCost k j)) :
    HoareTime (program callback)
      (fun v => v=input st ds 0 (native 0))
      (fun v => v=input st ds ds.length (native (count ds)))
      (∑ k : Fin ds.length, (bodyCost st ds k callCost+2)) := by
  let X := fun k => input (a := a) st ds k (native (count (ds.take k)))
  let costs := fun k => if hk : k<ds.length then bodyCost st ds ⟨k,hk⟩ callCost else 0
  have hb : ∀ k<ds.length, HoareTime (CompactComplexRootPieceDigit.body callback arity).2
      (fun v => v=X k) (fun v => v=X (k+1)) (costs k) := by
    intro k hk
    let pre := putWord (fun _ => blank) 1 (CompactComplexRootDigits.fields (a := a) (ds.take k))
    have hq : putWord pre (cursor ds k) (CompactComplexRootDigits.fields (ds[k]::ds.drop (k+1)))=queue ds := by
      rw [← field_tail ds k hk,← queue_split ds k]
    have hr := CompactComplexRootPieceDigit.runs callback arity (by decide)
      (state st ds k) k (preceding (ds.take k)) (arity^k) ds[k]
      (by simp [state,ready,put]) (by simp [state,ready,put]) (by simp [state,ready,put])
      (by simp [state,ready,put,h4]) (by simp [state,ready,put,h22])
      (by simp [state,ready,put,h23]) (by simp [state,ready,put,h24])
      pre (cursor ds k) (ds.drop (k+1)) (fun j => native (count (ds.take k)+j)) (callCost k)
      (by
        intro j hj
        simpa only [hq,← cursor_step ds k hk,Nat.add_assoc] using hc k hk j hj)
    rw [hq,← cursor_step ds k hk,state_next st ds k hk] at hr
    have hn := CompactComplexRootPiecePrefixes.count_step ds k hk
    simpa only [X,input,costs,dite_eq_left hk,bodyCost,Fin.val_mk,Nat.add_zero,hn] using hr
  have ht := while_chain_hoare (CompactComplexRootPieceDigit.body callback arity).2 (test (t := t)) X costs ds.length
    hb (fun k hk => test_before st ds k _ hk) (test_end st ds _)
  have hs : (∑ k ∈ Finset.range ds.length, (costs k+2))=
      ∑ k : Fin ds.length, (bodyCost st ds k callCost+2) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simp [costs,k.isLt]
  simpa only [program,X,List.take_zero,List.take_length,count,expandDigits,List.length_nil,hs] using ht

/-- The generated initial root shape is exactly the paid seed program's output. -/
theorem state_zero (st : State) (ds : List ℕ) :
    state st ds 0=CompactComplexRootPieceNumbers.seeded st := by
  simp [state,ready,preceding,expandDigits,CompactComplexRootPieceNumbers.seeded]

/-- Every generated callback location is a literal canonical root Visit of
its original active-prefix header. -/
theorem visit_at (active k j : ℕ) (hk : k<(Nat.digits arity active).length)
    (hj : j<(Nat.digits arity active)[k]) :
    CompactComplexRecursiveGeometry.Visit active
      (preceding ((Nat.digits arity active).take k)+j*arity^k) k := by
  let ds := Nat.digits arity active
  have hd : ds=ds.take k++ds[k]::ds.drop (k+1) := by
    rw [← field_tail ds k hk,List.take_append_drop]
  have hv := CompactComplexRootPieceVisits.generated_visit active (ds.take k)
    (ds.drop (k+1)) ds[k] j hd hj
  have hl : min k ds.length=k := Nat.min_eq_left (Nat.le_of_lt hk)
  simpa only [List.length_take,hl] using hv

/-- The generated root boundaries exhaust exactly the original active count. -/
theorem final_left (active : ℕ) : preceding (Nat.digits arity active)=active := by
  simpa only [preceding,CompactComplexRecursiveGeometry.widths,
    CompactComplexRecursiveGeometry.exponents] using CompactComplexRecursiveGeometry.widths_sum active

end
end IntegerMultBounds.Machine.CompactComplexRootPieceController
