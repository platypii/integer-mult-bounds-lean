import IntegerMultBounds.Machine.BinaryCorrectionOffsetRow
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatPass

/-! Runtime-counted independent modular subtraction of packed row pairs.
The body re-enters the subtraction transducer at state zero on every row. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetLoop
open CountedCopyReuse (empty binary)
open BinaryCorrectionOffsetRow (diff)
noncomputable section

def left (rows : List (List Bool × List Bool)) := (rows.map Prod.fst).flatten
def right (rows : List (List Bool × List Bool)) := (rows.map Prod.snd).flatten
def result (rows : List (List Bool × List Bool)) := (rows.map (fun x => diff x.1 x.2)).flatten
def Uniform (W : ℕ) (rows : List (List Bool × List Bool)) := ∀ x ∈ rows, x.1.length=W ∧ x.2.length=W

theorem left_uniform (W : ℕ) (rows : List (List Bool × List Bool)) (hu : Uniform W rows) :
    BlockRotationData.Uniform W (rows.map Prod.fst) := by
  intro xs hx; obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hx; exact (hu pair hp).1

theorem right_uniform (W : ℕ) (rows : List (List Bool × List Bool)) (hu : Uniform W rows) :
    BlockRotationData.Uniform W (rows.map Prod.snd) := by
  intro xs hx; obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hx; exact (hu pair hp).2

theorem result_uniform (W : ℕ) (rows : List (List Bool × List Bool)) (hu : Uniform W rows) :
    BlockRotationData.Uniform W (rows.map (fun x => diff x.1 x.2)) := by
  intro xs hx; obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hx
  simp only [diff,ColumnTransducer.digits_length,List.length_zip,(hu pair hp).1,(hu pair hp).2,Nat.min_self]

theorem result_length (W : ℕ) (rows : List (List Bool × List Bool)) (hu : Uniform W rows) :
    (result rows).length=rows.length*W := by
  rw [result,BlockRotationData.uniform_volume W _ (result_uniform W rows hu),List.length_map]

def bank (f g out : ℤ → Fin 4) (p q r : ℤ) (ws ns : List Bool) :=
  CountedLoopReuse.bank (BinaryCorrectionOffsetRow.bank f g out (fun _ => blank) (fun _ => blank) p q r 0 0 ws)
    empty (binary ns) 1 1

def state (rows : List (List Bool × List Bool)) (W : ℕ) (f g out : ℤ → Fin 4)
    (p q r : ℤ) (ws : List Bool) (i : ℕ) :=
  BinaryCorrectionOffsetRow.bank (putWord f p ((left rows).map bitSymbol))
    (putWord g q ((right rows).map bitSymbol)) (putWord out r ((result (rows.take i)).map bitSymbol))
    (fun _ => blank) (fun _ => blank) (p+(i*W : ℕ)) (q+(i*W : ℕ)) (r+(i*W : ℕ)) 0 0 ws

theorem body_hoare (rows : List (List Bool × List Bool)) (W : ℕ) (hu : Uniform W rows)
    (f g out : ℤ → Fin 4) (p q r : ℤ) (ws : List Bool) (hw : Counter.value ws=W)
    (i : ℕ) (hi : i<rows.length) :
    HoareTime BinaryCorrectionOffsetRow.program (fun z => z=state rows W f g out p q r ws i)
      (fun z => z=state rows W f g out p q r ws (i+1)) (15*W+14*ws.length+46) := by
  have hp := hu rows[i] (List.getElem_mem hi)
  have hl := BinaryAddressOffsetRepeatPass.source_block (rows.map Prod.fst) W (left_uniform W rows hu) f p i (by simpa using hi)
  have hr := BinaryAddressOffsetRepeatPass.source_block (rows.map Prod.snd) W (right_uniform W rows hu) g q i (by simpa using hi)
  simp only [List.getElem_map] at hl hr
  have h := BinaryCorrectionOffsetRow.runs rows[i].1 rows[i].2 (hp.1.trans hp.2.symm)
    (putWord f p ((left rows).map bitSymbol)) (putWord g q ((right rows).map bitSymbol))
    (putWord out r ((result (rows.take i)).map bitSymbol)) (p+(i*W : ℕ)) (q+(i*W : ℕ)) (r+(i*W : ℕ))
    ws (hw.trans hp.1.symm)
  change putWord (putWord f p ((left rows).map bitSymbol)) (p+(i*W : ℕ)) (rows[i].1.map bitSymbol)=_ at hl
  change putWord (putWord g q ((right rows).map bitSymbol)) (q+(i*W : ℕ)) (rows[i].2.map bitSymbol)=_ at hr
  rw [hl,hr,hp.1] at h
  have hlen : (result (rows.take i)).length=i*W := by
    rw [result_length W _ (fun x hx => hu x (List.mem_of_mem_take hx)),List.length_take,Nat.min_eq_left (by omega)]
  have hout : putWord (putWord out r ((result (rows.take i)).map bitSymbol)) (r+(i*W : ℕ))
      ((diff rows[i].1 rows[i].2).map bitSymbol)=putWord out r ((result (rows.take (i+1))).map bitSymbol) := by
    have he : result (rows.take (i+1))=result (rows.take i)++diff rows[i].1 rows[i].2 := by
      rw [List.take_succ_eq_append_getElem hi]
      simp only [result,List.map_append,List.map_singleton,List.flatten_append,List.flatten_singleton]
    rw [he,List.map_append]
    simpa only [List.length_map,hlen] using putWord_append_forward out r
      ((result (rows.take i)).map bitSymbol) ((diff rows[i].1 rows[i].2).map bitSymbol)
  have hadd (s : ℤ) : s+(i*W : ℕ)+W=s+((i+1)*W : ℕ) := by push_cast; ring
  simpa only [state,left,right,hout,hadd] using h

def program := CountedLoopReuse.program BinaryCorrectionOffsetRow.program
def cost (W N : ℕ) (ws ns : List Bool) := N*(15*W+14*ws.length+52)+7*ns.length+16

theorem runs (rows : List (List Bool × List Bool)) (W : ℕ) (hu : Uniform W rows)
    (f g out : ℤ → Fin 4) (p q r : ℤ) (ws ns : List Bool)
    (hw : Counter.value ws=W) (hn : Counter.value ns=rows.length) :
    HoareTime program
      (fun z => z=bank (putWord f p ((left rows).map bitSymbol)) (putWord g q ((right rows).map bitSymbol)) out p q r ws ns)
      (fun z => z=bank (putWord f p ((left rows).map bitSymbol)) (putWord g q ((right rows).map bitSymbol))
        (putWord out r ((result rows).map bitSymbol)) (p+(rows.length*W : ℕ)) (q+(rows.length*W : ℕ))
        (r+(rows.length*W : ℕ)) ws ns) (cost W rows.length ws ns) := by
  have h := CountedLoopReuse.loop_hoare BinaryCorrectionOffsetRow.program ns rows.length
    (state rows W f g out p q r ws) (fun _ => 15*W+14*ws.length+46) hn
    (body_hoare rows W hu f g out p q r ws hw)
  apply h.consequence
  · intro z hz; simpa only [state,bank,List.take_zero,result,List.map_nil,List.flatten_nil,putWord,Nat.zero_mul,Nat.cast_zero,add_zero] using hz
  · intro z hz; simpa only [state,bank,List.take_length] using hz
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,cost]; nlinarith

end
end IntegerMultBounds.Machine.BinaryCorrectionOffsetLoop
