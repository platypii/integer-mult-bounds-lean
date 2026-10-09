import IntegerMultBounds.Machine.BinaryParityXorOffsetRow
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatPass

/-! Counted rowwise modular negation with a fresh two's-complement state for
each row; the runtime width determines the copied blank-backed boundary. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetLoop
open CountedCopyReuse (empty binary)
open TwosComplement (negWord)
noncomputable section

def result (blocks : List (List Bool)) := (blocks.map negWord).flatten

theorem result_length (W : ℕ) (blocks : List (List Bool)) (hu : BlockRotationData.Uniform W blocks) :
    (result blocks).length=blocks.length*W := by
  rw [result,BlockRotationData.uniform_volume W _ (by
    intro xs hx; obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx; rw [TwosComplement.negWord_length,hu ys hy]),List.length_map]

def bank (f g : ℤ → Fin 4) (p q : ℤ) (ws ns : List Bool) :=
  CountedLoopReuse.bank (BinaryParityXorOffsetRow.bank f g (fun _ => blank) p q 0 ws) empty (binary ns) 1 1

def state (blocks : List (List Bool)) (W : ℕ) (f g : ℤ → Fin 4) (p q : ℤ) (ws : List Bool) (i : ℕ) :=
  BinaryParityXorOffsetRow.bank (putWord f p (blocks.flatten.map bitSymbol))
    (putWord g q ((result (blocks.take i)).map bitSymbol)) (fun _ => blank) (p+(i*W : ℕ)) (q+(i*W : ℕ)) 0 ws

theorem body_hoare (blocks : List (List Bool)) (W : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (f g : ℤ → Fin 4) (p q : ℤ) (ws : List Bool) (hw : Counter.value ws=W) (i : ℕ) (hi : i<blocks.length) :
    HoareTime BinaryParityXorOffsetRow.program (fun z => z=state blocks W f g p q ws i)
      (fun z => z=state blocks W f g p q ws (i+1)) (12*W+7*ws.length+31) := by
  have hl := hu blocks[i] (List.getElem_mem hi)
  have h := BinaryParityXorOffsetRow.runs blocks[i] (putWord f p (blocks.flatten.map bitSymbol))
    (putWord g q ((result (blocks.take i)).map bitSymbol)) (p+(i*W : ℕ)) (q+(i*W : ℕ)) ws (hw.trans hl.symm)
  rw [BinaryAddressOffsetRepeatPass.source_block blocks W hu f p i hi,hl] at h
  have hlen : (result (blocks.take i)).length=i*W := by
    rw [result_length W _ (fun xs hx => hu xs (List.mem_of_mem_take hx)),List.length_take,Nat.min_eq_left (by omega)]
  have hout : putWord (putWord g q ((result (blocks.take i)).map bitSymbol)) (q+(i*W : ℕ))
      ((negWord blocks[i]).map bitSymbol)=putWord g q ((result (blocks.take (i+1))).map bitSymbol) := by
    have he : result (blocks.take (i+1))=result (blocks.take i)++negWord blocks[i] := by
      rw [List.take_succ_eq_append_getElem hi]
      simp only [result,List.map_append,List.map_singleton,List.flatten_append,List.flatten_singleton]
    rw [he,List.map_append]
    simpa only [List.length_map,hlen] using putWord_append_forward g q
      ((result (blocks.take i)).map bitSymbol) ((negWord blocks[i]).map bitSymbol)
  have hadd (r : ℤ) : r+(i*W : ℕ)+W=r+((i+1)*W : ℕ) := by push_cast; ring
  simpa only [state,hout,hadd] using h

def program := CountedLoopReuse.program BinaryParityXorOffsetRow.program
def cost (W N : ℕ) (ws ns : List Bool) := N*(12*W+7*ws.length+37)+7*ns.length+16

theorem runs (blocks : List (List Bool)) (W : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (f g : ℤ → Fin 4) (p q : ℤ) (ws ns : List Bool) (hw : Counter.value ws=W) (hn : Counter.value ns=blocks.length) :
    HoareTime program (fun z => z=bank (putWord f p (blocks.flatten.map bitSymbol)) g p q ws ns)
      (fun z => z=bank (putWord f p (blocks.flatten.map bitSymbol)) (putWord g q ((result blocks).map bitSymbol))
        (p+(blocks.length*W : ℕ)) (q+(blocks.length*W : ℕ)) ws ns) (cost W blocks.length ws ns) := by
  have h := CountedLoopReuse.loop_hoare BinaryParityXorOffsetRow.program ns blocks.length
    (state blocks W f g p q ws) (fun _ => 12*W+7*ws.length+31) hn (body_hoare blocks W hu f g p q ws hw)
  apply h.consequence
  · intro z hz; simpa only [state,bank,List.take_zero,result,List.map_nil,List.flatten_nil,putWord,Nat.zero_mul,Nat.cast_zero,add_zero] using hz
  · intro z hz; simpa only [state,bank,List.take_length] using hz
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,cost]; nlinarith

end
end IntegerMultBounds.Machine.BinaryParityXorOffsetLoop
