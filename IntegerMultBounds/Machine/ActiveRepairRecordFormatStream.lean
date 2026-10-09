import IntegerMultBounds.Machine.ActiveRepairRecordFormatWords

/-! Entire raw-array formatter: an outer runtime record count drives the
fixed record producer, whose independent runtime width count copies payloads.
Both clocks are copied, decremented and restored by real amortized machines. -/
namespace IntegerMultBounds.Machine.ActiveRepairRecordFormatStream
noncomputable section
open ActiveRepairRecordFormatWords

def stage (source dest : ℤ → Fin 4) (p q : ℤ) (chunks : List (List Bool)) (bs : List Bool) (i : ℕ) :=
  CountedCopyReuse.bank (putWord source p (raw chunks)) (putWord dest q (encoded (chunks.take i)))
    CountedCopyReuse.empty (CountedCopyReuse.binary bs)
    (p+(raw (chunks.take i)).length) (q+(encoded (chunks.take i)).length) 1 1

def program := CountedLoopReuseAlphabet.program ActiveRepairRecordFormatRecord.program

theorem body (source dest : ℤ → Fin 4) (p q : ℤ) (chunks : List (List Bool)) (bs : List Bool)
    (R i : ℕ) (hi : i<chunks.length) (hw : ∀ xs ∈ chunks,xs.length=R) (hbs : Counter.value bs=R) :
    HoareTime ActiveRepairRecordFormatRecord.program
      (fun v => v=stage source dest p q chunks bs i)
      (fun v => v=stage source dest p q chunks bs (i+1)) (5*R+7*bs.length+20) := by
  have hlen : chunks[i].length=R := hw _ (List.getElem_mem hi)
  have hsource : putWord (putWord source p (raw chunks)) (p+(raw (chunks.take i)).length)
      (chunks[i].map bitSymbol)=putWord source p (raw chunks) := by
    rw [raw_decompose chunks i hi]
    exact segment_self _ _ _ _ _
  have hh := ActiveRepairRecordFormatRecord.runs (putWord source p (raw chunks))
    (putWord dest q (encoded (chunks.take i)))
    (p+(raw (chunks.take i)).length) (q+(encoded (chunks.take i)).length)
    chunks[i] bs (hbs.trans hlen.symm)
  rw [hsource,hlen] at hh
  have hout : putWord (putWord dest q (encoded (chunks.take i)))
      (q+(encoded (chunks.take i)).length) (Partition.recordWord false chunks[i])=
      putWord dest q (encoded (chunks.take (i+1))) := by
    rw [putWord_append_forward,encoded_take_succ chunks i hi]
  rw [hout] at hh
  have hrlen : (raw (chunks.take (i+1))).length=(raw (chunks.take i)).length+R := by
    rw [raw_take_succ chunks i hi,List.length_append,List.length_map,hlen]
  have helen : (encoded (chunks.take (i+1))).length=(encoded (chunks.take i)).length+R+2 := by
    rw [encoded_take_succ chunks i hi]
    simp only [List.length_append,Partition.recordWord,List.length_cons,List.length_map,List.length_nil]
    rw [hlen]
    omega
  unfold stage
  simpa only [hrlen,helen,Nat.cast_add,Nat.cast_ofNat,add_assoc] using hh

theorem runs (source dest : ℤ → Fin 4) (p q : ℤ) (chunks : List (List Bool)) (bs ns : List Bool)
    (R : ℕ) (hw : ∀ xs ∈ chunks,xs.length=R) (hbs : Counter.value bs=R)
    (hns : Counter.value ns=chunks.length) :
    HoareTime program
      (fun v => v=CountedLoopReuseAlphabet.bank (stage source dest p q chunks bs 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v=CountedLoopReuseAlphabet.bank (stage source dest p q chunks bs chunks.length)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (chunks.length*(5*R+7*bs.length+26)+7*ns.length+16) := by
  have h := CountedLoopReuseAlphabet.loop_hoare ActiveRepairRecordFormatRecord.program ns chunks.length
    (stage source dest p q chunks bs) (fun _ => 5*R+7*bs.length+20) hns
    (fun i hi => body source dest p q chunks bs R i hi hw hbs)
  refine h.consequence (fun _ h => h) (fun _ h => h) ?_
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  nlinarith

end
end IntegerMultBounds.Machine.ActiveRepairRecordFormatStream
