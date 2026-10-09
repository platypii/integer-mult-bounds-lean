import IntegerMultBounds.Machine.CountedCopyReuse
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.Partition
import IntegerMultBounds.Machine.Gather

/-! Runtime-width formatting of one raw binary payload. Two fixed output
symbols enclose an amortized binary-counted copy, preserving the raw source
and width descriptor and restoring the reusable clock. -/
namespace IntegerMultBounds.Machine.ActiveRepairRecordFormatRecord
noncomputable section
open CountedCopyReuse (bank empty binary)

def write (symbol : Fin 4) : Program 4 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s=0 then some
    (1,fun i => if i=1 then (symbol,.right) else (symbols i,.stay)) else none

theorem writes (symbol : Fin 4) (source dest clock desc : ℤ → Fin 4) (p q r u : ℤ) :
    HoareTime (write symbol) (fun v => v=bank source dest clock desc p q r u)
      (fun v => v=bank source (Function.update dest q symbol) clock desc p (q+1) r u) 1 := by
  rintro v rfl
  let w := bank source (Function.update dest q symbol) clock desc p (q+1) r u
  refine ⟨1,⟨1,w.head,w.tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,write,Tapes.start,ite_true,Move.offset]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [w,bank]
    · funext i j
      fin_cases i <;> simp [w,bank,Function.update_apply,eq_comm] <;> intro hj <;> rw [hj]
  · simp [step,write]

def program := seq (seq (write (bitSymbol false)) CountedCopyReuse.program) (write separator)

theorem runs (source dest : ℤ → Fin 4) (p q : ℤ) (bits bs : List Bool)
    (hw : Counter.value bs=bits.length) :
    HoareTime program
      (fun v => v=bank (putWord source p (bits.map bitSymbol)) dest empty (binary bs) p q 1 1)
      (fun v => v=bank (putWord source p (bits.map bitSymbol))
        (putWord dest q (Partition.recordWord false bits)) empty (binary bs)
        (p+bits.length) (q+bits.length+2) 1 1)
      (5*bits.length+7*bs.length+20) := by
  have hf := writes (bitSymbol false) (putWord source p (bits.map bitSymbol)) dest empty (binary bs) p q 1 1
  have hc := CountedCopyReuse.copy_hoare source (Function.update dest q (bitSymbol false)) p (q+1)
    (bits.map bitSymbol) bs (by simpa using hw)
  simp only [List.length_map] at hc
  have hs := writes separator (putWord source p (bits.map bitSymbol))
    (putWord (Function.update dest q (bitSymbol false)) (q+1) (bits.map bitSymbol)) empty (binary bs)
    (p+bits.length) (q+1+bits.length) 1 1
  have he : Function.update
      (putWord (Function.update dest q (bitSymbol false)) (q+1) (bits.map bitSymbol))
      (q+1+bits.length) separator=putWord dest q (Partition.recordWord false bits) := by
    rw [←putWord_cons]
    unfold Partition.recordWord
    have ht := Gather.putWord_snoc dest q (bitSymbol false::bits.map bitSymbol) separator
    simpa only [List.cons_append,List.nil_append,List.length_cons,List.length_map,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm]
      using ht
  rw [he] at hs
  have hp : q+1+(bits.length:ℤ)+1=q+bits.length+2 := by omega
  exact ((hf.seq hc).seq hs).consequence (fun _ h => h)
    (fun _ h => by simpa only [hp] using h) (by omega)

end
end IntegerMultBounds.Machine.ActiveRepairRecordFormatRecord
