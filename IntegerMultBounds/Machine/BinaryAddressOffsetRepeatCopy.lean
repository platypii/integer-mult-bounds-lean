import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatData
import IntegerMultBounds.Machine.WordBankCleanup

/-! Copy one complete temporary offset word and physically return its head.
Only the destination advances; no per-bit scan of a runtime descriptor occurs. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCopy
open BinaryAddressOffsetRepeatData

private def empty : ℤ → Fin 4 := fun _ => blank

def program := seq (Copy.program (blank : Fin 4) false) (extend (ReturnOrigin.program (a := 0)) 1)
def bank (xs : List Bool) (g : ℤ → Fin 4) (p : ℤ) := Copy.tapes (putWord empty 0 (xs.map bitSymbol)) g 0 p

theorem copies (xs : List Bool) (g : ℤ → Fin 4) (p : ℤ) :
    HoareTime program (fun z => z=bank xs g p)
      (fun z => z=bank xs (putWord g p (xs.map bitSymbol)) (p+xs.length)) (2*xs.length+3) := by
  have h0 := Copy.copy_hoare (blank : Fin 4) false empty g 0 p (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl
  have he : (Copy.retained false : Fin 4 → Fin 4)=id := rfl
  simp only [he,List.map_id,List.length_map,zero_add] at h0
  have h1 := hoare_extend_eq (ReturnOrigin.return_hoare_at empty 0 (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl)
    (⟨fun _ => p+xs.length,fun _ => putWord g p (xs.map bitSymbol)⟩ : Tapes 1 0)
  simp only [List.length_map,zero_add,ReturnOrigin.cfg,Config.tapes,
    BinaryAddressTableStep.pair_append] at h1
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

def state (xs : List Bool) (g : ℤ → Fin 4) (p : ℤ) (i : ℕ) :=
  bank xs (putWord g p ((BinaryAddressOffsetRepeatData.copies xs i).map bitSymbol)) (p+(i*xs.length : ℕ))

theorem step (xs : List Bool) (g : ℤ → Fin 4) (p : ℤ) (i : ℕ) :
    HoareTime program (fun z => z=state xs g p i) (fun z => z=state xs g p (i+1)) (2*xs.length+3) := by
  have hh := copies xs (putWord g p ((BinaryAddressOffsetRepeatData.copies xs i).map bitSymbol)) (p+(i*xs.length : ℕ))
  have hword : putWord (putWord g p ((BinaryAddressOffsetRepeatData.copies xs i).map bitSymbol))
      (p+(i*xs.length : ℕ)) (xs.map bitSymbol) =
      putWord g p ((BinaryAddressOffsetRepeatData.copies xs (i+1)).map bitSymbol) := by
    rw [copies_succ,List.map_append]
    simpa only [List.length_map,copies_length] using
      putWord_append_forward g p ((BinaryAddressOffsetRepeatData.copies xs i).map bitSymbol) (xs.map bitSymbol)
  have hp : p+(i*xs.length : ℕ)+xs.length=p+((i+1)*xs.length : ℕ) := by push_cast; ring
  simpa only [state,hword,hp] using hh

end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCopy
