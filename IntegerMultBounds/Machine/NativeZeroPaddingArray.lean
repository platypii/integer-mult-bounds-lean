import IntegerMultBounds.Machine.NativeZeroPaddingPlaced
import IntegerMultBounds.Machine.ButterflySpectatorGeometry

/-! The emitted native word is exactly the original coefficient array extended
by signed-zero coefficient records, at the complete padded row cardinality. -/
namespace IntegerMultBounds.Machine.NativeZeroPaddingArray
noncomputable section
open ButterflyStreamData (Coefficient encoded)
open NativeZeroPaddingHeaders (count)

def word {N : ℕ} (f : Fin N → Coefficient) := (List.ofFn (fun i => encoded (f i))).flatten

def append {N : ℕ} (w extra : ℕ) (f : Fin N → Coefficient) : Fin (N+extra) → Coefficient :=
  Fin.append f (fun _ => NativeZeroRecord.coefficient w)

theorem word_append {N : ℕ} (w extra : ℕ) (f : Fin N → Coefficient) :
    word (append w extra f)=word f++NativeZeroStream.records w extra := by
  unfold word append NativeZeroStream.records
  rw [List.ofFn_comp',List.ofFn_fin_append,List.map_append,List.flatten_append]
  simp only [←List.ofFn_comp',List.ofFn_const,NativeZeroRecord.word,List.map_replicate]

/-- Casting cardinality only reinterprets the same row-major native word. -/
def padded (rows targetRows D ell w : ℕ) (hpad : rows≤targetRows)
    (f : Fin (rows*2^D*2^ell) → Coefficient) : Fin (targetRows*2^D*2^ell) → Coefficient :=
  fun i => append w (count rows targetRows D ell) f (Fin.cast (NativeZeroPaddingHeaders.added_volume rows targetRows D ell hpad).symm i)

theorem padded_word (rows targetRows D ell w : ℕ) (hpad : rows≤targetRows)
    (f : Fin (rows*2^D*2^ell) → Coefficient) :
    word (padded rows targetRows D ell w hpad f)=word f++NativeZeroStream.records w (count rows targetRows D ell) := by
  have hh := List.ofFn_congr (NativeZeroPaddingHeaders.added_volume rows targetRows D ell hpad)
    (fun i => encoded (append w (count rows targetRows D ell) f i))
  have he := congrArg List.flatten hh
  change word (append w (count rows targetRows D ell) f)=word (padded rows targetRows D ell w hpad f) at he
  rw [←he,word_append]

theorem padded_width (rows targetRows D ell w : ℕ) (hpad : rows≤targetRows)
    (f : Fin (rows*2^D*2^ell) → Coefficient)
    (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) :
    ∀ i,(padded rows targetRows D ell w hpad f i).1.length=w ∧
      (padded rows targetRows D ell w hpad f i).2.length=w := by
  intro i
  unfold padded
  generalize Fin.cast (NativeZeroPaddingHeaders.added_volume rows targetRows D ell hpad).symm i=k
  induction k using Fin.addCases with
  | left i => simpa [append] using hw i
  | right i => simp [append,NativeZeroRecord.coefficient,NativeZeroRecord.digits]

theorem nonblank {N : ℕ} (f : Fin N → Coefficient) (x : Fin 6) (hx : x∈word f) : x≠blank := by
  simp only [word,List.mem_flatten] at hx
  obtain ⟨xs,hxs,hx⟩ := hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hxs
  simp only [encoded,DelimitedRadixRecord.complex,DelimitedRadixRecord.field,List.mem_append,List.mem_map,List.mem_singleton] at hx
  rcases hx with (⟨y,_,rfl⟩|rfl)|(⟨y,_,rfl⟩|rfl)
  all_goals intro he
  all_goals have hv := congrArg Fin.val he
  all_goals simp [RadixDigits.digitSymbol,blank,separator] at hv

theorem runs (rows targetRows D ell w : ℕ) (hpad : rows≤targetRows)
    (f : Fin (rows*2^D*2^ell) → Coefficient) :
    HoareTime NativeZeroPaddingPlaced.program
      (fun v => v=NativeZeroPaddingPlaced.bank (NativeZeroPaddingHeaders.initial rows targetRows D ell w) (word f))
      (fun v => v=NativeZeroPaddingPlaced.bank (NativeZeroPaddingHeaders.initial rows targetRows D ell w)
        (word (padded rows targetRows D ell w hpad f)))
      (NativeZeroPaddingPlaced.cost rows targetRows D ell w (word f)) := by
  have hh := NativeZeroPaddingPlaced.runs rows targetRows D ell w hpad (word f) (fun x hx => nonblank f x hx)
  rwa [←padded_word rows targetRows D ell w hpad f] at hh

end
end IntegerMultBounds.Machine.NativeZeroPaddingArray
