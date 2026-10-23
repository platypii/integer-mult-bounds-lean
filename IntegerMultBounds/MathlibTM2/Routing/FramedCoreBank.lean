module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankReady
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream
public import Mathlib.Data.List.FinRange

/-! Load every non-stream register of an embedded fixed core. Empty scratch words
are framed too; the record stream itself is never serialized into metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
variable {N T A : ℕ}

def framedCoreRegisters (str : Fin N) : List (Fin N) :=
  (List.finRange N).filter fun j => decide (j ≠ str)

@[simp] theorem mem_framedCoreRegisters (str j : Fin N) :
    j ∈ framedCoreRegisters str ↔ j ≠ str := by
  simp [framedCoreRegisters]

theorem framedCoreRegisters_nodup (str : Fin N) : (framedCoreRegisters str).Nodup :=
  (List.nodup_finRange N).filter _

def framedCoreDestinations (e : Fin N → Fin T) (str : Fin N) : List (Fin T) :=
  (framedCoreRegisters str).map e

def framedCoreJobs (e : Fin N → Fin T) (str : Fin N) (words : Fin N → List (Fin (A + 4))) :
    List (Fin T × List (Fin (A + 4))) :=
  (framedCoreRegisters str).map fun j => (e j, words j)

/-- A fixed core serializes at most one bounded word per physical register. -/
theorem framedCoreFrames_length_le (delimiter : Fin (A + 4))
    (e : Fin N → Fin T) (str : Fin N) (words : Fin N → List (Fin (A + 4)))
    (W : ℕ) (hwords : ∀ j, j ≠ str → (words j).length ≤ W) :
    (delimitedBankFrames delimiter (framedCoreJobs e str words)).length ≤ N * (W + 1) := by
  have hjobs : ∀ job ∈ framedCoreJobs e str words, job.2.length ≤ W := by
    intro job hj
    change job ∈ (framedCoreRegisters str).map (fun j => (e j, words j)) at hj
    obtain ⟨j, hmem, rfl⟩ := List.mem_map.mp hj
    exact hwords j ((mem_framedCoreRegisters str j).mp hmem)
  refine (delimitedBankFrames_length_le delimiter _ W hjobs).trans ?_
  apply Nat.mul_le_mul_right
  simp only [framedCoreJobs, List.length_map, framedCoreRegisters]
  exact (List.length_filter_le _ _).trans_eq (List.length_finRange)

theorem framedCoreJobs_destinations (e : Fin N → Fin T) (str : Fin N)
    (words : Fin N → List (Fin (A + 4))) :
    (framedCoreJobs e str words).map Prod.fst = framedCoreDestinations e str := by
  simp only [framedCoreJobs, framedCoreDestinations, List.map_map, Function.comp_def]

theorem framedCoreDestinations_nodup (e : Fin N → Fin T) (he : Function.Injective e) (str : Fin N) :
    (framedCoreDestinations e str).Nodup := (framedCoreRegisters_nodup str).map he

theorem framedCoreDestinations_stream (e : Fin N → Fin T) (he : Function.Injective e) (str : Fin N) :
    e str ∉ framedCoreDestinations e str := by
  simp only [framedCoreDestinations, List.mem_map]
  rintro ⟨j, hj, heq⟩
  exact (mem_framedCoreRegisters str j).mp hj (he heq)

/-- Loading a full core establishes its complete raw bank, with only the live
record stream retained from the caller. All scratch contents follow from words. -/
theorem framedCoreLoaded (e : Fin N → Fin T) (he : Function.Injective e) (str : Fin N)
    (src tmp saved : Fin T) (hs : ∀ j, e j ≠ src) (ht : ∀ j, e j ≠ tmp)
    (ha : ∀ j, e j ≠ saved) (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (words : Fin N → List (Fin (A + 4))) (bank : Fin T → List (Fin (A + 4))) :
    (delimitedBankLoaded src tmp saved delimiter rest (framedCoreJobs e str words) bank) ∘ e =
      Function.update words str (bank (e str)) := by
  funext j
  by_cases hj : j = str
  · subst j
    rw [Function.comp_apply, Function.update_self]
    apply delimitedBankLoaded_keep src tmp saved (e str) delimiter rest (framedCoreJobs e str words)
      (hs str) (ht str) (ha str)
    intro job hjob
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hjob
    exact he.ne (Ne.symm ((mem_framedCoreRegisters str j).mp hj))
  · rw [Function.comp_apply, Function.update_of_ne hj]
    apply delimitedBankLoaded_at src tmp saved delimiter rest (framedCoreJobs e str words)
      (by rw [framedCoreJobs_destinations]; exact framedCoreDestinations_nodup e he str)
      ?_ (e j, words j) ?_ bank
    · intro job hjob
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hjob
      exact ⟨hs j, ht j, ha j⟩
    · exact List.mem_map.mpr ⟨j, (mem_framedCoreRegisters str j).mpr hj, rfl⟩

/-- Full-core metadata loading preserves every tape outside that core and the
three shared loader registers. -/
theorem framedCoreLoaded_off (e : Fin N → Fin T) (str : Fin N) (src tmp saved j : Fin T)
    (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (words : Fin N → List (Fin (A + 4))) (bank : Fin T → List (Fin (A + 4)))
    (hs : j ≠ src) (ht : j ≠ tmp) (ha : j ≠ saved) (hoff : ∀ k, j ≠ e k) :
    delimitedBankLoaded src tmp saved delimiter rest (framedCoreJobs e str words) bank j = bank j := by
  apply delimitedBankLoaded_keep src tmp saved j delimiter rest (framedCoreJobs e str words) hs ht ha
  intro job hjob
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hjob
  exact hoff k

end IntegerMultBounds.MathlibTM2.Routing
