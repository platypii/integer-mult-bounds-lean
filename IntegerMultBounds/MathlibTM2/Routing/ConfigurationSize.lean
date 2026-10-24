module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationBatchSpec
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-!
# Size bounds for the actual reusable configuration bank

A register outside the configuration source and rewind archive can grow by at
most the framed input size. This controls the real interchange bank-size term
and the subsequent cleanup, without depending on the archived prefix length.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {T A : ℕ}

theorem configurationLoaded_length_le (R : Fin T → List (Fin (A + 4)))
    (src dst tmp saved : Fin T) (word rest : List (Fin (A + 4))) (header : Bool)
    (j : Fin T) (hs : j ≠ src) (ha : j ≠ saved) :
    (configurationLoaded R src dst tmp saved word rest header j).length ≤
      (R j).length + word.length + 1 := by
  by_cases hd : j = dst
  · subst j
    cases header
    · simp [configurationLoaded]
      omega
    · simp [configurationLoaded]
  · by_cases ht : j = tmp
    · subst j
      simp [configurationLoaded, Function.update_of_ne hd, Function.update_of_ne ha]
    · simp [configurationLoaded, Function.update_of_ne hd, Function.update_of_ne ha,
        Function.update_of_ne ht, Function.update_of_ne hs]
      omega

theorem configurationBatchLoaded_length_le (R : Fin T → List (Fin (A + 4))) (src tmp saved : Fin T)
    (slots : List (ConfigurationSlot T)) (words : List (List (Fin (A + 4))))
    (rest : List (Fin (A + 4))) (j : Fin T) (hs : j ≠ src) (ha : j ≠ saved) :
    (configurationBatchLoaded R src tmp saved slots words rest j).length ≤
      (R j).length + (configurationWords words).length := by
  induction slots generalizing R words with
  | nil => simp [configurationBatchLoaded]
  | cons slot slots ih =>
    cases words with
    | nil => simp [configurationBatchLoaded, configurationWords]
    | cons word words =>
      rw [configurationBatchLoaded]
      have h := ih (configurationLoaded R src slot.dst tmp saved word
        (configurationWords words ++ rest) slot.header) words
      have hb := configurationLoaded_length_le R src slot.dst tmp saved word
        (configurationWords words ++ rest) slot.header j hs ha
      simp only [configurationWords, List.length_append, List.length_cons]
      omega


end IntegerMultBounds.MathlibTM2.Routing
