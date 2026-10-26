module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGatherData

/-! Equal-origin RHS replicas are windows in distinct consecutive ambient lines.
Each window remains inside its own line, including the final replica. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem flatten_uniform_window {K : Type*} (rows : List (List K)) (s p L n : ℕ)
    (hlen : ∀ row ∈ rows, row.length = s) (hn : n < rows.length) (hfit : p+L ≤ s) :
    (rows.flatten.drop (n*s+p)).take L = ((rows.getD n []).drop p).take L := by
  induction rows generalizing n with
  | nil => simp at hn
  | cons row rows ih =>
    have hr := hlen row (by simp)
    have ht : ∀ z ∈ rows, z.length = s := fun z hz => hlen z (by simp [hz])
    cases n with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatten_cons,List.getD_cons_zero]
      rw [List.drop_append_of_le_length (by omega),List.take_append_of_le_length]
      simp only [List.length_drop,hr]
      omega
    | succ n =>
      have he : (n+1)*s+p = row.length+(n*s+p) := by rw [hr]; ring
      simp only [List.flatten_cons,he,List.drop_length_add_append,List.getD_cons_succ]
      exact ih n ht (by simpa using hn)

def replicaAmbientWords {s : ℕ} (B : ℕ) (C : ℕ → ZMod s → GaussianInt) : List GaussianInt :=
  (List.range B).flatMap (fun n => chirpLine s (C n))

@[simp] theorem replicaAmbientWords_length {s : ℕ} (B : ℕ) (C : ℕ → ZMod s → GaussianInt) :
    (replicaAmbientWords B C).length = B*s := by
  simp [replicaAmbientWords,List.length_flatMap]

theorem replicaAmbient_window {s : ℕ} (B : ℕ) (C : ℕ → ZMod s → GaussianInt)
    (p L n : ℕ) (hn : n < B) (hfit : p+L ≤ s) :
    ((replicaAmbientWords B C).drop (n*s+p)).take L =
      cellSourceRows L (fun _ => (p : ZMod s)) C n := by
  have hh := flatten_uniform_window ((List.range B).map (fun n => chirpLine s (C n))) s p L n
    (by intro row hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr; simp)
    (by simpa using hn) hfit
  have hrow : ((List.range B).map (fun n => chirpLine s (C n))).getD n [] = chirpLine s (C n) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hn)]
    simp
  rw [hrow] at hh
  simpa [replicaAmbientWords,List.flatMap_def,ambientLine_window (C n) p L hfit,cellSourceRows] using hh

theorem replicaAmbientStream_window {A s : ℕ} (w B : ℕ) (C : ℕ → ZMod s → GaussianInt)
    (p L n : ℕ) (hn : n < B) (hfit : p+L ≤ s) :
    ((cstream A w (replicaAmbientWords B C)).drop ((n*s+p)*w)).take (L*w) =
      cstream A w (cellSourceRows L (fun _ => (p : ZMod s)) C n) := by
  rw [rsa_cstream_drop,rsa_cstream_take,replicaAmbient_window B C p L n hn hfit]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
