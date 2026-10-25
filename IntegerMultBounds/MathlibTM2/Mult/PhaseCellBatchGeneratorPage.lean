module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicateGenerators
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratorPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTwoBranches

/-! Generated inverse columns are evaluated once and replicated into the exact
row-bank layout consumed by grouped cell arithmetic. The scalar is shared. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem replicate_cstream (A w B : ℕ) (xs : List GaussianInt) :
    (List.replicate B (cstream A w xs)).flatten = cstream A w (List.replicate B xs).flatten := by
  induction B with
  | zero => simp
  | succ B ih => simp [List.replicate_succ, cstream_append, ih]

theorem range_flatMap_const {K : Type*} (B : ℕ) (xs : List K) :
    (List.range B).flatMap (fun _ => xs) = (List.replicate B xs).flatten := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, ih]
    simp only [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- First all first-column rows, then all shifted-reverse rows. -/
theorem rowBank_const_flatMap (B : ℕ) (xs ys : List GaussianInt) :
    (List.range (B + B)).flatMap (rowBank B (fun _ => xs) (fun _ => ys)) =
      (List.replicate B xs).flatten ++ (List.replicate B ys).flatten := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  have hleft : (List.range B).flatMap (rowBank B (fun _ => xs) (fun _ => ys)) =
      (List.range B).flatMap (fun _ => xs) := by
    apply List.flatMap_congr
    intro i hi
    simp [rowBank, List.mem_range.mp hi]
  rw [hleft]
  simp only [rowBank_right, range_flatMap_const]

def batchGeneratorPage (A B P s t u band L q n : ℕ) : List (Fin (A + 4)) :=
  cstream A (2 * q + 8) (List.replicate B (columnWords P s t u band L q n)).flatten ++
    (cstream A (2 * q + 8) (List.replicate B (reversedColumnWords P s t u band L q n)).flatten ++
      csyms A (2 * q + 8) (reciprocalWord P s t u band L q n))

@[simp] theorem batchGeneratorPage_length (A B P s t u band L q n : ℕ) :
    (batchGeneratorPage A B P s t u band L q n).length = (2 * B * L + 1) * (2 * q + 8) := by
  simp [batchGeneratorPage, List.length_flatten]
  ring

theorem batchGeneratorPage_eq_rowBank (A B P s t u band L q n : ℕ) :
    batchGeneratorPage A B P s t u band L q n =
      cstream A (2 * q + 8) ((List.range (B + B)).flatMap
        (rowBank B (fun _ => columnWords P s t u band L q n)
          (fun _ => reversedColumnWords P s t u band L q n))) ++
        csyms A (2 * q + 8) (reciprocalWord P s t u band L q n) := by
  rw [rowBank_const_flatMap]
  simp only [batchGeneratorPage, cstream_append, List.append_assoc]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem replicateGeneratorPage_exec (B P s t u band L q n : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R 96).length = B) (hL : (S.R 103).length = L) (hw : (S.R 94).length = 2 * q + 8)
    (hsrc : S.R 110 = generatorPage A P s t u band L q n ++ tail)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105, 106, 107, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ replicateGeneratorsCost B L (2 * q + 8) ∧
      Exec body replicateGenerators (mk v S) m
        (mk v' { S with R := Function.update S.R 110 (batchGeneratorPage A B P s t u band L q n ++ tail) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := replicateGenerators_exec (body := body) B L (2 * q + 8)
    (cstream A (2 * q + 8) (columnWords P s t u band L q n))
    (cstream A (2 * q + 8) (reversedColumnWords P s t u band L q n))
    (csyms A (2 * q + 8) (reciprocalWord P s t u band L q n)) tail v S hbatch hL hw
    (by simp) (by simp) (by simp) (by simpa [generatorPage, List.append_assoc] using hsrc) hfresh
  refine ⟨v', m, hu, hm, he.cast rfl ?_⟩
  simp [batchGeneratorPage, replicate_cstream, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
