import IntegerMultBounds.Swap.Interchange

/-! Simultaneous modular specialization of an ordered rational frame schedule.
One prime avoids old/new frame denominators, every difference factorization's
denominators, and any additional endpoint matrices. At every prime-power width
the ordered programs realize the differences of the reduced frames, with the
exact rational-rank interchange total. Reduction uses only the coprime-denominator
subring; no homomorphism from all rationals to a finite ring is assumed. -/

namespace IntegerMultBounds.Networks.ModularFrameSchedule

open Matrix Finset
open IntegerMultBounds.Swap
open Modular (Admissible reduce denCoprime toZMod denominators factorizationDenominators)
open Shear (Op State run interchanges shearProgram)
open ShearFrame (address)

section Reduction
variable {ι κ : Type*} (m : ℕ)

theorem admissible_add {A B : Matrix ι κ ℚ} (hA : Admissible m A) (hB : Admissible m B) :
    Admissible m (A + B) :=
  fun i j => (denCoprime m).add_mem (hA i j) (hB i j)

theorem admissible_neg {A : Matrix ι κ ℚ} (hA : Admissible m A) : Admissible m (-A) :=
  fun i j => (denCoprime m).neg_mem (hA i j)

theorem admissible_sub {A B : Matrix ι κ ℚ} (hA : Admissible m A) (hB : Admissible m B) :
    Admissible m (A - B) :=
  fun i j => (denCoprime m).sub_mem (hA i j) (hB i j)

theorem reduce_add {A B : Matrix ι κ ℚ} (hA : Admissible m A) (hB : Admissible m B) :
    reduce m (A + B) = reduce m A + reduce m B := by
  ext i j
  exact Modular.ratMod_add m (hA i j) (hB i j)

theorem reduce_neg {A : Matrix ι κ ℚ} (hA : Admissible m A) : reduce m (-A) = -reduce m A := by
  ext i j
  change toZMod m (- (⟨A i j,hA i j⟩ : denCoprime m)) = -toZMod m ⟨A i j,hA i j⟩
  exact map_neg (toZMod m) _

theorem reduce_sub {A B : Matrix ι κ ℚ} (hA : Admissible m A) (hB : Admissible m B) :
    reduce m (A - B) = reduce m A - reduce m B := by
  ext i j
  change toZMod m ((⟨A i j,hA i j⟩ : denCoprime m) - ⟨B i j,hB i j⟩) =
    toZMod m ⟨A i j,hA i j⟩ - toZMod m ⟨B i j,hB i j⟩
  exact map_sub (toZMod m) _ _

theorem reduce_zero : reduce m (0 : Matrix ι κ ℚ) = 0 := by
  ext i j
  exact Modular.ratMod_zero m

theorem reduce_id [DecidableEq ι] : reduce m (1 : Matrix ι ι ℚ) = 1 := Modular.reduce_one m

theorem admissible_id [DecidableEq ι] : Admissible m (1 : Matrix ι ι ℚ) := Modular.admissible_one m

end Reduction

section Schedule
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

abbrev Edge (ι : Type*) := Matrix ι ι ℚ × Matrix ι ι ℚ

/-- Fix the rational pivot factorization before choosing a prime. -/
noncomputable def factors (e : Edge ι) : LowerTriangular.Factorization univ univ (e.2 - e.1) :=
  Classical.choice (LowerTriangular.factorization (e.2 - e.1))

/-- Both endpoint matrices and every factor/inverse denominator are protected. -/
noncomputable def edgeDenominators (e : Edge ι) : Finset ℕ :=
  denominators e.1 ∪ denominators e.2 ∪ factorizationDenominators (factors e)

/-- Additional endpoints affect prime selection but add no edge programs. -/
noncomputable def allDenominators (es : List (Edge ι)) (extra : Finset (Matrix ι ι ℚ)) : Finset ℕ := by
  classical
  exact es.toFinset.biUnion edgeDenominators ∪ extra.biUnion denominators

/-- The reduced program keeps exactly the pivots of its rational difference. -/
noncomputable def program (m : ℕ) (e : Edge ι) : List (Op ι (ZMod m)) :=
  shearProgram (reduce m (factors e).E₁) (reduce m (factors e).E₁')
    (reduce m (factors e).E₂) (reduce m (factors e).E₂') (factors e).L

/-- All frame/rank facts required for this particular ordered edge. -/
structure EdgeSpec (m : ℕ) (e : Edge ι) (p : List (Op ι (ZMod m))) : Prop where
  old_admissible : Admissible m e.1
  new_admissible : Admissible m e.2
  difference_admissible : Admissible m (e.2 - e.1)
  reduce_difference : reduce m (e.2 - e.1) = reduce m e.2 - reduce m e.1
  interchange_count : interchanges p = (e.2 - e.1).rank
  run_difference : ∀ s, run p s = address (Matrix.toLin' (reduce m e.2 - reduce m e.1)) s

/-- The same program also realizes the reduction of the rational difference. -/
theorem EdgeSpec.run_reduced {m : ℕ} {e : Edge ι} {p : List (Op ι (ZMod m))}
    (h : EdgeSpec m e p) (s : State ι (ZMod m)) :
    run p s = address (Matrix.toLin' (reduce m (e.2 - e.1))) s := by
  rw [h.reduce_difference]
  exact h.run_difference s

theorem program_spec (e : Edge ι) {q : ℕ} (hq : q.Prime)
    (hd : ∀ d ∈ edgeDenominators e, d < q) (b : ℕ) :
    EdgeSpec (q ^ b) e (program (q ^ b) e) := by
  have hold : Admissible (q ^ b) e.1 := Modular.admissible_of_lt hq
    (fun d hd' => hd d (mem_union_left _ (mem_union_left _ hd'))) b
  have hnew : Admissible (q ^ b) e.2 := Modular.admissible_of_lt hq
    (fun d hd' => hd d (mem_union_left _ (mem_union_right _ hd'))) b
  have hf : ∀ d ∈ factorizationDenominators (factors e), d < q :=
    fun d hd' => hd d (mem_union_right _ hd')
  obtain ⟨hlen,_,_,_,_,hi₁,_,_,hi₂',heq⟩ :=
    Modular.reduce_factorization_of_prime (factors e) hq hf b
  refine ⟨hold,hnew,admissible_sub _ hnew hold,reduce_sub _ hnew hold,?_,?_⟩
  · rw [program,Shear.shearProgram_interchanges,hlen]
  · intro s
    have hr : ∀ t, run (program (q ^ b) e) t = (t.1 + reduce (q ^ b) (e.2 - e.1) *ᵥ t.2,t.2) := by
      intro t
      rw [program,Shear.shearProgram_run _ _ _ _ hi₁ hi₂',heq]
    have hh := Interchange.run_eq_address (e.2 - e.1) _ _ _ _ _ hr s
    rw [reduce_sub _ hnew hold] at hh
    exact hh

private theorem map_programs (es : List (Edge ι)) (m : ℕ)
    (h : ∀ e ∈ es, EdgeSpec m e (program m e)) :
    List.Forall₂ (EdgeSpec m) es (es.map (program m)) := by
  rw [List.forall₂_map_right_iff,List.forall₂_same]
  exact h

private theorem sum_interchanges (es : List (Edge ι)) (m : ℕ)
    (h : ∀ e ∈ es, EdgeSpec m e (program m e)) :
    ((es.map (program m)).map interchanges).sum = (es.map (fun e => (e.2 - e.1).rank)).sum := by
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  exact fun e he => (h e he).interchange_count

/-- One odd prime works at every power, with all old/new frame matrices,
all rational difference-factorization denominators, and every requested extra
endpoint admissible. Extra matrices add neither programs nor interchanges. -/
theorem exists_prime_schedule_extra (es : List (Edge ι)) (extra : Finset (Matrix ι ι ℚ)) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ (∀ d ∈ allDenominators es extra, d < q) ∧
      ∀ b : ℕ, (∀ A ∈ extra, Admissible (q ^ b) A) ∧
        ∃ ps : List (List (Op ι (ZMod (q ^ b)))),
          List.Forall₂ (EdgeSpec (q ^ b)) es ps ∧
          (ps.map interchanges).sum = (es.map (fun e => (e.2 - e.1).rank)).sum := by
  classical
  obtain ⟨q,hq,h2,hd⟩ := Modular.exists_prime_gt (allDenominators es extra)
  refine ⟨q,hq,h2,hd,?_⟩
  intro b
  have hextra : ∀ A ∈ extra, Admissible (q ^ b) A := by
    intro A hA
    apply Modular.admissible_of_lt hq _ b
    intro d hdA
    exact hd d (mem_union_right _ (mem_biUnion.mpr ⟨A,hA,hdA⟩))
  have hedge : ∀ e ∈ es, EdgeSpec (q ^ b) e (program (q ^ b) e) := by
    intro e he
    apply program_spec e hq _ b
    intro d hde
    exact hd d (mem_union_left _ (mem_biUnion.mpr ⟨e,List.mem_toFinset.mpr he,hde⟩))
  exact ⟨hextra,es.map (program (q ^ b)),map_programs es _ hedge,sum_interchanges es _ hedge⟩

/-- The ordered frame schedule without additional endpoint matrices. -/
theorem exists_prime_schedule (es : List (Edge ι)) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ (∀ d ∈ allDenominators es ∅, d < q) ∧
      ∀ b : ℕ, ∃ ps : List (List (Op ι (ZMod (q ^ b)))),
        List.Forall₂ (EdgeSpec (q ^ b)) es ps ∧
        (ps.map interchanges).sum = (es.map (fun e => (e.2 - e.1).rank)).sum := by
  obtain ⟨q,hq,h2,hd,hs⟩ := exists_prime_schedule_extra es ∅
  exact ⟨q,hq,h2,hd,fun b => (hs b).2⟩

end Schedule
end IntegerMultBounds.Networks.ModularFrameSchedule
