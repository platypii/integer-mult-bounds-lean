module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterRead
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGatherSchedule

/-! Convert absolute disjoint origins to the relative gaps consumed by the
publication sweep. The original ambient coordinates remain the read ABI. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

variable {α : Type*}

def windowGaps (L : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | cursor,p::ps => (p-cursor)::windowGaps L (p+L) ps

@[simp] theorem windowGaps_length (L cursor : ℕ) (ps : List ℕ) :
    (windowGaps L cursor ps).length = ps.length := by
  induction ps generalizing cursor with
  | nil => rfl
  | cons p ps ih => simp [windowGaps,ih]

theorem windowGaps_fits (L cursor : ℕ) (ps : List ℕ) (E : List α)
    (hbefore : ∀ p ∈ ps, cursor ≤ p) (hdisjoint : ps.Pairwise (fun p q => p+L ≤ q))
    (hfit : ∀ p ∈ ps, p+L ≤ E.length) :
    ScatterFits L (E.drop cursor) (windowGaps L cursor ps) := by
  induction ps generalizing cursor with
  | nil => trivial
  | cons p ps ih =>
    have hcp := hbefore p (by simp)
    have hp := hfit p (by simp)
    have htail := List.pairwise_cons.mp hdisjoint
    refine ⟨by simp only [List.length_drop]; omega, ?_⟩
    have he : (E.drop cursor).drop (p-cursor+L) = E.drop (p+L) := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [he]
    exact ih (p+L) htail.1 htail.2 (fun q hq => hfit q (by simp [hq]))

theorem windowGaps_offset (L cursor : ℕ) (ps : List ℕ)
    (hbefore : ∀ p ∈ ps, cursor ≤ p) (hdisjoint : ps.Pairwise (fun p q => p+L ≤ q))
    (n : ℕ) (hn : n < ps.length) :
    scatterWindowOffset L (windowGaps L cursor ps) n = ps[n]-cursor := by
  induction ps generalizing cursor n with
  | nil => simp at hn
  | cons p ps ih =>
    have hcp := hbefore p (by simp)
    have htail := List.pairwise_cons.mp hdisjoint
    cases n with
    | zero => simp [windowGaps]
    | succ n =>
      have hn' : n < ps.length := by simpa using hn
      have hq : p+L ≤ ps[n] := htail.1 _ (List.getElem_mem hn')
      simp only [windowGaps,scatterWindowOffset_succ,List.getElem_cons_succ]
      rw [ih (p+L) htail.1 htail.2 n hn']
      omega

/-- Every absolute window receives its corresponding packed solution row. -/
theorem scatterRows_absolute (L : ℕ) (ps : List ℕ) (E X : List α)
    (hdisjoint : ps.Pairwise (fun p q => p+L ≤ q))
    (hfit : ∀ p ∈ ps, p+L ≤ E.length) (hx : ps.length*L ≤ X.length)
    (n : ℕ) (hn : n < ps.length) :
    ((scatterRows L E X (windowGaps L 0 ps)).drop ps[n]).take L = (X.drop (n*L)).take L := by
  have hf := windowGaps_fits L 0 ps E (fun _ _ => Nat.zero_le _) hdisjoint hfit
  have he := scatterRows_window L (windowGaps L 0 ps) E X (by simpa using hf)
    (by simpa using hx) n (by simpa using hn)
  rw [windowGaps_offset L 0 ps (fun _ _ => Nat.zero_le _) hdisjoint n hn,Nat.sub_zero] at he
  exact he

theorem scatterRows_absolute_off (L : ℕ) (ps : List ℕ) (E X : List α)
    (hdisjoint : ps.Pairwise (fun p q => p+L ≤ q))
    (hfit : ∀ p ∈ ps, p+L ≤ E.length) (hx : ps.length*L ≤ X.length) (j : ℕ)
    (hoff : ∀ n (hn : n < ps.length), j < ps[n] ∨ ps[n]+L ≤ j) :
    (scatterRows L E X (windowGaps L 0 ps))[j]? = E[j]? := by
  have hf := windowGaps_fits L 0 ps E (fun _ _ => Nat.zero_le _) hdisjoint hfit
  apply scatterRows_off L (windowGaps L 0 ps) E X (by simpa using hf) (by simpa using hx) j
  intro n hn
  have hn' : n < ps.length := by simpa using hn
  rw [windowGaps_offset L 0 ps (fun _ _ => Nat.zero_le _) hdisjoint n hn',Nat.sub_zero]
  exact hoff n hn'

/-- A scatter leaves every slice disjoint from its destination windows intact. -/
theorem scatterRows_slice_off (L : ℕ) (ps : List ℕ) (E X : List α)
    (hdisjoint : ps.Pairwise (fun p q => p+L ≤ q))
    (hfit : ∀ p ∈ ps, p+L ≤ E.length) (hx : ps.length*L ≤ X.length)
    (j w : ℕ) (hoff : ∀ n (hn : n < ps.length), j+w ≤ ps[n] ∨ ps[n]+L ≤ j) :
    ((scatterRows L E X (windowGaps L 0 ps)).drop j).take w = (E.drop j).take w := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < w
  · simp only [List.getElem?_take,hi,↓reduceIte,List.getElem?_drop]
    apply scatterRows_absolute_off L ps E X hdisjoint hfit hx
    intro n hn
    rcases hoff n hn with h | h
    · left; omega
    · right; omega
  · simp [List.getElem?_take,hi]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
