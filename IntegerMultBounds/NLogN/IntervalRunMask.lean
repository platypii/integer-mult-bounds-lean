module

public import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! Rasterize arbitrary ordered disjoint intervals by false/true runs. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.IntervalRunMask

def Ordered (start stop : ℕ) : List (ℕ × ℕ) → Prop
  | [] => start ≤ stop
  | (lo,hi)::xs => start ≤ lo ∧ lo ≤ hi ∧ Ordered hi stop xs

def contains (xs : List (ℕ × ℕ)) (k : ℕ) : Bool :=
  xs.any (fun r => decide (r.1 ≤ k ∧ k < r.2))

def mask (start stop : ℕ) : List (ℕ × ℕ) → List Bool
  | [] => List.replicate (stop-start) false
  | (lo,hi)::xs => List.replicate (lo-start) false++(List.replicate (hi-lo) true++mask hi stop xs)

theorem bounds {start stop : ℕ} {xs : List (ℕ × ℕ)} (h : Ordered start stop xs) :
    start ≤ stop ∧ ∀ r ∈ xs, start ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ stop := by
  induction xs generalizing start with
  | nil => exact ⟨h,by simp⟩
  | cons r xs ih =>
    obtain ⟨lo,hi⟩ := r
    obtain ⟨hstart,hlo,htail⟩ := h
    obtain ⟨hh,hr⟩ := ih htail
    refine ⟨by omega,?_⟩
    intro r hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨hstart,hlo,hh⟩
    · obtain ⟨hlo',hhi',hstop⟩ := hr r hm
      exact ⟨by omega,hhi',hstop⟩

theorem ordered_of_pairwise {start stop : ℕ} {xs : List (ℕ × ℕ)} (hstop : start ≤ stop)
    (hstart : ∀ r ∈ xs, start ≤ r.1) (hrange : ∀ r ∈ xs, r.1 ≤ r.2 ∧ r.2 ≤ stop)
    (hsep : xs.Pairwise (fun r q => r.2 ≤ q.1)) : Ordered start stop xs := by
  induction xs generalizing start with
  | nil => exact hstop
  | cons r xs ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hsep
    refine ⟨hstart r (by simp),(hrange r (by simp)).1,?_⟩
    exact ih (hrange r (by simp)).2 hhead (fun q hq => hrange q (by simp [hq])) htail

theorem length_mask {start stop : ℕ} {xs : List (ℕ × ℕ)} (h : Ordered start stop xs) :
    (mask start stop xs).length = stop-start := by
  induction xs generalizing start with
  | nil => simp [mask]
  | cons r xs ih =>
    obtain ⟨lo,hi⟩ := r
    obtain ⟨hstart,hlo,htail⟩ := h
    have hh := (bounds htail).1
    simp only [mask,List.length_append,List.length_replicate,ih htail]
    omega

theorem contains_below {start stop : ℕ} {xs : List (ℕ × ℕ)} (h : Ordered start stop xs)
    {k : ℕ} (hk : k < start) : contains xs k = false := by
  unfold contains
  apply List.any_eq_false.mpr
  intro r hr
  have hb := (bounds h).2 r hr
  simp only [decide_eq_true_eq]
  omega

theorem getElem?_mask {start stop : ℕ} {xs : List (ℕ × ℕ)} (h : Ordered start stop xs)
    {k : ℕ} (hstart : start ≤ k) (hstop : k < stop) :
    (mask start stop xs)[k-start]? = some (contains xs k) := by
  induction xs generalizing start with
  | nil => simp [mask,contains,show k-start < stop-start by omega]
  | cons r xs ih =>
    obtain ⟨lo,hi⟩ := r
    obtain ⟨hlo,hhi,htail⟩ := h
    by_cases hpre : k < lo
    · have hidx : k-start < lo-start := by omega
      have hbelow := contains_below htail (by omega : k < hi)
      have hc : contains ((lo,hi)::xs) k = false := by
        change (decide (lo ≤ k ∧ k < hi) || contains xs k) = false
        rw [hbelow]
        simp [hpre]
      simp [mask,List.getElem?_append,hidx,hc]
    have hleft : lo ≤ k := by omega
    have hoff : k-start-(lo-start) = k-lo := by omega
    by_cases hmid : k < hi
    · have hidx : ¬k-start < lo-start := by omega
      have hinside : k-lo < hi-lo := by omega
      have hc : contains ((lo,hi)::xs) k = true := by
        change (decide (lo ≤ k ∧ k < hi) || contains xs k) = true
        simp [hleft,hmid]
      simp [mask,List.getElem?_append,hidx,hoff,hinside,hc]
    have hafter : hi ≤ k := by omega
    have hidx : ¬k-start < lo-start := by omega
    have hidx' : ¬k-lo < hi-lo := by omega
    have hoff' : k-lo-(hi-lo) = k-hi := by omega
    have ht := ih htail hafter
    have hc : contains ((lo,hi)::xs) k = contains xs k := by
      change (decide (lo ≤ k ∧ k < hi) || contains xs k) = contains xs k
      simp [hmid]
    simpa [mask,List.getElem?_append,hidx,hoff,hidx',hoff',hc] using ht

theorem mask_eq_map {start stop : ℕ} {xs : List (ℕ × ℕ)} (h : Ordered start stop xs) :
    mask start stop xs = (List.range (stop-start)).map (fun j => contains xs (start+j)) := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < stop-start
  · have hm := getElem?_mask h (k := start+j) (by omega) (by have := (bounds h).1; omega)
    simpa [List.getElem?_map,hj] using hm
  · have hm : (mask start stop xs)[j]? = none := List.getElem?_eq_none (by rw [length_mask h]; omega)
    simpa [hm,List.getElem?_map,hj] using hm

/-- A fixed scan emits one gap and one body per interval, then the final gap. -/
def runs (start stop : ℕ) : List (ℕ × ℕ) → List (Bool × ℕ)
  | [] => [(false,stop-start)]
  | (lo,hi)::xs => (false,lo-start)::(true,hi-lo)::runs hi stop xs

theorem length_runs (start stop : ℕ) (xs : List (ℕ × ℕ)) :
    (runs start stop xs).length = 2*xs.length+1 := by
  induction xs generalizing start with
  | nil => simp [runs]
  | cons r xs ih => simp [runs,ih]; omega

theorem flatten_runs (start stop : ℕ) (xs : List (ℕ × ℕ)) :
    (runs start stop xs).flatMap (fun r => List.replicate r.2 r.1) = mask start stop xs := by
  induction xs generalizing start with
  | nil => simp [runs,mask]
  | cons r xs ih => simp [runs,mask,ih]

theorem sum_runs {start stop : ℕ} {xs : List (ℕ × ℕ)} (h : Ordered start stop xs) :
    ((runs start stop xs).map Prod.snd).sum = stop-start := by
  induction xs generalizing start with
  | nil => simp [runs]
  | cons r xs ih =>
    obtain ⟨lo,hi⟩ := r
    obtain ⟨hstart,hlo,htail⟩ := h
    have hh := (bounds htail).1
    simp only [runs,List.map_cons,List.sum_cons,ih htail]
    omega

/-- Sum the binary-to-unary emitter budget without charging geometry per output bit. -/
theorem emission_cost {start stop : ℕ} {xs : List (ℕ × ℕ)}
    (h : Ordered start stop xs) (W : ℕ) :
    ((runs start stop xs).map (fun r => 8*r.2+11*W+8)).sum =
      8*(stop-start)+(11*W+8)*(2*xs.length+1) := by
  induction xs generalizing start with
  | nil => simp [runs]; omega
  | cons r xs ih =>
    obtain ⟨lo,hi⟩ := r
    obtain ⟨hstart,hlo,htail⟩ := h
    have hh := (bounds htail).1
    simp only [runs,List.map_cons,List.sum_cons,ih htail,List.length_cons]
    ring_nf
    omega

end IntegerMultBounds.NLogN.IntervalRunMask
