module

public import IntegerMultBounds.MathlibTM2.Routing.HaloScanLayout

/-! Derive monotone scan segments from interval endpoints. Within each pair the
cuts are previous end, next start, first end, following start, second end.
Nonadjacent disjointness places each saved tail wholly in newly read data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloIntervalLayout
open HaloScanLayout
variable {β : Type}

structure IntervalPair where
  start₁ : ℕ
  end₁ : ℕ
  start₂ : ℕ
  end₂ : ℕ

def slice (row : List β) (a b : ℕ) : List β := (row.drop a).take (b-a)

theorem slice_append (row : List β) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    slice row a b++slice row b c = slice row a c := by
  unfold slice
  have h : c-a = (b-a)+(c-b) := by omega
  have he := List.take_add (l := row.drop a) (i := b-a) (j := c-b)
  have hd : (row.drop a).drop (b-a) = row.drop b := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hd,←h] at he
  exact he.symm

theorem slice_length (row : List β) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ row.length) :
    (slice row a b).length = b-a := by
  simp only [slice,List.length_take,List.length_drop]
  omega

theorem slice_append_drop (row : List β) {a b : ℕ} (hab : a ≤ b) :
    slice row a b++row.drop b = row.drop a := by
  have he := List.take_append_drop (b-a) (row.drop a)
  have hd : (row.drop a).drop (b-a) = row.drop b := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hd] at he
  exact he

def firstStart (fallback : ℕ) : List IntervalPair → ℕ
  | [] => fallback
  | x::_ => x.start₁

def lastEnd : ℕ → List IntervalPair → ℕ
  | prev, [] => prev
  | _, x::xs => lastEnd x.end₂ xs

/-- Adjacent windows overlap or touch, and the next saved tail is new. -/
def Valid : ℕ → List IntervalPair → Prop
  | _, [] => True
  | prev, x::xs => x.start₁ ≤ prev ∧ prev ≤ x.start₂ ∧ x.start₂ ≤ x.end₁ ∧
      x.end₁ ≤ firstStart x.end₂ xs ∧ firstStart x.end₂ xs ≤ x.end₂ ∧ Valid x.end₂ xs

def segments (row : List β) : ℕ → List IntervalPair → List (WindowPair β)
  | _, [] => []
  | prev, x::xs =>
    {fresh₁ := slice row prev x.start₂, kept₁ := slice row x.start₂ x.end₁,
     fresh₂ := slice row x.end₁ (firstStart x.end₂ xs), kept₂ := slice row (firstStart x.end₂ xs) x.end₂}
      ::segments row x.end₂ xs

def windows (row : List β) (xs : List IntervalPair) : List β :=
  xs.flatMap fun x => slice row x.start₁ x.end₁++slice row x.start₂ x.end₂

theorem segments_length (row : List β) (prev : ℕ) (xs : List IntervalPair) :
    (segments row prev xs).length = xs.length := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [segments,ih]

theorem le_lastEnd (prev : ℕ) (xs : List IntervalPair) (hv : Valid prev xs) :
    prev ≤ lastEnd prev xs := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨_,hp,hs,he,hn,hv⟩ := hv
    have hh := ih x.end₂ hv
    simp only [lastEnd]
    omega

theorem segments_input (row : List β) (prev : ℕ) (xs : List IntervalPair) (hv : Valid prev xs) :
    (segments row prev xs).flatMap WindowPair.input = slice row prev (lastEnd prev xs) := by
  induction xs generalizing prev with
  | nil => simp [segments,lastEnd,slice]
  | cons x xs ih =>
    obtain ⟨_,hp,hs,he,hn,hv⟩ := hv
    have hlast := le_lastEnd x.end₂ xs hv
    simp only [segments,List.flatMap_cons,WindowPair.input,ih _ hv,lastEnd]
    rw [slice_append row hp hs,slice_append row (hp.trans hs) he,
      slice_append row (hp.trans (hs.trans he)) hn,slice_append row (by omega) hlast]

theorem segments_output (row : List β) (prev : ℕ) (xs : List IntervalPair) (hv : Valid prev xs) :
    output (slice row (firstStart prev xs) prev) (segments row prev xs) = windows row xs := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨ha,hp,hs,he,hn,hv⟩ := hv
    change ((slice row x.start₁ prev++slice row prev x.start₂++slice row x.start₂ x.end₁)++
      (slice row x.start₂ x.end₁++slice row x.end₁ (firstStart x.end₂ xs)++slice row (firstStart x.end₂ xs) x.end₂))++
      output (slice row (firstStart x.end₂ xs) x.end₂) (segments row x.end₂ xs) = _
    rw [slice_append row ha hp,slice_append row (ha.trans hp) hs,
      slice_append row hs he,slice_append row (hs.trans he) hn,ih _ hv]
    rfl

theorem segments_final (row : List β) (prev : ℕ) (xs : List IntervalPair) :
    remainingOverlap (slice row (firstStart prev xs) prev) (segments row prev xs) = [] := by
  induction xs generalizing prev with
  | nil => simp [segments,remainingOverlap,firstStart,slice]
  | cons x xs ih => exact ih x.end₂

theorem segments_fits (row : List β) (V prev : ℕ) (xs : List IntervalPair) (hfit : row.length < 2^V) :
    ∀ x ∈ segments row prev xs, x.Fits V := by
  have hs (a b : ℕ) : (slice row a b).length < 2^V := by
    have h := List.length_take_le' (b-a) (row.drop a)
    simp only [List.length_drop] at h
    exact h.trans_lt ((Nat.sub_le _ _).trans_lt hfit)
  induction xs generalizing prev with
  | nil => simp [segments]
  | cons x xs ih =>
    intro y hy
    simp only [segments,List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨hs _ _,hs _ _,hs _ _,hs _ _⟩
    · exact ih _ y hy

/-- Ordinary binary byte-count words, computed solely from the endpoint cuts. -/
def metadata {A : ℕ} (V : ℕ) : ℕ → List IntervalPair → List (Fin (A+4))
  | _, [] => []
  | prev, x::xs =>
    IntegerMultBounds.MathlibTM2.Host.binSyms V (x.start₂-prev)++
    IntegerMultBounds.MathlibTM2.Host.binSyms V (x.end₁-x.start₂)++
    IntegerMultBounds.MathlibTM2.Host.binSyms V (firstStart x.end₂ xs-x.end₁)++
    IntegerMultBounds.MathlibTM2.Host.binSyms V (x.end₂-firstStart x.end₂ xs)++metadata V x.end₂ xs

theorem segments_metadata {A : ℕ} (row : List (Fin (A+4))) (V prev : ℕ) (xs : List IntervalPair)
    (hv : Valid prev xs) (hbound : lastEnd prev xs ≤ row.length) :
    (segments row prev xs).flatMap (WindowPair.metadata V) = metadata V prev xs := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨_,hp,hs,he,hn,hv⟩ := hv
    have hlast := le_lastEnd x.end₂ xs hv
    have hend : x.end₂ ≤ row.length := hlast.trans hbound
    simp only [segments,List.flatMap_cons,WindowPair.metadata,metadata]
    rw [slice_length row hp (by omega),slice_length row hs (by omega),
      slice_length row he (by omega),slice_length row hn hend,ih _ hv hbound]

end IntegerMultBounds.MathlibTM2.Routing.HaloIntervalLayout
