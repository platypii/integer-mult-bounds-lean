import Mathlib.Tactic
import IntegerMultBounds.Machine

/-! Kronecker substitution: integer multiplication as convolution of bounded
digit vectors, least-significant digit first. Proved: the acyclic convolution
evaluates to the product in every base, a coefficient bound, agreement with the
length-`L` cyclic convolution whenever `a.length + b.length ≤ L + 1`, chunking
of a digit string into `k`-digit blocks with values below `B ^ k`, and the link
to the machine's most-significant-first bit encoding. Nothing here computes a
convolution quickly or on a tape. -/

namespace IntegerMultBounds.NLogN

def evalBase (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + B * evalBase B ds

/-- Pointwise sum, padding the shorter list with zeros. -/
def addLists : List ℕ → List ℕ → List ℕ
  | [], v => v
  | u, [] => u
  | x :: u, y :: v => (x + y) :: addLists u v

/-- Acyclic convolution. -/
def aconv : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x :: xs, ys => addLists (ys.map (x * ·)) (0 :: aconv xs ys)

@[simp] theorem addLists_nil_left (v : List ℕ) : addLists [] v = v := by
  cases v <;> rfl

@[simp] theorem addLists_nil_right (u : List ℕ) : addLists u [] = u := by
  cases u <;> rfl

@[simp] theorem addLists_cons (x y : ℕ) (u v : List ℕ) :
    addLists (x :: u) (y :: v) = (x + y) :: addLists u v := rfl

@[simp] theorem aconv_nil (b : List ℕ) : aconv [] b = [] := rfl

theorem aconv_cons (x : ℕ) (xs ys : List ℕ) :
    aconv (x :: xs) ys = addLists (ys.map (x * ·)) (0 :: aconv xs ys) := rfl

theorem addLists_length (u v : List ℕ) :
    (addLists u v).length = max u.length v.length := by
  induction u generalizing v with
  | nil => simp
  | cons x u ih => cases v with
    | nil => simp
    | cons y v => simp only [addLists_cons, List.length_cons, ih]; omega

theorem evalBase_addLists (B : ℕ) (u v : List ℕ) :
    evalBase B (addLists u v) = evalBase B u + evalBase B v := by
  induction u generalizing v with
  | nil => simp [evalBase]
  | cons x u ih => cases v with
    | nil => simp [evalBase]
    | cons y v => simp only [addLists_cons, evalBase, ih]; ring

theorem evalBase_map_mul (B x : ℕ) (ys : List ℕ) :
    evalBase B (ys.map (x * ·)) = x * evalBase B ys := by
  induction ys with
  | nil => simp [evalBase]
  | cons y ys ih => simp only [List.map_cons, evalBase, ih]; ring

/-- The acyclic convolution of digit vectors evaluates to the product. -/
theorem evalBase_aconv (B : ℕ) (a b : List ℕ) :
    evalBase B (aconv a b) = evalBase B a * evalBase B b := by
  induction a with
  | nil => simp [evalBase]
  | cons x xs ih =>
    rw [aconv_cons, evalBase_addLists, evalBase_map_mul]
    simp only [evalBase, ih]; ring

theorem aconv_length (a b : List ℕ) (ha : a ≠ []) (hb : b ≠ []) :
    (aconv a b).length = a.length + b.length - 1 := by
  have hb' := List.length_pos_of_ne_nil hb
  induction a with
  | nil => exact absurd rfl ha
  | cons x xs ih =>
    rcases xs with _ | ⟨y, ys⟩
    · rw [aconv_cons, addLists_length]; simp; omega
    · have := ih (by simp)
      rw [aconv_cons, addLists_length, List.length_map, List.length_cons, this]
      simp only [List.length_cons]; omega

theorem addLists_bound {u v : List ℕ} {P Q : ℕ} (hu : ∀ c ∈ u, c ≤ P)
    (hv : ∀ c ∈ v, c ≤ Q) : ∀ c ∈ addLists u v, c ≤ P + Q := by
  induction u generalizing v with
  | nil => intro c hc; simp at hc; exact (hv c hc).trans (Nat.le_add_left _ _)
  | cons x u ih => cases v with
    | nil => intro c hc; rw [addLists_nil_right] at hc; exact (hu c hc).trans (Nat.le_add_right _ _)
    | cons y v =>
      intro c hc
      simp only [addLists_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact Nat.add_le_add (hu x (by simp)) (hv y (by simp))
      · exact ih (fun c hc => hu c (List.mem_cons_of_mem _ hc))
          (fun c hc => hv c (List.mem_cons_of_mem _ hc)) c hc

/-- Convolution coefficients of digits below `M` are at most `a.length * M ^ 2`. -/
theorem aconv_coeff_le {a b : List ℕ} {M : ℕ} (ha : ∀ x ∈ a, x < M)
    (hb : ∀ y ∈ b, y < M) : ∀ c ∈ aconv a b, c ≤ a.length * M ^ 2 := by
  induction a with
  | nil => intro c hc; simp at hc
  | cons x xs ih =>
    have h := addLists_bound (P := M ^ 2) (Q := xs.length * M ^ 2)
      (u := b.map (x * ·)) (v := 0 :: aconv xs b) ?_ ?_
    · intro c hc
      have := h c (by rwa [aconv_cons] at hc)
      rw [List.length_cons]; nlinarith
    · intro c hc
      rw [List.mem_map] at hc
      obtain ⟨y, hy, rfl⟩ := hc
      rw [pow_two]
      exact Nat.mul_le_mul (ha x (by simp)).le (hb y hy).le
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact Nat.zero_le _
      · exact ih (fun x hx => ha x (by simp [hx])) c hc

/-! ### Entrywise description and cyclic wrap-around -/

theorem getD_of_length_le {l : List ℕ} {n : ℕ} (h : l.length ≤ n) : l.getD n 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem getD_eq_getElem {l : List ℕ} {n : ℕ} (h : n < l.length) : l.getD n 0 = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem addLists_getD (u v : List ℕ) (k : ℕ) :
    (addLists u v).getD k 0 = u.getD k 0 + v.getD k 0 := by
  induction u generalizing v k with
  | nil => simp
  | cons x u ih => cases v with
    | nil => simp
    | cons y v => cases k with
      | zero => simp
      | succ k => rw [addLists_cons, List.getD_cons_succ, List.getD_cons_succ,
          List.getD_cons_succ, ih]

theorem getD_map_mul (x : ℕ) (ys : List ℕ) (k : ℕ) :
    (ys.map (x * ·)).getD k 0 = x * ys.getD k 0 := by
  induction ys generalizing k with
  | nil => simp
  | cons y ys ih => cases k with
    | zero => simp
    | succ k => rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ, ih]

theorem aconv_getD (a b : List ℕ) (k : ℕ) :
    (aconv a b).getD k 0 = ∑ i ∈ Finset.range (k + 1), a.getD i 0 * b.getD (k - i) 0 := by
  induction a generalizing k with
  | nil => simp
  | cons x xs ih =>
    rw [aconv_cons, addLists_getD, getD_map_mul, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.sub_zero]
    cases k with
    | zero => simp
    | succ k =>
      rw [List.getD_cons_succ, ih]
      simp only [Nat.add_sub_add_right]
      ring

/-- Length-`L` cyclic convolution of zero-padded digit vectors. -/
def cconvList (L : ℕ) (a b : List ℕ) : List ℕ :=
  (List.range L).map fun k =>
    ∑ i ∈ Finset.range L, a.getD i 0 * b.getD ((k + L - i) % L) 0

@[simp] theorem cconv_length (L : ℕ) (a b : List ℕ) : (cconvList L a b).length = L := by
  simp [cconvList]

/-- No wrap-around occurs once `L + 1 ≥ a.length + b.length`. -/
theorem cconv_getD {L : ℕ} {a b : List ℕ} (hL : a.length + b.length ≤ L + 1)
    {k : ℕ} (hk : k < L) : (cconvList L a b).getD k 0 = (aconv a b).getD k 0 := by
  have h1 : (cconvList L a b).getD k 0 =
      ∑ i ∈ Finset.range L, a.getD i 0 * b.getD ((k + L - i) % L) 0 := by
    simp [cconvList, List.getD_eq_getElem?_getD, List.getElem?_range hk]
  have hsub : ∑ i ∈ Finset.range (k + 1), a.getD i 0 * b.getD ((k + L - i) % L) 0 =
      ∑ i ∈ Finset.range L, a.getD i 0 * b.getD ((k + L - i) % L) 0 := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hi'
    rw [Finset.mem_range] at hi hi'
    rw [Nat.mod_eq_of_lt (by omega : k + L - i < L)]
    by_cases hia : i < a.length
    · rw [getD_of_length_le (l := b) (by omega)]; simp
    · rw [getD_of_length_le (l := a) (by omega)]; simp
  rw [h1, aconv_getD, ← hsub]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [show k + L - i = (k - i) + L by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem getD_replicate_zero (m n : ℕ) : (List.replicate m 0).getD n 0 = 0 := by
  induction m generalizing n with
  | zero => simp
  | succ m ih => cases n with
    | zero => simp [List.replicate_succ]
    | succ n => rw [List.replicate_succ, List.getD_cons_succ, ih]

theorem getD_append_replicate (c : List ℕ) (m n : ℕ) :
    (c ++ List.replicate m 0).getD n 0 = c.getD n 0 := by
  induction c generalizing n with
  | nil => rw [List.nil_append, getD_replicate_zero, List.getD_nil]
  | cons x c ih => cases n with
    | zero => simp
    | succ n => rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ, ih]

/-- The cyclic convolution is the zero-padded acyclic one. -/
theorem cconv_eq_pad {L : ℕ} {a b : List ℕ} (hL : a.length + b.length ≤ L + 1)
    (hlen : (aconv a b).length ≤ L) :
    cconvList L a b = aconv a b ++ List.replicate (L - (aconv a b).length) 0 := by
  apply List.ext_getElem
  · simp; omega
  · intro n h₁ h₂
    rw [← getD_eq_getElem h₁, ← getD_eq_getElem h₂, getD_append_replicate,
      cconv_getD hL (by simpa using h₁)]

/-! ### Padding and chunking -/

theorem evalBase_append (B : ℕ) (u v : List ℕ) :
    evalBase B (u ++ v) = evalBase B u + B ^ u.length * evalBase B v := by
  induction u with
  | nil => simp [evalBase]
  | cons x u ih => simp only [List.cons_append, evalBase, ih, List.length_cons, pow_succ]; ring

theorem evalBase_replicate_zero (B m : ℕ) : evalBase B (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, evalBase, ih]

theorem evalBase_append_replicate (B : ℕ) (c : List ℕ) (m : ℕ) :
    evalBase B (c ++ List.replicate m 0) = evalBase B c := by
  rw [evalBase_append, evalBase_replicate_zero]; ring

theorem evalBase_lt {B : ℕ} {ds : List ℕ} (h : ∀ d ∈ ds, d < B) :
    evalBase B ds < B ^ ds.length := by
  induction ds with
  | nil => simp [evalBase]
  | cons d ds ih =>
    have hd := h d (by simp)
    have ih := ih (fun x hx => h x (by simp [hx]))
    simp only [evalBase, List.length_cons]
    calc d + B * evalBase B ds + 1 ≤ B + B * evalBase B ds := by omega
      _ = B * (evalBase B ds + 1) := by ring
      _ ≤ B * B ^ ds.length := Nat.mul_le_mul_left _ ih
      _ = B ^ (ds.length + 1) := by ring

/-- Consecutive blocks of `k` digits; the last block may be shorter. For the
degenerate width `0` the whole string is one block. -/
def chunks : ℕ → List ℕ → List (List ℕ)
  | 0, ds => [ds]
  | _ + 1, [] => []
  | k + 1, d :: ds => (d :: ds.take k) :: chunks (k + 1) (ds.drop k)
termination_by _ ds => ds.length
decreasing_by all_goals (simp [List.length_drop]; try omega)

@[simp] theorem chunks_nil (k : ℕ) : chunks (k + 1) [] = [] := by
  unfold chunks; rfl

theorem chunks_cons (k d : ℕ) (ds : List ℕ) :
    chunks (k + 1) (d :: ds) = (d :: ds.take k) :: chunks (k + 1) (ds.drop k) := by
  conv_lhs => unfold chunks

theorem evalBase_chunks_succ (B k : ℕ) (ds : List ℕ) :
    evalBase B ds = evalBase (B ^ (k + 1)) ((chunks (k + 1) ds).map (evalBase B)) := by
  match ds with
  | [] => simp [evalBase]
  | d :: ds =>
    have ih := evalBase_chunks_succ B k (ds.drop k)
    rw [chunks_cons, List.map_cons]
    simp only [evalBase]
    rw [← ih]
    conv_lhs => rw [← List.take_append_drop k ds, evalBase_append]
    by_cases h : k ≤ ds.length
    · rw [List.length_take, min_eq_left h]; ring
    · rw [List.drop_eq_nil_of_le (by omega)]; simp [evalBase]
termination_by ds.length
decreasing_by all_goals (simp [List.length_drop]; try omega)

/-- A digit string is the base-`B ^ k` string of its `k`-digit chunk values. -/
theorem evalBase_chunks (B : ℕ) {k : ℕ} (hk : 0 < k) (ds : List ℕ) :
    evalBase B ds = evalBase (B ^ k) ((chunks k ds).map (evalBase B)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact evalBase_chunks_succ B k ds

theorem mem_chunks_succ {k : ℕ} {ds c : List ℕ} (hc : c ∈ chunks (k + 1) ds) :
    c.length ≤ k + 1 ∧ c ⊆ ds := by
  match ds with
  | [] => simp at hc
  | d :: ds =>
    rw [chunks_cons, List.mem_cons] at hc
    rcases hc with rfl | hc
    · refine ⟨by simp only [List.length_cons, List.length_take]; omega, ?_⟩
      exact List.cons_subset_cons d (List.take_subset k ds)
    · obtain ⟨h1, h2⟩ := mem_chunks_succ hc
      exact ⟨h1, List.Subset.trans h2
        (List.Subset.trans (List.drop_subset k ds) (List.subset_cons_self d ds))⟩
termination_by ds.length
decreasing_by all_goals (simp [List.length_drop]; try omega)

/-- Every `k`-digit chunk of digits below `B` has value below `B ^ k`. -/
theorem chunk_value_lt {B k : ℕ} (hB : 1 ≤ B) (hk : 0 < k) {ds : List ℕ}
    (h : ∀ d ∈ ds, d < B) : ∀ c ∈ chunks k ds, evalBase B c < B ^ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  intro c hc
  obtain ⟨hlen, hsub⟩ := mem_chunks_succ hc
  calc evalBase B c < B ^ c.length := evalBase_lt (fun d hd => h d (hsub hd))
    _ ≤ B ^ (k + 1) := Nat.pow_le_pow_right hB hlen

/-! ### The machine's bit encoding -/

/-- Most-significant-first bits are the reversed base-2 digit string. -/
theorem binaryValue_eq_evalBase (bs : List Bool) :
    Machine.binaryValue bs = evalBase 2 (bs.reverse.map fun b => if b then 1 else 0) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [Machine.binaryValue, ih, List.reverse_cons, List.map_append, evalBase_append]
    simp [evalBase]; rw [add_comm]

end IntegerMultBounds.NLogN
