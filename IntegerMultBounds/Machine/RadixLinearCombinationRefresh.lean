import IntegerMultBounds.Machine.MarkedRadixRefresh
import IntegerMultBounds.Machine.RadixLinearCombinationBinary
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! Refresh every expression leaf from one shared fixed-size control bank.
References are bounded at compilation; stale copies are physically erased.
No fresh-copy oracle or runtime-dependent tape placement is assumed. -/
namespace IntegerMultBounds.Machine.RadixLinearCombinationRefresh

open RadixDigits
open MarkedWordCleanup (one word)
open SharedPlacementAlphabet (setTape sharedPlacement)
variable {c q : ℕ}

inductive Expr (c : ℕ) where
  | term (index : Fin c) (coefficient : ℚ)
  | add (left right : Expr c)

def Expr.erase : Expr c → RadixLinearCombination.Expr
  | .term i r => .term i.val r
  | .add l r => .add l.erase r.erase

abbrev Size (e : Expr c) := RadixLinearCombination.TapeCount e.erase

def controls (xs : ℕ → List (Fin q)) : Tapes c q :=
  ⟨fun _ => 1,fun i => MarkedRadixRefresh.source (xs i.val)⟩

def bank (e : Expr c) (xs old : ℕ → List (Fin q)) : Tapes (c+Size e) q :=
  (controls xs).append (RadixLinearCombination.bank e.erase old [])

/-- Select the common controls and the left child, framing parent and sibling. -/
def leftPlacement (c l r : ℕ) : Fin ((c+l)+(1+r)) ≃ Fin (c+(1+(l+r))) where
  toFun := Fin.addCases
    (Fin.addCases (Fin.castAdd (1+(l+r))) (fun i => Fin.natAdd c (Fin.natAdd 1 (Fin.castAdd r i))))
    (Fin.addCases (fun i => Fin.natAdd c (Fin.castAdd (l+r) i)) (fun i => Fin.natAdd c (Fin.natAdd 1 (Fin.natAdd l i))))
  invFun := Fin.addCases (fun i => Fin.castAdd (1+r) (Fin.castAdd l i))
    (Fin.addCases (fun i => Fin.natAdd (c+l) (Fin.castAdd r i))
      (Fin.addCases (fun i => Fin.castAdd (1+r) (Fin.natAdd c i)) (fun i => Fin.natAdd (c+l) (Fin.natAdd 1 i))))
  left_inv := by intro i; induction i using Fin.addCases <;> rename_i i <;> induction i using Fin.addCases <;> simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => simp
    | right i =>
      induction i using Fin.addCases with
      | left i => simp
      | right i => induction i using Fin.addCases <;> simp

/-- Select the same controls and the right child, framing parent and sibling. -/
def rightPlacement (c l r : ℕ) : Fin ((c+r)+(1+l)) ≃ Fin (c+(1+(l+r))) where
  toFun := Fin.addCases
    (Fin.addCases (Fin.castAdd (1+(l+r))) (fun i => Fin.natAdd c (Fin.natAdd 1 (Fin.natAdd l i))))
    (Fin.addCases (fun i => Fin.natAdd c (Fin.castAdd (l+r) i)) (fun i => Fin.natAdd c (Fin.natAdd 1 (Fin.castAdd r i))))
  invFun := Fin.addCases (fun i => Fin.castAdd (1+l) (Fin.castAdd r i))
    (Fin.addCases (fun i => Fin.natAdd (c+r) (Fin.castAdd l i))
      (Fin.addCases (fun i => Fin.natAdd (c+r) (Fin.natAdd 1 i)) (fun i => Fin.castAdd (1+l) (Fin.natAdd c i))))
  left_inv := by intro i; induction i using Fin.addCases <;> rename_i i <;> induction i using Fin.addCases <;> simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => simp
    | right i =>
      induction i using Fin.addCases with
      | left i => simp
      | right i => induction i using Fin.addCases <;> simp

private theorem left_active {l r : ℕ} (v : Tapes c q) (z : Tapes 1 q) (x : Tapes l q) (y : Tapes r q) :
    Placement.active (leftPlacement c l r) (v.append (z.append (x.append y))) = v.append x := by
  unfold Placement.active leftPlacement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

private theorem left_extra {l r : ℕ} (v : Tapes c q) (z : Tapes 1 q) (x : Tapes l q) (y : Tapes r q) :
    Placement.extra (leftPlacement c l r) (v.append (z.append (x.append y))) = z.append y := by
  unfold Placement.extra leftPlacement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

private theorem right_active {l r : ℕ} (v : Tapes c q) (z : Tapes 1 q) (x : Tapes l q) (y : Tapes r q) :
    Placement.active (rightPlacement c l r) (v.append (z.append (x.append y))) = v.append y := by
  unfold Placement.active rightPlacement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

private theorem right_extra {l r : ℕ} (v : Tapes c q) (z : Tapes 1 q) (x : Tapes l q) (y : Tapes r q) :
    Placement.extra (rightPlacement c l r) (v.append (z.append (x.append y))) = z.append x := by
  unfold Placement.extra rightPlacement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

private theorem exact_placed {s u t states : ℕ} {M : Program s states q} {v w : Tapes s q} {cost : ℕ}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) (e : Fin (s+u) ≃ Fin t)
    (before after : Tapes t q) (hb : Placement.active e before = v)
    (ha : Placement.active e after = w) (hf : Placement.extra e before = Placement.extra e after) :
    HoareTime (Placement.placed M e) (fun x => x = before) (fun x => x = after) cost := by
  apply (Placement.hoare_at h e before hb).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨small,rfl,rfl⟩
  rw [Placement.replace,hf,← ha]
  exact Placement.view e after

def States : Expr c → ℕ
  | .term _ _ => 7
  | .add l r => States l+States r

def program : (e : Expr c) → Program (c+Size e) (States e) q
  | .term i _ => Placement.placed MarkedRadixRefresh.program (sharedPlacement i (0 : Fin 2))
  | .add l r => seq
      (Placement.placed (program l) (leftPlacement c (Size l) (Size r)))
      (Placement.placed (program r) (rightPlacement c (Size l) (Size r)))

def runtime : Expr c → (ℕ → List (Fin q)) → (ℕ → List (Fin q)) → ℕ
  | .term i _, xs, old => 2*(old i.val).length+2*(xs i.val).length+8
  | .add l r, xs, old => runtime l xs old+runtime r xs old+1

/-- The whole shared control bank is preserved, and every existing expression
leaf slot is synchronized with it. Every old source cell is charged for erasure. -/
theorem refresh_hoare (e : Expr c) (xs old : ℕ → List (Fin q)) :
    HoareTime (program e) (fun v => v = bank e xs old) (fun v => v = bank e xs xs) (runtime e xs old) := by
  induction e with
  | term i r =>
    have h := SharedPlacementAlphabet.shared_hoare (MarkedRadixRefresh.refresh_hoare (xs i.val) (old i.val))
      (controls (c := c) xs) i (0 : Fin 2) (word []) 0 rfl rfl
    have hs : ∀ us vs : List (Fin q), setTape (MarkedRadixRefresh.bank us vs) (0 : Fin 2) (word []) 0 =
        (one (word []) 0).append (one (MarkedRadixRefresh.source vs) 1) := by
      intro us vs
      unfold setTape MarkedRadixRefresh.bank Copy.tapes Copy.cfg Config.tapes one Tapes.append
      congr 1 <;> funext j <;> fin_cases j <;> simp <;> rfl
    have hc : setTape (controls (c := c) xs) i ((MarkedRadixRefresh.bank (xs i.val) (xs i.val)).tape 0)
        ((MarkedRadixRefresh.bank (xs i.val) (xs i.val)).head 0) = controls xs := by
      exact SharedPlacementAlphabet.setTape_self _ _
    rw [hs,hs,hc] at h
    exact h
  | add l r hl hr =>
    let z : Tapes 1 q := one (word []) 0
    let mid := (controls (c := c) xs).append (z.append
      ((RadixLinearCombination.bank l.erase xs []).append (RadixLinearCombination.bank r.erase old [])))
    have hleft := exact_placed hl (leftPlacement c (Size l) (Size r)) (bank (.add l r) xs old) mid
      (left_active _ _ _ _) (left_active _ _ _ _) (by change Placement.extra _ ((controls xs).append (z.append ((RadixLinearCombination.bank l.erase old []).append (RadixLinearCombination.bank r.erase old [])))) = _; rw [left_extra,left_extra])
    have hright := exact_placed hr (rightPlacement c (Size l) (Size r)) mid (bank (.add l r) xs xs)
      (right_active _ _ _ _) (right_active _ _ _ _) (by change _ = Placement.extra _ ((controls xs).append (z.append ((RadixLinearCombination.bank l.erase xs []).append (RadixLinearCombination.bank r.erase xs [])))); rw [right_extra,right_extra])
    exact (hleft.seq hright).consequence (fun _ h => h) (fun _ h => h) (by simp only [runtime]; omega)

/-- Number of physical source copies, fixed by the expression syntax. -/
def leaves : Expr c → ℕ
  | .term _ _ => 1
  | .add l r => leaves l+leaves r

theorem leaves_pos (e : Expr c) : 0 < leaves e := by
  induction e with
  | term => simp [leaves]
  | add l r hl hr => simp only [leaves]; omega

/-- Uniform word-width bound, including stale words of shorter lengths. -/
theorem runtime_le (e : Expr c) (xs old : ℕ → List (Fin q)) (b : ℕ)
    (hn : ∀ i : Fin c, (xs i.val).length ≤ b) (ho : ∀ i : Fin c, (old i.val).length ≤ b) :
    runtime e xs old+1 ≤ leaves e*(4*b+9) := by
  induction e with
  | term i r => simp only [runtime,leaves,one_mul]; have := hn i; have := ho i; omega
  | add l r hl hr => simp only [runtime,leaves]; nlinarith

/-- Bounded coefficient lists require a real control reference for the zero seed. -/
def ofList (seed : Fin c) : List (Fin c × ℚ) → Expr c
  | [] => .term seed 0
  | (i,r)::rest => .add (.term i r) (ofList seed rest)

theorem ofList_leaves (seed : Fin c) (terms : List (Fin c × ℚ)) :
    leaves (ofList seed terms) = terms.length+1 := by
  induction terms with
  | nil => rfl
  | cons term terms ih => rcases term with ⟨i,r⟩; simp [ofList,leaves,ih]; omega

end IntegerMultBounds.Machine.RadixLinearCombinationRefresh
