import IntegerMultBounds.Machine.RawLinearCombination

/-! Sequential composition of two machines with the same preserved control bank.
Their private banks are physically disjoint; each invocation frames the other. -/
namespace IntegerMultBounds.Machine.SharedControlPair

variable {c l r q m n B C : ℕ}

def leftPlacement (c l r : ℕ) : Fin ((c+l)+r) ≃ Fin (c+(l+r)) where
  toFun := Fin.addCases
    (Fin.addCases (Fin.castAdd (l+r)) (fun i => Fin.natAdd c (Fin.castAdd r i)))
    (fun i => Fin.natAdd c (Fin.natAdd l i))
  invFun := Fin.addCases (fun i => Fin.castAdd r (Fin.castAdd l i))
    (Fin.addCases (fun i => Fin.castAdd r (Fin.natAdd c i)) (Fin.natAdd (c+l)))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => simp
    | right i => induction i using Fin.addCases <;> simp

def rightPlacement (c l r : ℕ) : Fin ((c+r)+l) ≃ Fin (c+(l+r)) where
  toFun := Fin.addCases
    (Fin.addCases (Fin.castAdd (l+r)) (fun i => Fin.natAdd c (Fin.natAdd l i)))
    (fun i => Fin.natAdd c (Fin.castAdd r i))
  invFun := Fin.addCases (fun i => Fin.castAdd l (Fin.castAdd r i))
    (Fin.addCases (Fin.natAdd (c+r)) (fun i => Fin.castAdd l (Fin.natAdd c i)))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => simp
    | right i => induction i using Fin.addCases <;> simp

theorem left_active (v : Tapes c q) (x : Tapes l q) (y : Tapes r q) :
    Placement.active (leftPlacement c l r) (v.append (x.append y))=v.append x := by
  unfold Placement.active leftPlacement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem left_extra (v : Tapes c q) (x : Tapes l q) (y : Tapes r q) :
    Placement.extra (leftPlacement c l r) (v.append (x.append y))=y := by
  cases y
  simp [Placement.extra,leftPlacement,Tapes.append]

theorem right_active (v : Tapes c q) (x : Tapes l q) (y : Tapes r q) :
    Placement.active (rightPlacement c l r) (v.append (x.append y))=v.append y := by
  unfold Placement.active rightPlacement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem right_extra (v : Tapes c q) (x : Tapes l q) (y : Tapes r q) :
    Placement.extra (rightPlacement c l r) (v.append (x.append y))=x := by
  cases x
  simp [Placement.extra,rightPlacement,Tapes.append]

private theorem exact_placed {s u t states : ℕ} {M : Program s states q} {v w : Tapes s q} {cost : ℕ}
    (h : HoareTime M (fun x => x=v) (fun x => x=w) cost) (e : Fin (s+u) ≃ Fin t)
    (before after : Tapes t q) (hb : Placement.active e before=v)
    (ha : Placement.active e after=w) (hf : Placement.extra e before=Placement.extra e after) :
    HoareTime (Placement.placed M e) (fun x => x=before) (fun x => x=after) cost := by
  apply (Placement.hoare_at h e before hb).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨small,rfl,rfl⟩
  rw [Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine e z (Placement.extra e after)) ha.symm).trans
    (Placement.view e after)

def program (M : Program (c+l) m q) (N : Program (c+r) n q) : Program (c+(l+r)) (m+n) q :=
  seq (Placement.placed M (leftPlacement c l r)) (Placement.placed N (rightPlacement c l r))

/-- Both component calls use literally the same preserved physical controls. -/
theorem runs (M : Program (c+l) m q) (N : Program (c+r) n q)
    (v : Tapes c q) (x x' : Tapes l q) (y y' : Tapes r q)
    (hM : HoareTime M (fun z => z=v.append x) (fun z => z=v.append x') B)
    (hN : HoareTime N (fun z => z=v.append y) (fun z => z=v.append y') C) :
    HoareTime (program M N) (fun z => z=v.append (x.append y))
      (fun z => z=v.append (x'.append y')) (B+C+1) := by
  have hL := exact_placed hM (leftPlacement c l r) (v.append (x.append y)) (v.append (x'.append y))
    (left_active _ _ _) (left_active _ _ _) (by rw [left_extra,left_extra])
  have hR := exact_placed hN (rightPlacement c l r) (v.append (x'.append y)) (v.append (x'.append y'))
    (right_active _ _ _) (right_active _ _ _) (by rw [right_extra,right_extra])
  exact (hL.seq hR).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.SharedControlPair
