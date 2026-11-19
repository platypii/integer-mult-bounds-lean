module

public import IntegerMultBounds.Machine.FlatControlledShiftArray
public import IntegerMultBounds.MathlibTM2.Host.Foreign
public import IntegerMultBounds.MathlibTM2.Host.Lift
public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! Return the shear output to its common role tape using the three volume counters. -/
public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {P U : Type} {T M d W A : ℕ} [NeZero M]

def returnWord (r : Fin 8 ↪ Fin T) : Pr P T 217 A U :=
  embProg r Empty.elim (foreign (liftQ FlatArrayNormalize.program (by decide)))

/-- The two payload tape views and the three clock/descriptor pairs suffice for normalization. -/
theorem returnWord_ready (r : Fin 8 ↪ Fin T) (S : Stacks T A)
    (dest source : ℤ → Fin (A+4)) (q p : ℤ) (bs qs ps : List Bool)
    (dst : ∀ z, readAt blank (S.L (r 0)) (S.R (r 0)) (z-q) = dest z)
    (src : ∀ z, readAt blank (S.L (r 1)) (S.R (r 1)) (z-p) = source z)
    (controls : ∀ (i : Fin 6) z, CountedLoopReuseAlphabet.binary (![[],bs,[],qs,[],ps] i) z =
      readAt blank (S.L (r (Fin.natAdd 2 i))) (S.R (r (Fin.natAdd 2 i))) (z-1)) :
    RepT (FlatArrayNormalize.bank dest source q p bs qs ps) (S.L ∘ r) (S.R ∘ r) := by
  intro i z
  induction i using Fin.addCases (m := 2) (n := 6) with
  | left i => fin_cases i <;> first | exact (dst z).symm | exact (src z).symm
  | right i => fin_cases i <;> first
      | exact controls 0 z | exact controls 1 z | exact controls 2 z
      | exact controls 3 z | exact controls 4 z | exact controls 5 z

theorem returnPackedList_exec (body : P → Pr P T 217 A U) (r : Fin 8 ↪ Fin T) {N R Q B : ℕ} (volume : N = R*(Q*B)) (hR : 0 < R) (hQ : 0 < Q) (hB : 0 < B)
    (source dest : ℤ → Fin (A+4)) (p q : ℤ) (a word : List (Fin (A+4)))
    (ha : a.length = N) (hw : word.length = N)
    (bs qs ps : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (hp : Counter.value ps = R)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cp : GrowingCounterData.Canonical ps)
    (empty : ∀ z, q ≤ z → z < q+(N : ℕ) → dest z = blank)
    (v : HS T 217 A U) (S : Stacks T A)
    (ready : RepT (FlatArrayNormalize.bank (putWord dest q word) (putWord source p a)
      (q+(N : ℕ)) (p+(N : ℕ)) bs qs ps) (S.L ∘ r) (S.R ∘ r)) :
    ∃ u F n, u.user = v.user ∧ n ≤ (327*N+2)*13+6 ∧
      Exec body (returnWord r) (mk v S) n (mk u F) ∧
      RepT (FlatArrayNormalize.bank dest (putWord source p word) q p bs qs ps) (F.L ∘ r) (F.R ∘ r) ∧
      ∀ j, (∀ i, r i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  have ret := FlatArrayNormalize.normalize_hoare dest (putWord source p a) q p word
    R Q B bs qs ps (hw.trans volume) hb hq hp
    hR hQ hB
    cb cq cp (by simpa only [hw] using empty)
  rw [FlatControlledShiftArray.overwrite _ _ _ _ (ha.trans hw.symm),hw] at ret
  obtain ⟨u,F,_,rfl,rep,hu,_,_,_,n,hn,run⟩ := foreign_exec (P := Empty) Empty.elim _
    (Host.HoareTime.liftQ (by decide : 150 ≤ 217) ret) (embDn r v) (embStk r S) _ rfl ready
  obtain ⟨z,D,placed,_,hz,eq,frame⟩ := exec_emb (body' := body) (ι := Empty.elim)
    r.injective (fun e => nomatch e) run v rfl S rfl
  rw [← eq] at rep
  exact ⟨z,D,n,hz.trans hu,hn,placed,rep,frame⟩

theorem returnPackedWord_exec (body : P → Pr P T 217 A U) (r : Fin 8 ↪ Fin T) {N R Q B : ℕ} (volume : N = R*(Q*B)) (hR : 0 < R) (hQ : 0 < Q) (hB : 0 < B)
    (source dest : ℤ → Fin (A+4)) (p q : ℤ) (a word : Fin N → Fin (A+4))
    (bs qs ps : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (hp : Counter.value ps = R)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cp : GrowingCounterData.Canonical ps)
    (empty : ∀ z, q ≤ z → z < q+(N : ℕ) → dest z = blank)
    (v : HS T 217 A U) (S : Stacks T A)
    (dst : ∀ z, readAt blank (S.L (r 0)) (S.R (r 0)) (z-(q+(N : ℕ))) =
      putWord dest q (List.ofFn word) z)
    (src : ∀ z, readAt blank (S.L (r 1)) (S.R (r 1)) (z-(p+(N : ℕ))) =
      putWord source p (List.ofFn a) z)
    (controls : ∀ (i : Fin 6) z, CountedLoopReuseAlphabet.binary (![[],bs,[],qs,[],ps] i) z =
      readAt blank (S.L (r (Fin.natAdd 2 i))) (S.R (r (Fin.natAdd 2 i))) (z-1)) :
    ∃ u F n, u.user = v.user ∧ n ≤ (327*N+2)*13+6 ∧
      Exec body (returnWord r) (mk v S) n (mk u F) ∧
      RepT (FlatArrayNormalize.bank dest (putWord source p (List.ofFn word)) q p bs qs ps) (F.L ∘ r) (F.R ∘ r) ∧
      ∀ j, (∀ i, r i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  exact returnPackedList_exec body r volume hR hQ hB source dest p q _ _ List.length_ofFn
    List.length_ofFn bs qs ps hb hq hp cb cq cp empty v S
    (returnWord_ready r S _ _ _ _ bs qs ps dst src controls)

theorem returnWord_exec (body : P → Pr P T 217 A U) (r : Fin 8 ↪ Fin T) (t : Fin d) (hW : 0 < W)
    (source dest : ℤ → Fin (A+4)) (p q : ℤ) (a word : Fin (M^d*W) → Fin (A+4))
    (bs qs ps : List Bool)
    (hb : Counter.value bs = suffixSize (Q := M) (W := W) t) (hq : Counter.value qs = M)
    (hp : Counter.value ps = prefixSize (Q := M) t)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cp : GrowingCounterData.Canonical ps)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (v : HS T 217 A U) (S : Stacks T A)
    (dst : ∀ z, readAt blank (S.L (r 0)) (S.R (r 0)) (z-(q+(M^d*W : ℕ))) =
      putWord dest q (List.ofFn word) z)
    (src : ∀ z, readAt blank (S.L (r 1)) (S.R (r 1)) (z-(p+(M^d*W : ℕ))) =
      putWord source p (List.ofFn a) z)
    (controls : ∀ (i : Fin 6) z, CountedLoopReuseAlphabet.binary (![[],bs,[],qs,[],ps] i) z =
      readAt blank (S.L (r (Fin.natAdd 2 i))) (S.R (r (Fin.natAdd 2 i))) (z-1)) :
    ∃ u F n, u.user = v.user ∧ n ≤ (327*(M^d*W)+2)*13+6 ∧
      Exec body (returnWord r) (mk v S) n (mk u F) ∧
      RepT (FlatArrayNormalize.bank dest (putWord source p (List.ofFn word)) q p bs qs ps) (F.L ∘ r) (F.R ∘ r) ∧
      ∀ j, (∀ i, r i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  exact returnPackedWord_exec body r (split_volume (Q := M) (W := W) t)
    (pow_pos (NeZero.pos M) _) (NeZero.pos M) (Nat.mul_pos (pow_pos (NeZero.pos M) _) hW)
    source dest p q a word bs qs ps hb hq hp cb cq cp empty v S dst src controls

end IntegerMultBounds.MathlibTM2.Cover.Fallback
