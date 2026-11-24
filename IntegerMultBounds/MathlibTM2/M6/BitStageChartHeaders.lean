module

public import IntegerMultBounds.MathlibTM2.M6.BitDispatchedCorrectedStage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Cover RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- The outer chart views 128 coordinates and the inner correction views 16.
Their caller banks differ only in the spectator word at position one. -/
noncomputable def stageChartWords (w W : ℕ) (inner : Bool) : Fin 4 → List (Fin (prime+4)) :=
  let M := prime^w
  let count := if inner then M^112*W else W
  ![binSyms M.size M,binSyms count.size count,binSyms 1 1,binSyms w.size w]

def stageChartSources {T : ℕ} (hdr : Fin 127 → Fin 6 → Fin T) (inner : Bool) : Fin 4 → Fin T :=
  ![hdr 1 2, hdr (if inner then 14 else 126) 5,hdr 0 0,hdr 0 3]

theorem stageChartSources_read {T w W : ℕ} (hdr : Fin 127 → Fin 6 → Fin T) (S : Stacks T prime)
    (ready : ∀ i j, S.R (hdr i j) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol)
    (inner : Bool) (i : Fin 4) :
    S.R (stageChartSources hdr inner i) = stageChartWords w W inner i := by
  cases inner <;> fin_cases i <;>
    simp [stageChartSources,stageChartWords,ready,Routines.hdr,RecursiveDimensionBank.values,
      helperAdjacentView,canonicalBits_symbols]

private theorem stageChartLoadCost (w W : ℕ) (pos : 0 < W) (inner : Bool) :
    let V := (prime^w)^128*W
    seedLoadBill (stageChartWords w W inner) ≤ 57*V := by
  intro V
  let M := prime^w
  have hm : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have mass : M ≤ V := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans (Nat.le_mul_of_pos_right _ pos)
  have width : w ≤ V := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans mass
  have count : W ≤ V := Nat.le_mul_of_pos_left _ (pow_pos hm _)
  have suffix : M^112*W ≤ V := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hm (by decide : 112 ≤ 128))
  have size (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self
  have lengthBound (i : Fin 4) : (stageChartWords w W inner i).length ≤ V := by
    cases inner <;> fin_cases i <;> simp [stageChartWords,binSyms] <;>
      first | exact (size _).trans mass | exact (size _).trans width | exact (size _).trans count |
        exact (size _).trans suffix | exact pos.trans_le count
  have sum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
    (f := fun i => 8*(stageChartWords w W inner i).length+6) (g := fun _ => 8*V+6)
    (fun i _ => Nat.add_le_add_right (Nat.mul_le_mul_left 8 (lengthBound i)) 6)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at sum
  unfold seedLoadBill
  omega

/-- Load both callers from the same adjacent-exchange archive. Each bank's
last two slots are its copy scratch and return blank. -/
theorem loadStageChartCallers {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (hdr : Fin 127 → Fin 6 → Fin T) (outer inner : Fin 6 ↪ Fin T)
    (apart : ∀ i j, outer i ≠ inner j)
    (ext : ∀ i j k, hdr i j ≠ outer k) (inside : ∀ i j k, hdr i j ≠ inner k) :
    ∃ code, ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
      (∀ i j, S.R (hdr i j) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      (∀ i, S.R (outer i) = []) → (∀ i, S.R (inner i) = []) →
      ∃ v R n, Exec body code (mk u S) n (mk v {S with R := R}) ∧ v.user = u.user ∧
        CleanupBound S {S with R := R} n (114*((prime^w)^128*W)) ∧
        (∀ i, R (outer (i.castAdd 2)) = stageChartWords w W false i) ∧
        (∀ i, R (inner (i.castAdd 2)) = stageChartWords w W true i) ∧
        ∀ j, (∀ i : Fin 4, outer (i.castAdd 2) ≠ j) → (∀ i : Fin 4, inner (i.castAdd 2) ≠ j) → R j = S.R j := by
  let slots := Fin.castAddEmb 2 (n := 4)
  have load (bank : Fin 6 ↪ Fin T) (b : Bool) (safe : ∀ i j k, hdr i j ≠ bank k) := by
    have away (i j) : stageChartSources hdr b i ≠ bank j := by
      fin_cases i <;> exact safe _ _ _
    have regs (i : Fin 4) : [stageChartSources hdr b i,bank (slots i),bank 4,bank 5].Nodup := by
      have hi : slots i ≠ 4 := by fin_cases i <;> decide
      have hj : slots i ≠ 5 := by fin_cases i <;> decide
      simp [List.nodup_cons,away,bank.injective.eq_iff,hi,hj]
    exact installChildSeed body bank slots (stageChartSources hdr b) (bank 4) (bank 5)
      (fun i j => (away j _).symm) regs
  obtain ⟨a,first⟩ := load outer false ext
  obtain ⟨b,last⟩ := load inner true inside
  refine ⟨a.seq b,?_⟩
  intro w W pos u S ready clearOuter clearInner
  let seed (dir : Bool) : Stacks 6 prime := ⟨[],[],fun _ => [],Fin.append (stageChartWords w W dir) (fun _ : Fin 2 => [])⟩
  have word dir (i : Fin 4) : (seed dir).R (slots i) = stageChartWords w W dir i := by
    exact Fin.append_left (stageChartWords w W dir) (fun _ : Fin 2 => []) i
  obtain ⟨v,R,n,start,user,paid,stored,off⟩ := first (seed false) u S
    (fun i => (stageChartSources_read hdr S ready false i).trans (word false i).symm)
    (fun i => clearOuter _) (clearOuter 4) (clearOuter 5)
  have kept j := off (inner j) (fun i => apart _ j)
  obtain ⟨z,L,m,finish,same,bill,out,frame⟩ := last (seed true) v {S with R := R}
    (fun i => (stageChartSources_read hdr _ (fun j k =>
      (off (hdr j k) (fun _ => (ext j k _).symm)).trans (ready j k)) true i).trans (word true i).symm)
    (fun i => (kept _).trans (clearInner _)) ((kept 4).trans (clearInner 4)) ((kept 5).trans (clearInner 5))
  refine ⟨z,L,n+m,start.seq finish,same.trans user,?_,?_,?_,fun j h g => (frame j g).trans (off j h)⟩
  · have combined := CleanupBound.seq paid bill
    intro js nd
    apply (combined js nd).trans
    apply Nat.add_le_add_left
    simp only [word]
    change seedLoadBill (stageChartWords w W false)+seedLoadBill (stageChartWords w W true) ≤ _
    have h := stageChartLoadCost w W pos false
    have g := stageChartLoadCost w W pos true
    omega
  · intro i
    exact (frame _ (fun j => (apart _ _).symm)).trans ((stored _ (fun h => False.elim (h i rfl))).trans (word false i))
  · intro i
    exact (out _ (fun h => False.elim (h i rfl))).trans (word true i)

/-- Divide the parent row count, construct the adjacent headers, and load
both chart callers on the host of the stage. The bill includes tape growth. -/
theorem parentStageChartCallers {P U : Type} {H Q : ℕ} (body : P → Pr P H Q prime U)
    (archive : Fin (80+273) ↪ Fin H) (outer inner : Fin 6 ↪ Fin H)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (outerOff : ∀ i j, outer i ≠ archive j) (innerOff : ∀ i j, inner i ≠ archive j)
    (separate : ∀ i j, outer i ≠ inner j) :
    ∃ code rate, ∀ (c : CutoffNodeInput) u (S : Stacks H prime),
      let w := c.w+1
      let W := c.B*prime^(64*(w*64))*c.stageFactor
      ParentArchiveInput c.node c.w (embStk archive S) →
      (∀ i, S.R (outer i) = []) → (∀ i, S.R (inner i) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (rate*((prime^w)^16*c.stageWidth)) ∧
        (∀ i, F.R (outer (i.castAdd 2)) = stageChartWords w W false i) ∧
        (∀ i, F.R (inner (i.castAdd 2)) = stageChartWords w W true i) ∧
        (∀ i : Fin 2, F.R (outer (i.natAdd 4)) = [] ∧ F.R (inner (i.natAdd 4)) = []) ∧
        ∀ j, (∀ i, archive i ≠ j) → (∀ i : Fin 4, outer (i.castAdd 2) ≠ j) →
          (∀ i : Fin 4, inner (i.castAdd 2) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let closed : Empty → Pr Empty (80+273) Q prime U := Empty.elim
  obtain ⟨prog,prepare⟩ := placedMoveHeaders (Function.Embedding.refl _) closed capacity
  obtain ⟨C,bound⟩ := placedClosedWorkerCost (P := P) archive prog true
  let headers i j := archive (borrowedHeaders 80 i j)
  obtain ⟨load,fill⟩ := loadStageChartCallers body headers outer inner separate
    (fun _ _ k => (outerOff k _).symm) (fun _ _ k => (innerOff k _).symm)
  let A := (RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152
  refine ⟨(embProg archive Empty.elim prog).seq load,C*A+114,?_⟩
  intro c u S w W input clearO clearI
  obtain ⟨v,D,n,run,user,time,ready,_⟩ := prepare c.node c.w c.B c.rowsPerStage c.width c.rows c.label
    c.stagePositive (embDn archive u) (embStk archive S) input
  obtain ⟨v',E,start,_,vu,proj,off⟩ := exec_emb (body' := body) (ι := Empty.elim) archive.injective
    (fun f => Empty.elim f) run u rfl S rfl
  have width : c.node.beforeRows*c.rowsPerStage*c.node.beforeH*c.node.between*c.node.afterD = W := by
    dsimp only [W,CutoffNodeInput.stageFactor,w]
    rw [c.label]
    ring
  have suffix : (prime^w)^112*W = c.stageWidth := by simp only [W,CutoffNodeInput.stageWidth,w,Nat.mul_assoc]
  have positive : 0 < W := Nat.mul_pos (c.label ▸ c.stagePositive.2.2.1)
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos c.stagePositive.1 c.stagePositive.2.1) c.stagePositive.2.2.2.1)
      c.stagePositive.2.2.2.2)
  have beforeO i := off (outer i) (fun j => (outerOff i j).symm)
  have beforeI i := off (inner i) (fun j => (innerOff i j).symm)
  obtain ⟨z,R,m,finish,last,charge,out,inside,frame⟩ := fill w W positive v' E (by
    rw [← proj,width] at ready
    exact ready) (fun i => (beforeO i).2.trans (clearO i)) (fun i => (beforeI i).2.trans (clearI i))
  refine ⟨z,{E with R := R},n+m,start.seq finish,last.trans (vu.trans user),?_,out,inside,?_,?_⟩
  · have paid : CleanupBound S E n (C*n) := bound body _ _ _ _ _ start
    have total := paid.seq charge
    rw [width] at time
    have h : n ≤ A*((prime^w)^16*c.stageWidth) := suffix ▸ time
    have vol : (prime^w)^128*W = (prime^w)^16*c.stageWidth := by
      rw [← suffix]
      exact (ordinaryCompact_width _ _).symm
    intro js nd
    apply (total js nd).trans
    apply Nat.add_le_add_left
    rw [vol,Nat.add_mul]
    exact Nat.add_le_add_right (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left C h) _
  · intro i
    have disj (j : Fin 4) : j.castAdd 2 ≠ i.natAdd 4 := by
      intro eq
      have h := congrArg Fin.val eq
      change j.val = 4+i.val at h
      omega
    exact ⟨(frame _ (fun j => outer.injective.ne (disj j)) (fun j => (separate _ _).symm)).trans
      ((beforeO _).2.trans (clearO _)),(frame _ (fun j => separate _ _) (fun j => inner.injective.ne (disj j))).trans
      ((beforeI _).2.trans (clearI _))⟩
  · intro j away a b
    exact ⟨(off j away).1,(frame j a b).trans (off j away).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
