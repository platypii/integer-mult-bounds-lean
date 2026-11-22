module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaSources
public import IntegerMultBounds.MathlibTM2.M6.BitSweepRankLayout

/-! The rank evaluator shares the coordinate reader's zero, one and scratch tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Cover.Fallback RingFormula Host Stack Node

def sweepConstantMap (a : Leaf (Option (Fin 128))) : Fin 4 ↪ Fin 11 :=
  match a with
  | .input _ => ⟨![10,3,4,5],by decide⟩
  | .zero => ⟨![8,3,4,5],by decide⟩
  | .one => ⟨![9,3,4,5],by decide⟩

theorem sweepRankInputs_prepared {T D E A M : ℕ} [NeZero M]
    (rankPool : Fin ((D+1)*13) ↪ Fin T) (coordPool : Fin ((E+1)*13) ↪ Fin T)
    (bank : Fin 11 ↪ Fin T) (disjoint : ∀ i j, coordPool i ≠ rankPool j)
    (rankApart : ∀ i j, bank i ≠ rankPool j) (coordApart : ∀ i j, bank i ≠ coordPool j)
    (H : ℕ) (mat : Bool → Matrix (Fin 64) (Fin 64) (ZMod M))
    (f : Fin 128 → RingFormula (Entry Bool 64)) (rankDepth : sweepBinaryRankCode.depth ≤ D)
    (coordDepth : ∀ i, (f i).depth ≤ E) (out : Fin T) (R : Regs T A)
    (empty : R out = []) (outside : ∀ i, rankPool i ≠ out) (coordOut : ∀ i, coordPool i ≠ out)
    (bankOut : ∀ i, bank i ≠ out)
    (rankMod : ∀ k ≤ D, R (frame rankPool k 2) = binSyms H (M^128))
    (coordMod : ∀ k ≤ E, R (frame coordPool k 2) = binSyms H M)
    (rankFree : ∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → R (frame rankPool k i) = [])
    (coordFree : ∀ k ≤ E, ∀ i : Fin 13, i ≠ 2 → R (frame coordPool k i) = [])
    (chart : ∃ tail, R (bank 2) = matrixWords A H (mat false) ++ tail)
    (width : (R (bank 1)).length = H) (zero : R (bank 8) = binSyms H 0)
    (one : R (bank 9) = binSyms H (1 : ZMod M).val)
    (radix : R (bank 10) = binSyms H (M : ZMod (M^128)).val)
    (free : ∀ i : Fin 11, i ∈ [0,4,5,6] → R (bank i) = [])
    (suffix : List (Fin (A+4))) :
    let updated := Function.update R (bank 7) (matrixWords A H (mat true) ++ suffix)
    let source := sourcePorts ((Fin.castLEEmb (by decide : 10 ≤ 11)).trans bank) id
    let regs := fun a dst => ((sweepConstantMap a).trans bank).trans (Equiv.swap (bank 3) dst).toEmbedding
    let x := fun i => eval (entryValue mat) (f i)
    let leaf := fun i => prepared (registerBank coordPool) (entryValue mat) H
      (leafReady (leafBank source) mat H) (f i) 0
    prepared (registerBank rankPool) (rankInput x) H (rankLeafReady H x leaf regs)
      sweepBinaryRankCode 0 out updated := by
  intro updated source regs x leaf
  let constant := fun a => (sweepConstantMap a).trans bank
  have same (a) : constant a 1 = bank 3 := by cases a <;> rfl
  have redirects : regs = fun a dst => (constant a).trans (Equiv.swap (constant a 1) dst).toEmbedding := by
    funext a dst; rw [same]
  rw [redirects]
  have keep (t) (h : t ≠ bank 7) : updated t = R t := Function.update_of_ne h _ _
  have slot (i : Fin 11) (hi : i ≠ 7) := keep _ (bank.injective.ne hi)
  apply sweepRankLayout_prepared rankPool coordPool source constant disjoint
    (fun _ _ _ => rankApart _ _) (fun _ _ _ => coordApart _ _) (fun _ _ _ => rankApart _ _)
    H mat f rankDepth coordDepth out updated ((keep _ (bankOut 7).symm).trans empty) outside coordOut
    (fun _ _ => bankOut _) (fun _ _ => bankOut _)
    (fun k hk => (keep _ (rankApart 7 _).symm).trans (rankMod k hk))
    (fun k hk => (keep _ (coordApart 7 _).symm).trans (coordMod k hk))
    (fun k hk i hi => (keep _ (rankApart 7 _).symm).trans (rankFree k hk i hi))
    (fun k hk i hi => (keep _ (coordApart 7 _).symm).trans (coordFree k hk i hi))
  · apply sourcePorts_ready
    · intro b; cases b
      · exact (slot 2 (by decide)) ▸ chart
      · exact ⟨suffix,Function.update_self ..⟩
    · exact (slot 1 (by decide)) ▸ width
    · exact (slot 8 (by decide)).trans zero
    · exact (slot 9 (by decide)).trans one
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> exact (slot _ (by decide)).trans (free _ (by decide))
  · intro a h
    have scratch (i : Fin 11) (hi : i ∈ [0,4,5,6]) (ne : i ≠ 7) := (slot i ne).trans (free i hi)
    have oneVal : (1 : ZMod M).val = (1 : ZMod (M^128)).val := by
      by_cases m : M = 1
      · subst M; simp
      · simp [ZMod.val_one'',m]
    cases a with
    | input i =>
      cases i with
      | none => exact ⟨(slot 10 (by decide)).trans radix,scratch 4 (by decide) (by decide),scratch 5 (by decide) (by decide)⟩
      | some i => exact (h i rfl).elim
    | zero => exact ⟨by simpa [constant,sweepConstantMap,Leaf.value] using (slot 8 (by decide)).trans zero,
        scratch 4 (by decide) (by decide),scratch 5 (by decide) (by decide)⟩
    | one => exact ⟨((slot 9 (by decide)).trans one).trans (congrArg (binSyms H) oneVal),
        scratch 4 (by decide) (by decide),scratch 5 (by decide) (by decide)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
