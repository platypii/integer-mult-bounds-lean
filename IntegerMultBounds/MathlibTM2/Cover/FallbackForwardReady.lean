module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackForwardStages

/-! Carry the payload layout through forward elimination. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem forwardReady_exec (rows : Fin d → Fin d) (H J : ℕ) (hm : M < 2^H)
    (body : P → Pr P (N+2) columnCapacity prime U) (v : HS (N+2) columnCapacity prime U) (S : Stacks (N+2) prime)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (valid : Itinerary.Valid rows m d)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M) :
    let bank := fun n => columnBank.trans (archivePorts n)
    let ready := fun n t => ColumnReady (bank n) H J (Itinerary.run rows m n) t SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original addr
    let clean := fun (D : Stacks (N+2) prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i).castSucc = [] ∧ D.R (columnPorts i).castSucc = []
    let words := fun n => matrixWords prime H (Itinerary.run rows m n)
    ready 0 tail S → clean S → S.R (Fin.last N).castSucc = scheduleCode rows ++ rest →
    ∃ z F l suffix, z.user = v.user ∧ l ≤ d*(2*d+(4*w+4+columnTime d prime w H))+1 ∧
      Exec body (streamedItinerary d prime forwardBank (Fin.last N).castSucc d) (mk v S) l (mk z F) ∧
      ready d suffix F ∧ clean F ∧ F.R (Fin.last N).castSucc = rest ∧
      (F.R (bank d 34),F.R (bank (d+1) 34)) = matrixArchive words (words 0 ++ tail) (S.R (bank 1 34)) d := by
  intro bank ready clean words initial free code
  obtain ⟨word,h,placed⟩ := initial
  have fresh (i : Fin 23) (hi : (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21) :
      S.R (forwardBank i) = [] := by
    have spec : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 →
        i ≠ 16 ∧ forwardSlots i ∈ shearWork := by decide
    simpa only [bank,Function.Embedding.trans_apply,forwardBank,Function.Embedding.coeFn_mk,ite_eq_right (spec i hi).1] using (h.scratch _ (spec i hi).2).2
  obtain ⟨z,F,l,suffix,hz,hl,run,packed,pair,remaining,left,_,_,frame⟩ :=
    forwardStages_exec rows H hm body v S m valid tail rest h.archive h.modulus h.padded h.clock fresh code
  have fixed (i : Fin 35) (hi : i ≠ 34) : bank d i = bank 0 i := by
    simp only [bank,Function.Embedding.trans_apply,archivePorts_fixed _ _ (columnBank.injective.ne hi)]
  have keep (i : Fin 35) (hi : i ≠ 34) : F.R (bank d i) = S.R (bank 0 i) := by
    apply Eq.trans _ (congrArg S.R (fixed i hi))
    apply frame
    · rw [← archivePorts_stream d]
      apply (archivePorts d).injective.ne
      intro eq
      have e := congrArg Fin.val eq
      change i.val = rowSwapBlock.tapes+35 at e
      have := i.isLt
      omega
    · exact (bank d).injective.ne hi
    · exact archivePorts_other d _
  have keepL (i : Fin 35) (hi : i ≠ 34) : F.L (bank d i) = S.L (bank 0 i) := by rw [left,fixed i hi]
  refine ⟨z,F,l,suffix,hz,hl,run,⟨word,?_,placed⟩,?_,remaining,pair⟩
  · refine ⟨(keep 2 (by decide)).trans h.modulus,(keep 27 (by decide)).trans h.width,
      (keep 28 (by decide)).trans h.one,(keep 32 (by decide)).trans h.padded,?_,packed,?_,?_,?_⟩
    · rw [keep 33 (by decide),h.clock]
    · intro i hi
      have ne : i ≠ 34 := fun e => (by decide : (34 : Fin 35) ∉ shearWork) (e ▸ hi)
      exact ⟨(keepL i ne).trans (h.scratch i hi).1,(keep i ne).trans (h.scratch i hi).2⟩
    · rw [keepL 24 (by decide),keep 24 (by decide)]
      exact h.src
    · rw [keepL 25 (by decide),keep 25 (by decide)]
      exact h.dst
  · intro i hi
    refine ⟨by rw [left]; exact (free i hi).1, (frame _ ?_ ?_ ?_).trans (free i hi).2⟩
    · intro eq
      have e := congrArg Fin.val eq
      change i.val = N at e
      exact i.isLt.ne e
    · rw [← archivePorts_workspace (d+1) i hi]
      exact archivePorts_previous d _
    · rw [← archivePorts_workspace d i hi]
      exact archivePorts_other d _

end IntegerMultBounds.MathlibTM2.Cover.Fallback
