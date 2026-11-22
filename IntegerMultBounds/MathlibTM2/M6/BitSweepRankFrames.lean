module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaInit
public import IntegerMultBounds.MathlibTM2.M6.BitSweepRankSources

/-! Borrow and restore both arithmetic pools around a PR589 rank computation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Cover.Fallback RingFormula Host Stack Node

theorem withSweepFrames_exec {T D E Q A M : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (rankPool : Fin ((D+1)*13) ↪ Fin T) (coordPool : Fin ((E+1)*13) ↪ Fin T)
    (rankMod coordMod dst : Fin T) (disjoint : ∀ i j, coordPool i ≠ rankPool j)
    (rankOff : ∀ j, rankMod ≠ rankPool j) (coordOff : ∀ j, coordMod ≠ coordPool j)
    (modOff : ∀ j, coordMod ≠ rankPool j) (dstRank : ∀ j, dst ≠ rankPool j)
    (dstCoord : ∀ j, dst ≠ coordPool j) (v : HS T Q A U) (S : Stacks T A)
    (blankRank : ∀ j, S.R (rankPool j) = []) (blankCoord : ∀ j, S.R (coordPool j) = [])
    (H : ℕ) (rankWord : S.R rankMod = binSyms H (M^128)) (coordWord : S.R coordMod = binSyms H M)
    (program : Pr P T Q A U) (word : List (Fin (A+4))) (cost : ℕ)
    (writer : ∀ (u : HS T Q A U) (B : Stacks T A),
      (∀ i, (∀ j, i ≠ rankPool j) → (∀ j, i ≠ coordPool j) → B.R i = S.R i) →
      (∀ k ≤ D, B.R (frame rankPool k 2) = binSyms H (M^128)) →
      (∀ k ≤ E, B.R (frame coordPool k 2) = binSyms H M) →
      (∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → B.R (frame rankPool k i) = []) →
      (∀ k ≤ E, ∀ i : Fin 13, i ≠ 2 → B.R (frame coordPool k i) = []) →
      ∃ z n, z.user = u.user ∧ n ≤ cost ∧ Exec body program (mk u B) n
        (mk z {B with R := Function.update B.R dst (word ++ B.R dst)})) :
    ∃ z n, z.user = v.user ∧ n ≤ cost+(D+E+2)*(8*H+8)+4 ∧
      Exec body ((initFrames rankPool rankMod (D+1)).seq
        (((initFrames coordPool coordMod (E+1)).seq (program.seq (clearFrames coordPool (E+1)))).seq
          (clearFrames rankPool (D+1)))) (mk v S) n
        (mk z {S with R := Function.update S.R dst (word ++ S.R dst)}) := by
  let inner := (E+1)*(6*H+6)+1+(cost+((E+1)*(2*H+2)+1))
  obtain ⟨z,n,hz,hn,run⟩ := withFrames_exec body rankPool rankMod dst rankOff dstRank _ word inner v S blankRank (by
    intro u B keepRank filledRank freeRank
    have coord := (keepRank coordMod modOff).trans coordWord
    have blank j := (keepRank _ (disjoint j)).trans (blankCoord j)
    obtain ⟨y,k,hy,hk,exec⟩ := withFrames_exec body coordPool coordMod dst coordOff dstCoord program word cost u B blank (by
      intro t F keepCoord filledCoord freeCoord
      apply writer t F
      · exact fun i hr hc => (keepCoord i hc).trans (keepRank i hr)
      · intro k hk
        exact (keepCoord _ (fun j => (disjoint j _).symm)).trans ((filledRank k hk).trans rankWord)
      · exact fun k hk => (filledCoord k hk).trans coord
      · intro k hk i hi
        exact (keepCoord _ (fun j => (disjoint j _).symm)).trans (freeRank k hk i hi)
      · exact freeCoord)
    exact ⟨y,k,hy,by simpa only [coord,length_binSyms,inner] using hk,exec⟩)
  refine ⟨z,n,hz,hn.trans ?_,run⟩
  rw [rankWord,length_binSyms]
  dsimp [inner]
  exact le_of_eq (by ring)

theorem sweepRankFromBlankFrames_exec {T D E Q A M : ℕ} [NeZero M] {P U : Type}
    (body : P → Pr P T Q A U) (rankPool : Fin ((D+1)*13) ↪ Fin T) (coordPool : Fin ((E+1)*13) ↪ Fin T)
    (bank : Fin 11 ↪ Fin T) (disjoint : ∀ i j, coordPool i ≠ rankPool j)
    (rankApart : ∀ i j, bank i ≠ rankPool j) (coordApart : ∀ i j, bank i ≠ coordPool j)
    (rankMod coordMod out : Fin T) (rankOff : ∀ j, rankMod ≠ rankPool j)
    (coordOff : ∀ j, coordMod ≠ coordPool j) (modOff : ∀ j, coordMod ≠ rankPool j)
    (outside : ∀ j, out ≠ rankPool j) (coordOut : ∀ j, out ≠ coordPool j) (bankOut : ∀ i, bank i ≠ out)
    (H : ℕ) (fits : M^128 < 2^H) (mat : Bool → Matrix (Fin 64) (Fin 64) (ZMod M))
    (f : Fin 128 → RingFormula (Entry Bool 64)) (rd : sweepBinaryRankCode.depth ≤ D)
    (cd : ∀ i, (f i).depth ≤ E) (v : HS T Q A U) (S : Stacks T A)
    (blankRank : ∀ j, S.R (rankPool j) = []) (blankCoord : ∀ j, S.R (coordPool j) = [])
    (rankWord : S.R rankMod = binSyms H (M^128)) (coordWord : S.R coordMod = binSyms H M)
    (empty : S.R out = []) (packed : ∀ b, ∃ tail, S.R (bank (if b then 7 else 2)) = matrixWords A H (mat b) ++ tail)
    (width : (S.R (bank 1)).length = H) (zero : S.R (bank 8) = binSyms H 0)
    (one : S.R (bank 9) = binSyms H (1 : ZMod M).val) (radix : S.R (bank 10) = binSyms H (M : ZMod (M^128)).val)
    (free : ∀ i : Fin 11, i ∈ [0,4,5,6] → S.R (bank i) = []) :
    let source := sourcePorts ((Fin.castLEEmb (by decide : 10 ≤ 11)).trans bank) id
    let regs := fun a dst => ((sweepConstantMap a).trans bank).trans (Equiv.swap (bank 3) dst).toEmbedding
    let coord := fun i => compile (readLeaf (leafBank source)) (registerBank coordPool) (f i) 0
    let program := compile (rankLeafProgram coord regs) (registerBank rankPool) sweepBinaryRankCode 0 out
    let cost := time H (rankLeafCost H (fun i => time H (readTime H) (f i))) sweepBinaryRankCode
    let x := fun i => eval (entryValue mat) (f i)
    ∃ z n, z.user = v.user ∧ n ≤ cost+(D+E+2)*(8*H+8)+4 ∧
      Exec body ((initFrames rankPool rankMod (D+1)).seq
        (((initFrames coordPool coordMod (E+1)).seq (program.seq (clearFrames coordPool (E+1)))).seq
          (clearFrames rankPool (D+1)))) (mk v S) n
        (mk z {S with R := Function.update S.R out (binSyms H (FlatCoordinateLayout.rank x).val ++ S.R out)}) := by
  intro source regs coord program cost x
  apply withSweepFrames_exec body rankPool coordPool rankMod coordMod out disjoint rankOff coordOff modOff
    outside coordOut v S blankRank blankCoord H rankWord coordWord
  intro u B keep rm cm rf cf
  have slot i := keep (bank i) (rankApart i) (coordApart i)
  obtain ⟨tail,data⟩ := packed true
  have data' : B.R (bank 7) = matrixWords A H (mat true) ++ tail := (slot 7).trans data
  have ready := sweepRankInputs_prepared rankPool coordPool bank disjoint rankApart coordApart H mat f rd cd out B.R
    ((keep _ outside coordOut).trans empty) (fun i => (outside i).symm) (fun i => (coordOut i).symm) bankOut
    rm cm rf cf (by obtain ⟨t,eq⟩ := packed false; exact ⟨t,(slot 2).trans eq⟩)
    (by rwa [slot]) ((slot 8).trans zero) ((slot 9).trans one) ((slot 10).trans radix)
    (fun i hi => (slot i).trans (free i hi)) tail
  dsimp only at ready
  rw [← data',Function.update_eq_self] at ready
  exact rankFromCoordinates_writes body H fits x (registerBank rankPool) regs coord _ _
    (fun i dst => compile_from_matrices body (leafBank source) (registerBank coordPool) mat H
      ((Nat.le_self_pow (by decide : 128 ≠ 0) _).trans_lt fits) (f i) dst) out u B ready

end IntegerMultBounds.MathlibTM2.M6.BitNode
