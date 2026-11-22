module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderHandoffRow
public import IntegerMultBounds.Machine.TranslationStream

/-! A charged rotation moves the single occupied label in either direction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine
open FlatCoordinateSchedule (bits bits_value bits_canonical)

private def labelBlocks {N : ℕ} (atRow : Fin N) (word zeros : List (Fin 4)) :=
  List.ofFn (fun j => if j = atRow then word else zeros)

private theorem rotate_labelBlocks {N : ℕ} [NeZero N] (src dst : Fin N) (word zeros : List (Fin 4)) :
    BlockRotationData.rotate (dst-src).val (labelBlocks src word zeros) = labelBlocks dst word zeros := by
  apply List.ext_get
  · simp [labelBlocks]
  · intro j hj hk
    have smaller : j < N := by simpa [labelBlocks] using hk
    let delta := dst-src
    let i := (⟨j,smaller⟩ : Fin N)-delta
    have lands : i+delta = ⟨j,smaller⟩ := sub_add_cancel _ _
    have moves : (i.val+delta.val)%N = j := congrArg Fin.val lands
    have fromSrc : i = src ↔ j = dst.val := by
      constructor
      · intro eq
        have h : src+delta = dst := by simp [delta]
        exact (congrArg Fin.val lands).symm.trans (congrArg Fin.val (eq ▸ h))
      · intro eq
        have h : (⟨j,smaller⟩ : Fin N) = dst := Fin.ext eq
        simp [i,h,delta]
    have moved := BlockRotationData.block_destination delta.val (labelBlocks src word zeros) i.val
      (by simp [labelBlocks])
    have vals : i.val = src.val ↔ j = dst.val := Fin.ext_iff.symm.trans fromSrc
    simpa only [labelBlocks,List.length_ofFn,moves,List.getElem_ofFn,Fin.eta,Fin.ext_iff,vals,List.get_eq_getElem]
      using moved

open Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

private theorem streamBlocks {N : ℕ} (g : Fin N) (word zeros : List (Fin 4)) :
    TranslationStream.blocks N (fun j => if j = g.val then word else zeros) = labelBlocks g word zeros := by
  apply List.ext_get
  · simp [TranslationStream.blocks,labelBlocks]
  · intro j h k
    simp [TranslationStream.blocks,labelBlocks,Fin.ext_iff]

/-- Read a symbol of the streamed payload by inherited block, label and spectator. -/
theorem labelStream_cell {N W : ℕ} (g : Fin N) (count : ℕ) (word : ℕ → List (Fin 4))
    (zeros : List (Fin 4)) (hw : ∀ i, (word i).length = W) (hz : zeros.length = W)
    (i : Fin count) (j : Fin N) (k : Fin W) :
    let payload := fun b r => if r = g.val then word b else zeros
    (TranslationStream.fibers N count payload).flatten[i.val*(N*W)+(j.val*W+k.val)]? =
      if j = g then (word i.val)[k.val]? else zeros[k.val]? := by
  intro payload
  have width (b : ℕ) : BlockRotationData.Uniform W (TranslationStream.blocks N (payload b)) := by
    intro xs mem
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp mem
    dsimp only [payload]; split <;> simp [hw,hz]
  have full : BlockRotationData.Uniform (N*W) (TranslationStream.fibers N count payload) := by
    intro xs mem
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp mem
    rw [BlockRotationData.uniform_volume W _ (width b)]
    simp [TranslationStream.blocks]
  have inner : j.val*W+k.val < N*W := calc
    _ < (j.val+1)*W := by rw [Nat.add_mul,Nat.one_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_right _ j.isLt
  rw [BlockRotationData.flatten_index _ _ full _ _ (by simp [TranslationStream.fibers]) inner]
  simp only [TranslationStream.fibers,List.getElem_map,List.getElem_range]
  rw [BlockRotationData.flatten_index _ _ (width _) _ _ (by simp [TranslationStream.blocks]) k.isLt]
  simp only [TranslationStream.blocks,List.getElem_map,List.getElem_range,payload,Fin.ext_iff]
  split <;> rfl

/-- Across consecutive inherited blocks the same four runtime counters serve
all payloads. Rotation is reversible by interchanging the two row indices. -/
theorem labelRotationStream_exec {P U : Type} {Q N W : ℕ} [NeZero N]
    (body : P → Pr P 14 Q prime U) (fits : 235 ≤ Q) (count : ℕ)
    (src dst : Fin N) (positive : 0 < W) (word : ℕ → List (Fin 4)) (zeros : List (Fin 4))
    (hw : ∀ i, (word i).length = W) (hz : zeros.length = W) (source dest : ℤ → Fin 4) (p q : ℤ) :
    let enc := CountedLoopReuseAlphabet.encoding prime
    let machine := liftQ (Alphabet.program enc TranslationStream.program) fits
    let payload := fun (g : Fin N) i (j : ℕ) => if j = g.val then word i else zeros
    let a := (dst-src).val
    let start := TranslationStream.input N count source dest p q (bits W) (bits N) (bits a) (bits count) (payload src)
    let finish := CountedLoopReuse.bank
      (TranslationStream.state a N W count source dest p q (bits W) (bits N) (bits a) (payload src) count)
      CountedCopyReuse.empty (CountedCopyReuse.binary (bits count)) 1 1
    ∀ u S, RepT (Alphabet.mapTapes enc start) S.L S.R →
      ∃ z D t, Exec body (foreign machine) (mk u S) t (mk z D) ∧
        t ≤ (461*(count*(N*W))+25)*19+6 ∧ z.user = u.user ∧ RepT (Alphabet.mapTapes enc finish) D.L D.R ∧
        S.inp = D.inp ∧ S.out = D.out ∧
        (∀ i, (D.L i).length + (D.R i).length ≤ (S.L i).length + (S.R i).length +
          2*(461*(count*(N*W))+25)) ∧
        finish.tape 11 = putWord dest q (TranslationStream.fibers N count (payload dst)).flatten := by
  intro enc machine payload a start finish u S live
  have width (i j) : (payload src i j).length = W := by
    dsimp only [payload]; split <;> simp [hw,hz]
  have run := TranslationStream.translate_hoare_linear (NeZero.pos N) (dst-src).isLt.le positive
    source dest p q (bits W) (bits N) (bits a) (bits count) (bits_value _) (bits_value _)
    (bits_value _) (bits_value _) (bits_canonical _) (bits_canonical _) (bits_canonical _)
    (bits_canonical _) (payload src) width
  rw [TranslationStream.source_length N W count _ width] at run
  have mapped := HoareTime.liftQ fits (Alphabet.map_hoare enc run)
  obtain ⟨z,D,_,⟨_,rfl,rfl⟩,ready,user,inp,out,stock,t,cost,exec⟩ :=
    foreign_exec (body := body) machine mapped u S _ ⟨start,rfl,rfl⟩ live
  refine ⟨z,D,t,exec,cost,user,ready,inp.symm,out.symm,stock,?_⟩
  change putWord dest q (TranslationStream.outputPrefix a N count (payload src)) = _
  apply congrArg (putWord dest q)
  unfold TranslationStream.outputPrefix TranslationStream.fibers
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  apply congrArg List.flatten
  simpa only [payload,streamBlocks] using rotate_labelBlocks src dst (word i) zeros

end IntegerMultBounds.MathlibTM2.M6.BitNode
