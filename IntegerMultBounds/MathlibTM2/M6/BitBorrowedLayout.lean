module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece
public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap

/-! Interchange the label block and exterior digits between a sweep and an idle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)

theorem idleSize (w B K : ℕ) : volume prime (idleLayout w B K) =
    (prime^w)^128*(B*prime^(64*(w*64))*K) := by
  simp [volume,Nat.mul_assoc]

/-- In sweep order the label row follows the 16 active digits. In idle order
it follows all 128 digits. The offset within a trailing record is unchanged. -/
noncomputable def idleToSweep (w B K : ℕ) :
    Fin (volume prime (idleLayout w B K)) ≃
      Fin ((prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*K))) := by
  let split : Fin ((prime^w)^128) ≃ Fin ((prime^w)^16) × Fin ((prime^w)^112) :=
    (finCongr (by rw [← pow_add])).trans finProdFinEquiv.symm
  let rows := B*prime^(64*(w*64))
  let idle := (finCongr (idleSize w B K)).trans (finProdFinEquiv.symm.trans
    (split.prodCongr (@finProdFinEquiv rows K).symm))
  let sweep := (@finProdFinEquiv ((prime^w)^16) (rows*((prime^w)^112*K))).symm.trans ((Equiv.refl _).prodCongr
    (finProdFinEquiv.symm.trans ((Equiv.refl (Fin rows)).prodCongr (@finProdFinEquiv ((prime^w)^112) K).symm)))
  let shuffle : (Fin ((prime^w)^16) × Fin ((prime^w)^112)) × (Fin rows × Fin K) ≃
      Fin ((prime^w)^16) × Fin rows × Fin ((prime^w)^112) × Fin K :=
    ⟨fun ((a,e),l,t) => (a,l,e,t),fun (a,l,e,t) => ((a,e),l,t),fun _ => rfl,fun _ => rfl⟩
  exact (idle.trans shuffle).trans sweep.symm

local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

/-- Form an idle index from the payload rank, block, matrix label and tail. -/
noncomputable def idleCellIndex {w B K} (g : LabelPadding.Label 64 w) (rank : Fin ((prime^w)^128))
    (b : Fin B) (t : Fin K) : Fin (volume prime (idleLayout w B K)) :=
  let row := (LabelAddress.address g).cast (show (prime^w)^(64*64) = prime^(64*(w*64)) by
    rw [← pow_mul]; congr 1; omega)
  (finProdFinEquiv (rank,finProdFinEquiv (finProdFinEquiv (b,row),t))).cast (idleSize w B K).symm

theorem idleDigitCell_read {w B K n} (width : n = 128) (digits : Fin n → ZMod (prime^w))
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w)
    (x : Fin (volume prime (idleLayout w B K)) → ZMod 2) :
    chartRead x g (idleDigitCell width digits b t) =
      x (idleCellIndex g ((FlatCoordinateLayout.rank digits).cast (congrArg ((prime^w)^·) width)) b t) := by
  let idx := idleCellIndex g ((FlatCoordinateLayout.rank digits).cast (congrArg ((prime^w)^·) width)) b t
  rw [← ext_apply x idx]
  apply congrArg (ext x)
  simp [idx,idleCellIndex,idleDigitCell,RecursiveInterchangeLayout.index,idleLayout,finProdFinEquiv]
  <;> ring

theorem idleToSweep_cell {w B K} (g : LabelPadding.Label 64 w)
    (a : Fin ((prime^w)^16)) (e : Fin ((prime^w)^112)) (b : Fin B) (t : Fin K) :
    let rank := (finProdFinEquiv (a,e)).cast (show (prime^w)^16*(prime^w)^112 = (prime^w)^128 by rw [← pow_add])
    let label := (LabelAddress.address g).cast (show (prime^w)^(64*64) = prime^(64*(w*64)) by
      rw [← pow_mul]; congr 1; omega)
    idleToSweep w B K (idleCellIndex g rank b t) =
      finProdFinEquiv (a,finProdFinEquiv (finProdFinEquiv (b,label),finProdFinEquiv (e,t))) := by
  simp [idleToSweep,idleCellIndex]

/-- On serialized tapes the complete conversion is one rectangular transpose
inside each active slice, with a record of length K at each cell. -/
theorem idleToSweep_word {α : Type*} (fill : α) (w B K : ℕ)
    (x : Fin (volume prime (idleLayout w B K)) → α) :
    let M := prime^w
    let L := B*prime^(64*(w*64))
    Host.swapList (M^16) (M^112) 1 L K fill (List.ofFn x) =
      List.ofFn (x ∘ (idleToSweep w B K).symm) := by
  intro M L
  apply List.ext_getElem
  · simp [Host.swapList,Nat.mul_assoc,M,L]
  · intro j hj hy
    let atSweep : Fin (M^16*(L*(M^112*K))) := ⟨j,by simpa using hy⟩
    obtain ⟨⟨a,rest⟩,eqn⟩ := finProdFinEquiv.surjective atSweep
    obtain ⟨⟨l,rest⟩,rfl⟩ := finProdFinEquiv.surjective rest
    obtain ⟨⟨e,t⟩,rfl⟩ := finProdFinEquiv.surjective rest
    let rank : Fin (M^128) := (finProdFinEquiv (a,e)).cast (by rw [← pow_add])
    let idx := (finProdFinEquiv (rank,finProdFinEquiv (l,t))).cast (idleSize w B K).symm
    have read := Host.swapList_getElem? fill (List.ofFn x)
      (P := M^16) (H := M^112) (G := 1) (D := L) (B := K)
      (by simp [idleSize,M,L,← pow_add]; ring)
      a.isLt e.isLt (by decide : 0 < 1) l.isLt t.isLt
    have dst : (((a.val*L+l.val)*1+0)*M^112+e.val)*K+t.val = j := by
      have val := congrArg Fin.val eqn
      simp only [finProdFinEquiv,Equiv.coe_fn_mk,atSweep] at val
      simp only [mul_one,add_zero]
      rw [← val]; ring
    have src : (((a.val*M^112+e.val)*1+0)*L+l.val)*K+t.val = idx.val := by
      simp [idx,rank,finProdFinEquiv]; ring
    rw [dst,src,List.getElem?_eq_getElem hj,List.getElem?_eq_getElem (by simp [idx.isLt])] at read
    have back : (idleToSweep w B K).symm atSweep = idx := by
      rw [← eqn]
      simp [idleToSweep,idx,rank,M,L]
    simpa only [List.getElem_ofFn,Function.comp_apply,back,atSweep] using Option.some.inj read

/-- Move a field past the inherited block and then past the label. The
second transpose treats both the active digits and the block as a prefix. -/
private theorem swapAcrossProduct {α : Type*} (fill : α) (P E B N K : ℕ) (xs : List α)
    (length : xs.length = P*E*(B*N)*K) :
    Host.swapList (P*B) E 1 N K fill (Host.swapList P E 1 B (N*K) fill xs) =
      Host.swapList P E 1 (B*N) K fill xs := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < P*(B*(N*(E*K)))
  · let idx : Fin (P*(B*(N*(E*K)))) := ⟨j,hj⟩
    obtain ⟨⟨a,r⟩,ha⟩ := finProdFinEquiv.surjective idx
    obtain ⟨⟨b,r⟩,rfl⟩ := finProdFinEquiv.surjective r
    obtain ⟨⟨l,r⟩,rfl⟩ := finProdFinEquiv.surjective r
    obtain ⟨⟨e,t⟩,rfl⟩ := finProdFinEquiv.surjective r
    have index : (((a.val*B+b.val)*N+l.val)*E+e.val)*K+t.val = j := by
      have eqn := congrArg Fin.val ha
      change _ + _ = j at eqn
      rw [← eqn]; simp [finProdFinEquiv]; ring
    have first := Host.swapList_getElem? fill xs (P := P) (H := E) (G := 1) (D := B) (B := N*K)
      (by rw [length]; ring) a.isLt e.isLt (by decide : 0 < 1) b.isLt (Host.mix_lt l.isLt t.isLt)
    have second := Host.swapList_getElem? fill (Host.swapList P E 1 B (N*K) fill xs)
      (P := P*B) (H := E) (G := 1) (D := N) (B := K)
      (by simp [Host.swapList]; ring) (Host.mix_lt a.isLt b.isLt) e.isLt (by decide : 0 < 1) l.isLt t.isLt
    have both := Host.swapList_getElem? fill xs (P := P) (H := E) (G := 1) (D := B*N) (B := K)
      (by simpa using length) a.isLt e.isLt (by decide : 0 < 1) (Host.mix_lt b.isLt l.isLt) t.isLt
    rw [← index]
    simp only [Nat.mul_one,Nat.add_zero] at first second both
    ring_nf at first second both ⊢
    exact second.trans (first.trans both.symm)
  · apply Eq.trans (List.getElem?_eq_none ?_) (List.getElem?_eq_none ?_).symm
    all_goals simpa [Host.swapList,Nat.mul_assoc] using Nat.le_of_not_gt hj

theorem idleToSweep_split {α : Type*} (fill : α) (w B K : ℕ)
    (x : Fin (volume prime (idleLayout w B K)) → α) :
    let M := prime^w
    let N := prime^(64*(w*64))
    Host.swapList (M^16*B) (M^112) 1 N K fill
      (Host.swapList (M^16) (M^112) 1 B (N*K) fill (List.ofFn x)) =
      List.ofFn (x ∘ (idleToSweep w B K).symm) := by
  intro M N
  rw [swapAcrossProduct]
  · exact idleToSweep_word fill w B K x
  · simp [idleSize,M,N,← pow_add,Nat.mul_assoc]

/-- Returning to idle order uses the same rectangular interchange with
the two field sizes reversed. -/
theorem sweepToIdle_word {α : Type*} (fill : α) (w B K : ℕ)
    (x : Fin ((prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*K))) → α) :
    let M := prime^w
    let L := B*prime^(64*(w*64))
    Host.swapList (M^16) L 1 (M^112) K fill (List.ofFn x) =
      List.ofFn (x ∘ idleToSweep w B K) := by
  intro M L
  let y := x ∘ idleToSweep w B K
  have forward := idleToSweep_word fill w B K y
  have undo : y ∘ (idleToSweep w B K).symm = x := by funext j; simp [y]
  rw [undo] at forward
  rw [← forward]
  have size : volume prime (idleLayout w B K) =
      BinaryAdjacentWidthInterchange.volume (M^16) (M^112) 1 L K := by
    rw [idleSize]
    simp [BinaryAdjacentWidthInterchange.volume,M,L,← pow_add,Nat.mul_assoc]
  rw [List.ofFn_congr size y,← Host.ofFn_transpose,← Host.ofFn_transpose,
    BinaryAdjacentWidthInterchange.transpose_transpose]

/-- The selected remainder carries its input bit to the swapped digit
address in sweep order, keeping the block, matrix label and tail offset. -/
theorem IdleTransport.sweepDigits {i : Fin 9} {k : (Fin 32 × Fin 5) × Fin 222} {w B K}
    {x y : Fin ((prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*K))) → ZMod 2}
    (run : IdleTransport i k w B K (x ∘ idleToSweep w B K) (y ∘ idleToSweep w B K)) :
    let e := idleInterval i k.2
    ∀ (a b : Fin e.1 → ZMod (prime^w)) (h d : Fin (e.2-e.1) → ZMod (prime^w))
      (u v : Fin (64-e.2) → ZMod (prime^w)) (block : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w),
      let digits := fun (h d : Fin (e.2-e.1) → ZMod (prime^w)) => Fin.addCases (Fin.addCases (Fin.addCases a h) u) (Fin.addCases (Fin.addCases b d) v)
      let width : (e.1+(e.2-e.1)+(64-e.2))+(e.1+(e.2-e.1)+(64-e.2)) = 128 := by
        obtain ⟨hl,hr,_⟩ := BitHosting.remainder_counts _ (idleInterval_mem i k.2)
        change e.1 ≤ e.2 at hl
        change e.2 ≤ 63 at hr
        omega
      let pos := fun h d => idleToSweep w B K (idleCellIndex g
        ((FlatCoordinateLayout.rank (digits h d)).cast (congrArg ((prime^w)^·) width)) block t)
      y (pos d h) = x (pos h d) := by
  intro e a b h d u v block t g digits width pos
  simpa only [idleDigitCell_read,Function.comp_apply] using run.digits a b h d u v block t g

end IntegerMultBounds.MathlibTM2.M6.BitNode
