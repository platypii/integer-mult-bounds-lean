module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackAnchorHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix
public import IntegerMultBounds.Machine.BinaryDivide

/-! Load one queued payload into the array slot of the anchor's neutral tape bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.AtomBank Mult.PhaseCellToeplitz
variable {K T Q : ℕ} {P U : Type}

def payloadWord (a : Fin K → Fin 4) : List (Fin (prime+4)) :=
  (List.ofFn a).map RadixToBinary.binaryEncoding.encode

theorem payload_reads (a : Fin K → Fin 4) (z : ℤ) :
    arrTape a z = readAt blank [] (payloadWord a) z := by
  rcases int_cases z with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [readAt_nonneg]
    by_cases h : i < K
    · have inside := BinaryDivide.putWord_getElem (fun _ => blank) 0 (List.ofFn a) i (by simpa using h)
      simp [arrTape,zero_add] at inside ⊢
      rw [inside]
      simp [payloadWord,h]
    · rw [arrTape,putWord_outside _ _ _ _ (Or.inr (by simp; omega))]
      simp [payloadWord,h]
      rfl
  · rw [readAt_neg,arrTape,putWord_outside _ _ _ _ (Or.inl (by omega))]
    rfl

private theorem payload_on_blank (a : Fin K → Fin 4) (L R : List (Fin (prime+4)))
    (empty : ∀ j, readAt blank L R j = blank) (j : ℤ) :
    arrTape a j = readAt blank L (payloadWord a ++ R) j := by
  rw [payload_reads]
  rcases int_cases j with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · simp only [readAt_nonneg]
    by_cases hk : k < (payloadWord a).length
    · rw [List.getElem?_append_left hk]
    · rw [List.getElem?_append_right (by omega),List.getElem?_eq_none (by omega)]
      exact (empty ((k-(payloadWord a).length : ℕ) : ℤ)).symm
  · exact (empty (-(k+1 : ℕ))).symm

/-- One counted move consumes exactly the current array word. The queue tail can contain
arbitrary later records. The destination then represents the literal anchor array at head zero. -/
theorem loadPayload_exec (body : P → Pr P T Q prime U) {count src dst saved tmp : Fin T}
    (layout : [count,src,dst,saved,tmp].Nodup) (a : Fin K → Fin 4) (tail : List (Fin (prime+4)))
    (u : HS T Q prime U) (S : Stacks T prime) (queue : S.R src = payloadWord a ++ tail)
    (width : (S.R count).length = K) (empty : ∀ j, readAt blank (S.L dst) (S.R dst) j = blank)
    (hs : S.R saved = []) (ht : S.R tmp = []) :
    ∃ z F, z.user = u.user ∧ Exec body (movePrefix count src dst saved tmp) (mk u S) (6*K+6) (mk z F) ∧
      F = {S with R := Function.update (Function.update S.R src tail) dst (payloadWord a ++ S.R dst)} ∧
      ∀ j, arrTape a j = readAt blank (F.L dst) (F.R dst) j := by
  obtain ⟨z,hu,run⟩ := movePrefix_exec (body := body) layout (payloadWord a) tail u S queue
    (by simpa [payloadWord] using width) hs ht
  refine ⟨z,_,hu,?_,rfl,?_⟩
  · simpa [payloadWord] using run
  · intro j
    simpa using payload_on_blank a _ _ empty j

/-- After loading slot 17, the active frame and the caller's own stacks give the
whole input representation required by the foreign anchor call. -/
theorem loaded_rep {slots f : ℕ} (d : Fin 17 → Option (List Bool)) (a : Fin K → Fin 4)
    (S : Stacks ((22+slots)+T) prime)
    (array : ∀ j, arrTape a j = readAt blank (S.L (Fin.castAdd T (17 : Fin (22+slots))))
      (S.R (Fin.castAdd T (17 : Fin (22+slots)))) j)
    (frame : ∀ (i : Fin (22+slots)), i.val ≠ 17 → ∀ j,
      (outer slots d (arrTape a) f).tape i j = readAt blank (S.L (Fin.castAdd T i))
        (S.R (Fin.castAdd T i)) (j-(outer slots d (arrTape a) f).head i)) :
    let caller : Tapes T prime := ⟨fun _ => 0,fun i => readAt blank
      (S.L (Fin.natAdd (22+slots) i)) (S.R (Fin.natAdd (22+slots) i))⟩
    RepT ((outer slots d (arrTape a) f).append caller) S.L S.R := by
  intro caller i j
  induction i using Fin.addCases with
  | left i =>
    by_cases h : i.val = 17
    · have eqn : i = 17 := Fin.ext (by simpa [Fin.val_ofNat,Nat.mod_eq_of_lt (show 17 < 22+slots by omega)] using h)
      subst i
      simpa [Tapes.append,outer,Fin.val_ofNat,Nat.mod_eq_of_lt (show 17 < 22+slots by omega)] using array j
    · simpa only [Tapes.append,Fin.addCases_left] using frame i h j
  | right i => simp [caller,Tapes.append]

open Mult.ShortConv Node

private theorem transferReads {A : ℕ} (src dst : Fin T) (hne : src ≠ dst)
    (cs xs : List (Fin (A+4))) (len : cs.length = xs.length) (R : Regs T A)
    (reads : ∀ i (h : i < xs.length), (R src)[i]?.getD blank = xs[i]) :
    cs.foldl (fun r x => transferFx src dst x r) R =
      Function.update (Function.update R src ((R src).drop xs.length)) dst (xs.reverse ++ R dst) := by
  induction cs generalizing xs R with
  | nil =>
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero len.symm
    simp
  | cons c cs ih =>
    cases xs with
    | nil => simp at len
    | cons x xs =>
      have head := reads 0 (by simp)
      simp only [List.getElem_cons_zero,← List.head?_eq_getElem?] at head
      rw [List.foldl_cons,ih xs (by simpa using len)]
      · funext i
        by_cases hd : i = dst <;> by_cases hs : i = src <;>
          simp_all [transferFx,List.reverse_cons,List.append_assoc,Nat.add_comm]
      · intro i h
        simp [transferFx,hne,List.getElem?_tail]
        exact reads (i+1) (by simpa using h)

/-- Collect exactly the represented array into a reversed output archive, even when the
simulator omitted trailing blanks. Both sides of the vacated tape then represent blanks. -/
theorem collectPayload_exec (body : P → Pr P T Q prime U) {count src dst tmp : Fin T}
    (layout : [count,src,dst,tmp].Nodup) (a : Fin K → Fin 4) (u : HS T Q prime U)
    (S : Stacks T prime) (width : (S.R count).length = K) (empty : S.R tmp = [])
    (rep : ∀ j, arrTape a j = readAt blank (S.L src) (S.R src) j) :
    let F := {S with R := Function.update (Function.update S.R src ((S.R src).drop K)) dst ((payloadWord a).reverse ++ S.R dst)}
    ∃ z, z.user = u.user ∧ Exec body (transfer count src dst tmp) (mk u S) (4*K+4) (mk z F) ∧
      ∀ j, readAt blank (F.L src) (F.R src) j = blank := by
  regs_ne layout
  obtain ⟨z,hu,run⟩ := scanR_exec' body ‹count ≠ tmp› (transferAct_fx src dst ‹src ≠ dst›)
    (transferFx_frame ‹count ≠ src› ‹count ≠ dst›) (transferFx_frame ‹src ≠ tmp›.symm ‹dst ≠ tmp›.symm) u S empty
  have cell (i : ℕ) := (rep i).symm.trans (payload_reads a i)
  simp only [readAt_nonneg] at cell
  rw [transferReads src dst ‹src ≠ dst› _ (payloadWord a) (by simpa [payloadWord] using width) _ (by
    intro i hi; simpa [List.getElem?_eq_getElem hi] using cell i),width] at run
  refine ⟨z,hu,by simpa [transfer,payloadWord] using run,?_⟩
  intro j
  simp only [Function.update_of_ne ‹src ≠ dst›,Function.update_self]
  rcases int_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · simpa [readAt_nonneg,List.getElem?_drop,payloadWord] using cell (K+i)
  · simpa only [readAt_neg,List.getElem?_nil,Option.getD_none] using
      (rep (-(i+1 : ℕ))).symm.trans (payload_reads a (-(i+1 : ℕ)))


end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
