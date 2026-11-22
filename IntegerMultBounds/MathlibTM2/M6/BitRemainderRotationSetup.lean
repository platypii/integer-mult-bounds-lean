module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRotationRewind

/-! Load the four retained binary descriptors into the physical rotation bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)

def rotationDimensionPorts : Fin 4 ↪ Fin 14 := ⟨![5,7,8,13],by decide⟩

theorem prepareRotation_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 14 ↪ Fin T) (src : Fin 4 → Fin T) (apart : ∀ i j, src i ≠ bank j) :
    ∃ code, ∀ (W N a B : ℕ) (f g : ℤ → Fin (prime+4)) u S,
      (∀ i z, readAt blank (S.L (src i)) (S.R (src i)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![W,N,a,B] i)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      (∀ z, f z = readAt blank (S.L (bank 10)) (S.R (bank 10)) z) →
      (∀ z, g z = readAt blank (S.L (bank 11)) (S.R (bank 11)) z) →
      ∃ v F, Exec body code (mk u S)
        (((List.finRange 4).map (fun i => 8*(bits (![W,N,a,B] i)).length+8)).sum+2) (mk v F) ∧
        v.user = u.user ∧ RepT (rotationBank (TranslationDescriptors.initial (bits W) (bits N) (bits a))
          (CountedLoopReuse.controls (fun _ => blank) (CountedCopyReuse.binary (bits B)) 0 1) 0 f g)
          (fun j => F.L (bank j)) (fun j => F.R (bank j)) ∧
        ∀ j, (∀ i, bank (rotationDimensionPorts i) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let dst := rotationDimensionPorts.trans bank
  let marks := (List.finRange 4).map dst
  refine ⟨.seq (loadDimensions src dst (bank 0) (List.finRange 4)) (.act (Cover.Fallback.pushMarkers marks)),?_⟩
  intro W N a B f g u S words free source dest
  let ds := fun i : Fin 4 => bits (![W,N,a,B] i)
  have ports (i : Fin 4) : [src i,bank 0,dst i].Nodup := by
    have pair := ((by decide : ∀ i, [0,rotationDimensionPorts i].Nodup) i).map bank.injective
    exact List.nodup_cons.mpr ⟨by simp [dst,apart],pair⟩
  obtain ⟨v,D,user,load,left,loaded,off⟩ := loadDimensions_exec body src dst (bank 0) ds
    (fun i j => apart i _) ports _ (List.nodup_finRange 4) u S words (free 0 (by decide) (by decide))
    (fun i _ => (free _ ((by decide : ∀ i, rotationDimensionPorts i ≠ 10) i)
      ((by decide : ∀ i, rotationDimensionPorts i ≠ 11) i)).2)
  have mark := Exec.act (body := body) (Cover.Fallback.pushMarkers marks) (mk v D)
  rw [Cover.Fallback.pushMarkers_run _ ((List.nodup_finRange 4).map dst.injective)] at mark
  let F := {D with L := fun j => if j ∈ marks then separator :: D.L j else D.L j}
  refine ⟨v,F,(Exec.seq load mark).cast (by simp [ds,Nat.add_assoc]) rfl,user,?_,?_⟩
  · intro j z
    have counter (i : Fin 4) :
        (CountedLoopReuseAlphabet.encoding prime).encode (CountedCopyReuse.binary (ds i) z) =
          readAt blank (F.L (dst i)) (F.R (dst i)) (z-1) := by
      have hm : dst i ∈ marks := List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
      have emp := free _ ((by decide : ∀ i, rotationDimensionPorts i ≠ 10) i)
        ((by decide : ∀ i, rotationDimensionPorts i ≠ 11) i)
      change _ = readAt blank (if dst i ∈ marks then separator :: D.L (dst i) else D.L (dst i)) (D.R (dst i)) _
      rw [ite_eq_left hm,left,show S.L (dst i) = [] from emp.1,loaded i (List.mem_finRange i)]
      change RadixZeroFill.encodedBinary _ z = _
      rw [encodedBinary_eq,readAt_single]
    have unchanged (j : Fin 14) (h : ∀ i, rotationDimensionPorts i ≠ j) :
        F.L (bank j) = S.L (bank j) ∧ F.R (bank j) = S.R (bank j) := by
      have outside : bank j ∉ marks := by
        rintro hm; obtain ⟨i,_,eq⟩ := List.mem_map.mp hm; exact h i (bank.injective eq)
      exact ⟨by simp [F,outside,left], off _ (fun i _ => bank.injective.ne (h i))⟩
    have blankCell (j : Fin 14) (h : ∀ i, rotationDimensionPorts i ≠ j)
        (h10 : j ≠ 10) (h11 : j ≠ 11) (p : ℤ) :
        blank = readAt blank (F.L (bank j)) (F.R (bank j)) p := by
      rw [(unchanged j h).1,(unchanged j h).2,(free j h10 h11).1,(free j h10 h11).2,
        readAt_nil_left,wordTape_nil]
    have data (j : Fin 14) (h : ∀ i, rotationDimensionPorts i ≠ j) :
        readAt blank (S.L (bank j)) (S.R (bank j)) z =
        readAt blank (F.L (bank j)) (F.R (bank j)) (z-0) := by
      rw [(unchanged j h).1,(unchanged j h).2,sub_zero]
    fin_cases j <;> first
      | exact counter 0
      | exact counter 1
      | exact counter 2
      | exact counter 3
      | exact (source z).trans (data 10 (by decide))
      | exact (dest z).trans (data 11 (by decide))
      | exact blankCell _ (by decide) (by decide) (by decide) _
  · intro j h
    have outside : j ∉ marks := by
      rintro hm; obtain ⟨i,_,eq⟩ := List.mem_map.mp hm; exact h i eq
    exact ⟨by simp [F,outside,left],off j (fun i _ => h i)⟩

/-- Loading all four descriptors costs at most a constant per rotated cell. -/
theorem prepareRotation_cost {B N W a : ℕ} (hb : 0 < B) (hn : 0 < N) (hw : 0 < W) (ha : a ≤ N) :
    ((List.finRange 4).map (fun i => 8*(bits (![W,N,a,B] i)).length+8)).sum+2 ≤
      64*(B*(N*W))+34 := by
  let V := B*(N*W)
  have nw := Nat.mul_pos hn hw
  have pos : 0 < V := Nat.mul_pos hb nw
  have row : N*W ≤ V := Nat.le_mul_of_pos_left _ hb
  have w : W ≤ V := (Nat.le_mul_of_pos_left _ hn).trans row
  have n : N ≤ V := (Nat.le_mul_of_pos_right _ hw).trans row
  have b : B ≤ V := Nat.le_mul_of_pos_right _ nw
  have width := FlatCoordinateDimensions.bits_length_le_twice w pos
  have labels := FlatCoordinateDimensions.bits_length_le_twice n pos
  have shift := FlatCoordinateDimensions.bits_length_le_twice (ha.trans n) pos
  have blocks := FlatCoordinateDimensions.bits_length_le_twice b pos
  change 8*(bits W).length+8+(8*(bits N).length+8+(8*(bits a).length+8+(8*(bits B).length+8+0)))+2 ≤ 64*V+34
  omega

/-- Load the descriptors and rotate on the owner bank. The same host code
works for every row width, label count, and pair of labels. -/
theorem placedRotation_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (bank : Fin 14 ↪ Fin T) (headers : Fin 4 → Fin T)
    (apart : ∀ i j, headers i ≠ bank j) :
    ∃ code, ∀ {B N W : ℕ} [NeZero N] (hb : 0 < B) (hw : 0 < W) (src dst : Fin N)
      (row : Fin B → Fin W → ZMod 2) (x y : Fin ((B*N)*W) → ZMod 2),
      (∀ b j k, x (finProdFinEquiv (finProdFinEquiv (b,j),k)) = if j = src then row b k else 0) →
      (∀ b j k, y (finProdFinEquiv (finProdFinEquiv (b,j),k)) = if j = dst then row b k else 0) →
      ∀ u S, (∀ i z, readAt blank (S.L (headers i)) (S.R (headers i)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![W,N,(dst-src).val,B] i)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      WordAtZero x (S.L (bank 10)) (S.R (bank 10)) →
      (∀ z, readAt blank (S.L (bank 11)) (S.R (bank 11)) z = blank) →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧ t ≤ 8842*(B*(N*W))+559 ∧
        v.user = u.user ∧ WordAtZero x (F.L (bank 10)) (F.R (bank 10)) ∧
        WordAtZero y (F.L (bank 11)) (F.R (bank 11)) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨setup,load⟩ := prepareRotation_exec body bank headers apart
  let machine := liftQ (Alphabet.program (CountedLoopReuseAlphabet.encoding prime) TranslationStream.program) fits
  let localCode : Pr Empty 14 Q prime U := (foreign machine).seq (foreign (liftQ rotationRewind (by omega : 3 ≤ Q)))
  refine ⟨setup.seq (embProg bank Empty.elim localCode),?_⟩
  intro B N W _ hb hw src dst row x y hx hy u S words free input empty
  obtain ⟨v,D,prep,user,ready,outside⟩ := load W N (dst-src).val B _ _ u S words free
    (fun z => (input z).symm) (fun z => (empty z).symm)
  obtain ⟨z,E,t,rotate,time,same,rep,_,_,_⟩ := ordinaryRotationRewound_exec
    (P := Empty) (U := U) Empty.elim fits hw src dst row x y hx hy (embDn bank v) (embStk bank D) ready
  obtain ⟨v',F,run,_,keep,view,off⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := body)
    bank.injective (fun e => nomatch e) rotate v rfl D rfl
  have cost := prepareRotation_cost hb (NeZero.pos N) hw (dst-src).isLt.le
  rw [← view] at rep
  refine ⟨v',F,_,Exec.seq prep run,by omega,keep.trans (same.trans user),?_,?_,?_⟩
  · intro z
    have h := (rep 10 z).symm
    change readAt blank (F.L (bank 10)) (F.R (bank 10)) (z-0) =
      putWord (fun _ => blank) 0 (List.ofFn fun k => SparseRoleCircuit.encode (x k)) z at h
    simpa only [sub_zero] using h
  · intro z
    have h := (rep 11 z).symm
    change readAt blank (F.L (bank 11)) (F.R (bank 11)) (z-0) =
      putWord (fun _ => blank) 0 (List.ofFn fun k => SparseRoleCircuit.encode (y k)) z at h
    simpa only [sub_zero] using h
  · intro j hj
    have a := off j hj
    have b := outside j (fun i => hj _)
    exact ⟨a.1.trans b.1,a.2.trans b.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
