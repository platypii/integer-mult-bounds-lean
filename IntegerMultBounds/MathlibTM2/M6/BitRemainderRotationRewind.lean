module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRotationHost

/-! Return both rotation heads together, using the blank preceding the encoded word. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

def rotationDataMove (m : Move) (i : Fin 14) := if i = 10 ∨ i = 11 then m else Move.stay

def rotationRewind {a : ℕ} : Program 14 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun s xs =>
    if s = 2 then none else
    if s = 1 ∧ xs 10 = blank then some (2, fun i => (xs i,rotationDataMove .right i))
    else some (1, fun i => (xs i,rotationDataMove .left i))

private noncomputable def rewindCfg (d : Tapes 10 0) (c : Tapes 2 0) (f g : ℤ → Fin (prime+4)) (p : ℤ)
    (s : Fin 3) : Config 14 3 prime :=
  ⟨s,(rotationBank d c p f g).head,(rotationBank d c p f g).tape⟩

private theorem rewindStep (d : Tapes 10 0) (c : Tapes 2 0) (f g : ℤ → Fin (prime+4))
    (p : ℤ) (s t : Fin 3) (m : Move)
    (h : rotationRewind.transition s (fun i => (rewindCfg d c f g p s).tape i
        ((rewindCfg d c f g p s).head i)) = some (t,fun i => ((rewindCfg d c f g p s).tape i
        ((rewindCfg d c f g p s).head i),rotationDataMove m i))) :
    step rotationRewind (rewindCfg d c f g p s) = some (rewindCfg d c f g (p+m.offset) t) := by
  unfold step
  change rotationRewind.transition (rewindCfg d c f g p s).state _ = _ at h
  rw [h]
  dsimp only [rewindCfg]
  congr 1
  congr 1
  · funext i
    fin_cases i <;> first | rfl | exact add_zero _
  · funext i j
    by_cases hj : j = (rotationBank d c p f g).head i
    · subst j; simp only [ite_true]; rfl
    · simp only [hj,ite_false]; rfl

theorem rotationRewind_hoare (d : Tapes 10 0) (c : Tapes 2 0) (f g : ℤ → Fin (prime+4))
    (n : ℕ) (word : ∀ i : Fin n, f i.val ≠ blank) (before : f (-1) = blank) :
    HoareTime rotationRewind (fun v => v = rotationBank d c n f g)
      (fun v => v = rotationBank d c 0 f g) (n+2) := by
  let cfg := rewindCfg d c f g
  have left (k : ℕ) (hk : k ≤ n) :
      run rotationRewind k (cfg (n-1 : ℤ) 1) = some (cfg ((n:ℤ)-1-k) 1) := by
    induction k with
    | zero => simp [run]
    | succ k ih =>
      rw [run_add,ih (by omega),Option.bind_some,run_one]
      have hn := word (⟨n-1-k,by omega⟩ : Fin n)
      have pos : ((n-1-k : ℕ) : ℤ) = (n:ℤ)-1-k := by omega
      rw [pos] at hn
      have move := rewindStep d c f g ((n:ℤ)-1-k) 1 1 .left (by
        have read : (cfg ((n:ℤ)-1-k) 1).tape 10 ((cfg ((n:ℤ)-1-k) 1).head 10) ≠ blank := hn
        simp only [rotationRewind,show (1:Fin 3) ≠ 2 by decide,↓reduceIte,true_and]
        exact ite_eq_right read)
      convert move using 2; simp [cfg,Move.offset]; congr 1; omega
  rintro v rfl
  refine ⟨1+n+1,cfg 0 2,by omega,?_,?_,rfl⟩
  · rw [run_add,run_add,run_one]
    have start := rewindStep d c f g n 0 1 .left (by rfl)
    change step rotationRewind (cfg n 0) = _ at start
    change ((step rotationRewind (cfg n 0)).bind _).bind _ = _
    rw [start,Option.bind_some]
    change (run rotationRewind n (cfg ((n:ℤ)-1) 1)).bind _ = _
    rw [left n le_rfl,Option.bind_some,run_one]
    rw [show (n:ℤ)-1-n = -1 by omega]
    exact rewindStep d c f g (-1) 1 2 .right (by
      have read : (cfg (-1) 1).tape 10 ((cfg (-1) 1).head 10) = blank := before
      simp only [rotationRewind,show (1:Fin 3) ≠ 2 by decide,↓reduceIte,true_and]
      exact ite_eq_left read)
  · rfl

open Stack Host
open FlatCoordinateSchedule (bits)

theorem ordinaryRotationRewound_exec {P U : Type} {Q B N W : ℕ} [NeZero N]
    (body : P → Pr P 14 Q prime U) (fits : 235 ≤ Q) (hw : 0 < W) (src dst : Fin N)
    (row : Fin B → Fin W → ZMod 2) (x y : Fin ((B*N)*W) → ZMod 2)
    (hx : ∀ b j k, x (finProdFinEquiv (finProdFinEquiv (b,j),k)) = if j = src then row b k else 0)
    (hy : ∀ b j k, y (finProdFinEquiv (finProdFinEquiv (b,j),k)) = if j = dst then row b k else 0) :
    let a := (dst-src).val
    let tape := fun f : Fin ((B*N)*W) → ZMod 2 =>
      putWord (fun _ => blank) 0 (List.ofFn (fun j => SparseRoleCircuit.encode (a := prime) (f j)))
    let start := rotationBank (TranslationDescriptors.initial (bits W) (bits N) (bits a))
      (CountedLoopReuse.controls (fun _ => blank) (CountedCopyReuse.binary (bits B)) 0 1)
      0 (tape x) (fun _ => blank)
    let finish := rotationBank (TranslationDescriptors.bank (fun _ => []) (bits W) (bits N) (bits a)
      (fun _ => blank) 0) (CountedLoopReuse.controls CountedCopyReuse.empty (CountedCopyReuse.binary (bits B)) 1 1)
      0 (tape x) (tape y)
    let machine := liftQ (Alphabet.program (CountedLoopReuseAlphabet.encoding prime) TranslationStream.program) fits
    ∀ u S, RepT start S.L S.R → ∃ v D t, Exec body ((foreign machine).seq (foreign (liftQ rotationRewind (by omega : 3 ≤ Q)))) (mk u S) t (mk v D) ∧
      t ≤ (462*(B*(N*W))+27)*19+12 ∧ v.user = u.user ∧ RepT finish D.L D.R ∧
      D.inp = S.inp ∧ D.out = S.out ∧ ∀ i, (D.L i).length+(D.R i).length ≤
        (S.L i).length+(S.R i).length+2*(462*(B*(N*W))+27) := by
  intro a tape start finish machine u S live
  obtain ⟨v,D,t,rotate,ht,user,rep,inp,out,stock⟩ := ordinaryRotation_exec body fits hw src dst row x y hx hy u S live
  let n := B*(N*W)
  have hn : n = (B*N)*W := (Nat.mul_assoc ..).symm
  have word (i : Fin n) : tape x i.val ≠ blank := by
    let xs := List.ofFn (fun j => SparseRoleCircuit.encode (a := prime) (x j))
    have hi : i.val < xs.length := by simp [xs,← hn]
    have atCell := BinaryDivide.putWord_getElem (fun _ => blank) 0 xs i.val hi
    simp only [zero_add] at atCell
    change putWord _ 0 xs _ ≠ blank
    rw [atCell]
    simp only [xs,List.getElem_ofFn,SparseRoleCircuit.encode]
    cases decide (x ⟨i.val,by omega⟩ = 1) <;> decide
  have before : tape x (-1) = blank := putWord_outside _ _ _ _ (Or.inl (by decide))
  have rewind := rotationRewind_hoare
    (TranslationDescriptors.bank (fun _ => []) (bits W) (bits N) (bits a) (fun _ => blank) 0)
    (CountedLoopReuse.controls CountedCopyReuse.empty (CountedCopyReuse.binary (bits B)) 1 1) (tape x) (tape y) n word before
  obtain ⟨z,E,_,rfl,ready,same,ei,eo,sz,k,hk,back⟩ := foreign_exec (body := body) _
    (HoareTime.liftQ (by omega : 3 ≤ Q) rewind) v D _ rfl rep
  refine ⟨z,E,_,Exec.seq rotate back,?_,same.trans user,ready,ei.trans inp,eo.trans out,?_⟩
  · dsimp [n] at hk; omega
  · intro i
    have := sz i
    have := stock i
    dsimp only [n] at *
    omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
