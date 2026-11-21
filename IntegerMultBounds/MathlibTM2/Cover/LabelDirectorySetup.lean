module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryBuild
public import IntegerMultBounds.MathlibTM2.Cover.LabelCounts

/-! Initialize the label width, radix counter and box count from the unary atom width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDirectorySetup
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open Host Node RadixCounterData RadixDigits

variable {T Q : ℕ} {P U : Type} {body : P → Pr P T Q prime U}

def setup (m : ℕ) (r : Fin 15 ↪ Fin T) (atom one : Fin T) : Pr P T Q prime U :=
  .seq (umul (m*m) atom (r 11) (r 2))
    (.seq (umulSym (m*m) (digitSymbol (zeroDigit prime_prime.two_le)) atom (r 10) (r 2))
      (expProg 0 prime one (r 11) (r 4) (r 2) (r 3) (r 5)))

def prepared (R : Regs T prime) (r : Fin 15 ↪ Fin T) (L : ℕ) :=
  Function.update (Function.update (Function.update R (r 11) (List.replicate L tick))
    (r 10) ((zeros prime_prime.two_le L).map digitSymbol)) (r 4) (List.replicate (prime^L) tick)

theorem setup_exec (m : ℕ) (r : Fin 15 ↪ Fin T) (atom one : Fin T)
    (ha : ∀ i, atom ≠ r i) (ho : ∀ i, one ≠ r i) (v : HS T Q prime U) (S : Stacks T prime)
    (h1 : (S.R one).length = 1)
    (hf : ∀ i ∈ ([2,3,4,5,10,11] : List (Fin 15)), S.R (r i) = []) :
    let w := (S.R atom).length
    let L := w*(m*m)
    ∃ u n, u.user = v.user ∧ n ≤ 8*w+8+22*prime^L ∧ Exec body (setup m r atom one)
      (mk v S) n (mk u {S with R := prepared S.R r L}) := by
  intro w L
  obtain ⟨u,hu,he⟩ := umul_exec body (m*m) (ha 11) (ha 2) (by simp) v S (hf 2 (by simp))
  have mul : m*m*(S.R atom).length = L := Nat.mul_comm _ _
  rw [mul,hf 11 (by simp),List.append_nil] at he
  let M : Stacks T prime := {S with R := Function.update S.R (r 11) (List.replicate L tick)}
  obtain ⟨u',hu',he'⟩ := umulSym_exec body (m*m) (digitSymbol (zeroDigit prime_prime.two_le))
    (ha 10) (ha 2) (by simp) u M (by simp [M,hf 2 (by simp)])
  have width : M.R atom = S.R atom := by simp [M,ha]
  have empty : M.R (r 10) = [] := by simp [M,hf 10 (by simp)]
  rw [width,mul,empty,List.append_nil] at he'
  let H : Stacks T prime := {M with R := Function.update M.R (r 10) ((zeros prime_prime.two_le L).map digitSymbol)}
  have digits : List.replicate L (digitSymbol (zeroDigit prime_prime.two_le)) =
      (zeros prime_prime.two_le L).map digitSymbol := by simp [zeros]
  rw [digits] at he'
  have regs : [one,r 11,r 4,r 2,r 3,r 5].Nodup := by simp [ho]
  obtain ⟨u'',n,hu'',hn,run⟩ := LabelCounts.power_exec body regs u' H
    (by simpa [H,M,ho] using h1) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simp [H,M,hf])
  have len : (H.R (r 11)).length = L := by simp [H,M]
  rw [len] at run hn
  exact ⟨u'',_,hu''.trans (hu'.trans hu),by dsimp [w]; omega,Exec.seq he (Exec.seq he' run)⟩

/-- Start a per-record replay directly from the unary precision and record
count. Only the label width and zero seed occupy new workspace. -/
theorem replay_from_count (m boxesCount : ℕ) (r : Fin 15 ↪ Fin T) (atom : Fin T) (ha : ∀ i, atom ≠ r i)
    (v : HS T Q prime U) (S : Stacks T prime) (prefixes : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (fresh : ∀ i ∈ ([2,3,5,6,10,11] : List (Fin 15)), S.R (r i) = []) :
    let w := (S.R atom).length
    let L := w*(m*m)
    let N := (S.R (r 12)).length
    let W := (S.R (r 1)).length
    let R := Function.update (Function.update S.R (r 11) (List.replicate L tick))
      (r 10) ((zeros prime_prime.two_le L).map digitSymbol)
    0 < L → N = boxesCount*(prime^w)^(m*m) →
    S.R (r 0) = (List.range N).flatMap prefixes ++ tail → (∀ j < N, (prefixes j).length = W) →
    ∃ z n, z.user = v.user ∧ n ≤ 8*w+N*(6*W+15*L+28)+20 ∧
      Exec body ((umul (m*m) atom (r 11) (r 2)).seq
        ((umulSym (m*m) (digitSymbol (zeroDigit prime_prime.two_le)) atom (r 10) (r 2)).seq (LabelDirectoryBuild.replay r)))
        (mk v S) n (mk z {S with R := Function.update (Function.update R (r 0) tail) (r 14) ((List.range N).flatMap (LabelDirectory.entry prefixes m w) ++ S.R (r 14))}) := by
  intro w L N W R positive count source widths
  obtain ⟨u,user,clock⟩ := umul_exec body (m*m) (ha 11) (ha 2) (by simp) v S (fresh 2 (by decide))
  have mul : m*m*(S.R atom).length = L := Nat.mul_comm _ _
  rw [mul,fresh 11 (by decide),List.append_nil] at clock
  let M : Stacks T prime := {S with R := Function.update S.R (r 11) (List.replicate L tick)}
  obtain ⟨y,same,seed⟩ := umulSym_exec body (m*m) (digitSymbol (zeroDigit prime_prime.two_le))
    (ha 10) (ha 2) (by simp) u M (by simp [M,fresh 2 (by decide)])
  have atomWidth : M.R atom = S.R atom := by simp [M,ha]
  have empty : M.R (r 10) = [] := by simp [M,fresh 10 (by decide)]
  rw [atomWidth,mul,empty,List.append_nil] at seed
  let D : Stacks T prime := {S with R := R}
  obtain ⟨z,k,last,paid,run⟩ := LabelDirectoryBuild.replay_exec (body := body) r m w boxesCount prefixes tail y D
    positive (by simpa [D,R,N] using count) (by simpa [D,R,N] using source)
    (by simpa [D,R,N,W] using widths) (by simp [D,R,L]) (by simp [D,R,L]) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [D,R,fresh])
  have digits : List.replicate L (digitSymbol (zeroDigit prime_prime.two_le)) =
      (zeros prime_prime.two_le L).map digitSymbol := by simp [zeros]
  rw [digits] at seed
  refine ⟨z,4*w+4+(4*w+4+k),last.trans (same.trans user),?_,?_⟩
  · have bound : k ≤ N*(6*W+15*L+28)+12 := by simpa [D,R,N,W,L] using paid
    omega
  · simpa [D,R,N,M] using Exec.seq clock (Exec.seq seed run)

/-- Initialize the directory builder from unary widths and a child count. -/
theorem build_from_count (m : ℕ) (r : Fin 15 ↪ Fin T) (atom one : Fin T)
    (ha : ∀ i, atom ≠ r i) (ho : ∀ i, one ≠ r i) (v : HS T Q prime U) (S : Stacks T prime)
    (word : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    (h1 : (S.R one).length = 1)
    (fresh : ∀ i ∈ ([2,3,4,5,6,7,10,11,13] : List (Fin 15)), S.R (r i) = []) :
    let w := (S.R atom).length
    let L := w*(m*m)
    let B := prime^L
    let N := (S.R (r 9)).length
    let W := (S.R (r 1)).length
    0 < L → (S.R (r 12)).length = N*B →
    S.R (r 0) = (List.range N).flatMap word ++ tail → (∀ i < N, (word i).length = W) →
    ∃ u n, u.user = v.user ∧ n ≤ 8*w+8+22*B + (N*B*(9*L+15)+6 +
      (N*(B*(8*W+11)+6*W+15)+6 + N*B*(6*(W+L)+13)+6)) ∧
      Exec body (.seq (setup m r atom one) (LabelDirectoryBuild.program r)) (mk v S) n
        (mk u {S with R := Function.update (Function.update (prepared S.R r L) (r 0) tail) (r 14) ((List.range (N*B)).flatMap (LabelDirectory.entry (fun k => word (k/B)) m w) ++ S.R (r 14))}) := by
  intro w L B N W pos count hs hw
  obtain ⟨u,n,hu,hn,he⟩ := setup_exec (body := body) m r atom one ha ho v S h1 (by
    intro i hi; apply fresh; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto)
  let M : Stacks T prime := {S with R := prepared S.R r L}
  have box : (prime^w)^(m*m) = B := (pow_mul prime w (m*m)).symm
  have children : (M.R (r 12)).length = N*B := by simpa [M,prepared] using count
  obtain ⟨u',t,hu',ht,run⟩ := LabelDirectoryBuild.build_exec (body := body) r m w word tail u M pos
    (by simp [M,prepared,box,B]) (by simpa [M,prepared,box,N] using children)
    (by simpa [M,prepared,N] using hs) (by simpa [M,prepared,N,W] using hw)
    (by simp [M,prepared,L]) (by simp [M,prepared,L]) (by
      intro i hi
      have ne : i ≠ 4 ∧ i ≠ 10 ∧ i ≠ 11 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [M,prepared,Function.update_of_ne (r.injective.ne ne.1),
        Function.update_of_ne (r.injective.ne ne.2.1),Function.update_of_ne (r.injective.ne ne.2.2)]
      apply fresh
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto)
  refine ⟨u',n+t,hu'.trans hu,Nat.add_le_add hn (by simpa [M,prepared,box,N,W,L] using ht),?_⟩
  simpa [M,prepared,box,N,L] using Exec.seq he run

/-- Expand the parent count by the label-box size before writing the child directory. -/
theorem build_from_parents (m : ℕ) (r : Fin 15 ↪ Fin T) (atom one : Fin T)
    (ha : ∀ i, atom ≠ r i) (ho : ∀ i, one ≠ r i) (v : HS T Q prime U) (S : Stacks T prime)
    (word : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    (h1 : (S.R one).length = 1)
    (fresh : ∀ i ∈ ([2,3,4,5,6,7,10,11,12,13] : List (Fin 15)), S.R (r i) = []) :
    let w := (S.R atom).length
    let L := w*(m*m)
    let B := prime^L
    let N := (S.R (r 9)).length
    let W := (S.R (r 1)).length
    0 < L →
    S.R (r 0) = (List.range N).flatMap word ++ tail → (∀ i < N, (word i).length = W) →
    ∃ u n, u.user = v.user ∧ n ≤ 8*w+8+22*B + (N*(6*B+10)+6 + (N*B*(9*L+15)+6 +
      (N*(B*(8*W+11)+6*W+15)+6 + N*B*(6*(W+L)+13)+6))) ∧
      Exec body (.seq (setup m r atom one) (.seq (expandMask (r 9) (r 4) (r 2) (r 3) (r 5) (r 12) (fun _ => false)) (LabelDirectoryBuild.program r))) (mk v S) n
        (mk u {S with R := Function.update (Function.update (Function.update (prepared S.R r L) (r 12) (expandedMask B (fun _ => false) (S.R (r 9)))) (r 0) tail) (r 14) ((List.range (N*B)).flatMap (LabelDirectory.entry (fun k => word (k/B)) m w) ++ S.R (r 14))}) := by
  intro w L B N W pos hs hw
  obtain ⟨u,n,hu,hn,he⟩ := setup_exec (body := body) m r atom one ha ho v S h1 (by
    intro i hi; apply fresh; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  let M : Stacks T prime := {S with R := prepared S.R r L}
  have box : (prime^w)^(m*m) = B := (pow_mul prime w (m*m)).symm
  have blank (i : Fin 15) (hi : i ∈ [2,3,5,12]) : M.R (r i) = [] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [M,prepared,fresh]
  obtain ⟨y,c,hy,hc,countRun⟩ := expandMask_exec (body := body) (mask := r 9) (width := r 4)
    (saved := r 2) (tmp := r 3) (acc := r 5) (out := r 12) (by simp) B (fun _ => false) u M
    (by simp [M,prepared,B]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> apply blank <;> decide)
  simp only [blank 12 (by decide),List.append_nil] at countRun
  let C : Stacks T prime := {M with R := Function.update M.R (r 12) (expandedMask B (fun _ => false) (M.R (r 9)))}
  have children : (C.R (r 12)).length = N*B := by simp [C,M,prepared,N,expandedMask_length]
  obtain ⟨u',t,hu',ht,run⟩ := LabelDirectoryBuild.build_exec (body := body) r m w word tail y C pos
    (by simp [C,M,prepared,box,B]) (by simpa [C,M,prepared,box,N] using children)
    (by simpa [C,M,prepared,N] using hs) (by simpa [C,M,prepared,N,W] using hw)
    (by simp [C,M,prepared,L]) (by simp [C,M,prepared,L]) (by
      intro i hi
      have ne : i ≠ 12 ∧ i ≠ 4 ∧ i ≠ 10 ∧ i ≠ 11 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [C,M,prepared,Function.update_of_ne (r.injective.ne ne.1),
        Function.update_of_ne (r.injective.ne ne.2.1),Function.update_of_ne (r.injective.ne ne.2.2.1),Function.update_of_ne (r.injective.ne ne.2.2.2)]
      apply fresh
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨u',n+(c+t),hu'.trans (hy.trans hu),Nat.add_le_add hn (Nat.add_le_add (by simpa [M,prepared,N] using hc) (by simpa [C,M,prepared,box,N,W,L] using ht)),?_⟩
  simpa [C,M,prepared,box,N,L] using Exec.seq he (Exec.seq countRun run)

/-- Use the retained class mask itself to count the child records. -/
theorem build_from_mask (m : ℕ) (r : Fin 15 ↪ Fin T) (atom one : Fin T)
    (ha : ∀ i, atom ≠ r i) (ho : ∀ i, one ≠ r i) (v : HS T Q prime U) (S : Stacks T prime)
    (word : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4))) (keep : ℕ → Bool)
    (h1 : (S.R one).length = 1)
    (fresh : ∀ i ∈ ([2,3,4,5,6,7,10,11,13] : List (Fin 15)), S.R (r i) = []) :
    let w := (S.R atom).length
    let L := w*(m*m)
    let B := prime^L
    let N := (S.R (r 9)).length
    let W := (S.R (r 1)).length
    0 < L → S.R (r 12) = ((List.range (N*B)).map keep).map bitSymbol →
    S.R (r 0) = (List.range N).flatMap word ++ tail → (∀ i < N, (word i).length = W) →
    ∃ u n, u.user = v.user ∧ n ≤ 8*w+8+22*B + (N*B*(9*L+15)+6 +
      (N*(B*(8*W+11)+6*W+15)+6 + N*B*(6*(W+L)+13)+6)) ∧
      Exec body (.seq (setup m r atom one) (LabelDirectoryBuild.program r)) (mk v S) n
        (mk u {S with R := Function.update (Function.update (prepared S.R r L) (r 0) tail) (r 14) ((List.range (N*B)).flatMap (LabelDirectory.entry (fun k => word (k/B)) m w) ++ S.R (r 14))}) := by
  intro w L B N W pos mask hs hw
  exact build_from_count m r atom one ha ho v S word tail h1 fresh pos
    (by simp [mask,N,B,L,w]) hs hw

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDirectorySetup
