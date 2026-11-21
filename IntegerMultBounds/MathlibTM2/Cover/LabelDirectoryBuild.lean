module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryInherit

/-! Build the child directory directly from the parent stream and a zero radix counter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryBuild
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open Host Node RadixCounterData RadixDigits

private theorem advance_add (hq : 2 ≤ q) (i j : ℕ) (xs : List (Fin q)) :
    advance hq (i+j) xs = advance hq j (advance hq i xs) := by
  induction i generalizing xs with
  | zero => simp [advance]
  | succ i ih => rw [Nat.succ_add]; exact ih (increment hq xs)

private theorem boxes (hq : 2 ≤ q) (n L : ℕ) :
    advance hq (n*q^L) (zeros hq L) = zeros hq L := by
  induction n with
  | zero => simp [advance]
  | succ n ih => rw [Nat.succ_mul,advance_add,ih,full_cycle]

def gen : Fin 7 ↪ Fin 15 := ⟨![10,2,3,11,5,12,6],by decide⟩
def joinSlots : Fin 8 ↪ Fin 15 := ⟨![0,8,1,11,2,3,12,5],by decide⟩
def inheritSlots : Fin 8 ↪ Fin 15 := Fin.castLEEmb (by decide)

variable {T Q : ℕ} {P U : Type} {body : P → Pr P T Q prime U}

def program (r : Fin 15 ↪ Fin T) : Pr P T Q prime U :=
  .seq (LabelDirectoryLoop.write prime_prime.two_le (gen.trans r) (r 8))
    (.seq (LabelDirectoryInherit.expand (inheritSlots.trans r) (r 9) (r 13))
      (LabelDirectoryJoin.program (joinSlots.trans r) (r 14)))

theorem build_exec (r : Fin 15 ↪ Fin T) (m w : ℕ) (word : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (v : HS T Q prime U) (S : Stacks T prime) :
    let N := (S.R (r 9)).length
    let B := (prime^w)^(m*m)
    let W := (S.R (r 1)).length
    let L := w*(m*m)
    0 < L → (S.R (r 4)).length = B → (S.R (r 12)).length = N*B →
    S.R (r 0) = (List.range N).flatMap word ++ tail → (∀ i < N, (word i).length = W) →
    S.R (r 10) = (zeros prime_prime.two_le L).map digitSymbol → (S.R (r 11)).length = L →
    (∀ i ∈ ([2,3,5,6,7,13] : List (Fin 15)), S.R (r i) = []) →
    ∃ u n, u.user = v.user ∧ n ≤ N*B*(9*L+15)+6 + (N*(B*(8*W+11)+6*W+15)+6 + N*B*(6*(W+L)+13)+6) ∧
      Exec body (program r) (mk v S) n (mk u {S with R := Function.update (Function.update S.R (r 0) tail) (r 14) ((List.range (N*B)).flatMap (LabelDirectory.entry (fun k => word (k/B)) m w) ++ S.R (r 14))}) := by
  intro N B W L pos hB hN hs hw seed hl fresh
  let xs := zeros prime_prime.two_le L
  have g (i : Fin 7) : (gen.trans r) i = r (gen i) := rfl
  have ng (i : Fin 7) : (8 : Fin 15) ≠ gen i := by revert i; decide
  obtain ⟨u,n,hu,hn,he⟩ := LabelDirectoryLoop.write_exec (body := body) prime_prime.two_le
    (gen.trans r) (r 8) (fun i => by simpa [g] using ng i) xs (by simpa [xs] using pos) v S
    seed (by simpa [xs,gen] using hl) (by
      intro i hi
      apply fresh
      fin_cases i <;> simp_all [gen])
  have cycle : advance prime_prime.two_le (N*B) xs = xs := by
    simpa only [xs,B,L,pow_mul] using boxes prime_prime.two_le N L
  change (S.R (r 12)).length * _ + 6 ≥ n at hn
  rw [hN] at hn
  change Exec _ _ _ _ (mk u {S with R := Function.update (Function.update S.R (r 10)
    ((advance prime_prime.two_le (S.R (r 12)).length xs).map digitSymbol)) (r 8) (LabelDirectoryLoop.words prime_prime.two_le xs (S.R (r 12)).length ++ S.R (r 8))}) at he
  rw [hN,cycle,← seed,Function.update_eq_self] at he
  let M : Stacks T prime := {S with R := Function.update S.R (r 8) (LabelDirectoryLoop.words prime_prime.two_le xs (N*B) ++ S.R (r 8))}
  obtain ⟨u',t,hu',ht,run⟩ := LabelDirectoryInherit.directory_exec (body := body)
    (inheritSlots.trans r) (joinSlots.trans r) rfl rfl (r 9) (r 13) (r 14) (by simp)
    (fun i => r.injective.ne (show inheritSlots i ≠ 9 by revert i; decide))
    (fun i => r.injective.ne (show inheritSlots i ≠ 13 by revert i; decide))
    (fun i => r.injective.ne (show 14 ≠ joinSlots i by revert i; decide))
    m w word tail (S.R (r 8)) u M
    (by simpa [M,inheritSlots] using hB) (by simpa [M,joinSlots,N,inheritSlots] using hN)
    (by simpa [M,inheritSlots,N] using hs) (by simpa [M,inheritSlots,N,W] using hw)
    (by simp [M,joinSlots,N,B,xs,L]) (by simpa [M,joinSlots,L] using hl)
    (by intro i h; fin_cases i <;> simp_all [M,inheritSlots])
    (by simp [M,fresh 13 (by simp)])
    (by intro i h; fin_cases i <;> simp_all [M,joinSlots])
  refine ⟨u',n+t,hu'.trans hu,Nat.add_le_add (by simpa [xs] using hn) (by simpa [M,inheritSlots,N,B,W,L] using ht),?_⟩
  have run' := Exec.seq he run
  have restore : Function.update (Function.update S.R (r 0) tail) (r 8) (S.R (r 8)) = Function.update S.R (r 0) tail := by
    apply Function.update_eq_self_iff.mpr; simp
  simpa [program,M,joinSlots,N,B,Function.update_comm (show r 8 ≠ r 0 by simp),
    Function.update_idem,restore] using run'

/-- A replay stream already carries one inherited word per physical record.
Advance the child label counter alongside that stream and append its digits
to each record, retaining the caller's source and output suffixes. -/
def replay (r : Fin 15 ↪ Fin T) : Pr P T Q prime U :=
  (LabelDirectoryLoop.write prime_prime.two_le (gen.trans r) (r 8)).seq
    (LabelDirectoryJoin.program (joinSlots.trans r) (r 14))

theorem replay_exec (r : Fin 15 ↪ Fin T) (m w boxesCount : ℕ) (prefixes : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (v : HS T Q prime U) (S : Stacks T prime) :
    let N := (S.R (r 12)).length
    let L := w*(m*m)
    let W := (S.R (r 1)).length
    0 < L → N = boxesCount*(prime^w)^(m*m) →
    S.R (r 0) = (List.range N).flatMap prefixes ++ tail → (∀ j < N, (prefixes j).length = W) →
    S.R (r 10) = (zeros prime_prime.two_le L).map digitSymbol → (S.R (r 11)).length = L →
    (∀ i ∈ ([2,3,5,6] : List (Fin 15)), S.R (r i) = []) →
    ∃ u n, u.user = v.user ∧ n ≤ N*(6*W+15*L+28)+12 ∧
      Exec body (replay r) (mk v S) n (mk u {S with R := Function.update (Function.update S.R (r 0) tail) (r 14) ((List.range N).flatMap (LabelDirectory.entry prefixes m w) ++ S.R (r 14))}) := by
  intro N L W positive count source widths seed clock fresh
  let xs := zeros prime_prime.two_le L
  have cycle : advance prime_prime.two_le N xs = xs := by
    rw [count]
    simpa only [xs, L, pow_mul] using boxes prime_prime.two_le boxesCount L
  obtain ⟨z,k,user,paid,write⟩ := LabelDirectoryLoop.write_exec (body := body) prime_prime.two_le
    (gen.trans r) (r 8) (fun i => r.injective.ne (show 8 ≠ gen i by revert i; decide)) xs
    (by simpa [xs] using positive) v S seed (by simpa [xs,gen] using clock)
    (by intro i hi; fin_cases i <;> simp_all [gen])
  change Exec _ _ _ _ (mk z {S with R := Function.update (Function.update S.R (r 10)
    ((advance prime_prime.two_le N xs).map digitSymbol)) (r 8) (LabelDirectoryLoop.words prime_prime.two_le xs N ++ S.R (r 8))}) at write
  rw [cycle, ← seed, Function.update_eq_self] at write
  let D : Stacks T prime := {S with R := Function.update S.R (r 8) (LabelDirectoryLoop.words prime_prime.two_le xs N ++ S.R (r 8))}
  obtain ⟨u,t,same,price,join⟩ := LabelDirectoryJoin.directory_exec (body := body) (joinSlots.trans r)
    (r 14) (fun i => r.injective.ne (show 14 ≠ joinSlots i by revert i; decide)) m w prefixes z D tail (S.R (r 8))
    (by simpa [D,joinSlots,N] using source) (by simp [D,joinSlots,N,xs,L])
    (by simpa [D,joinSlots,N,W] using widths) (by simpa [D,joinSlots,L] using clock)
    (by intro i hi; fin_cases i <;> simp_all [D,joinSlots])
  refine ⟨u,k+t,same.trans user,?_,?_⟩
  · change k ≤ N*(9*xs.length+15)+6 at paid
    simp only [xs,zeros_length] at paid
    change t ≤ _ at price
    simp [D,joinSlots] at price
    dsimp only [W,N,L]
    dsimp only [W,N,L] at paid
    nlinarith
  · have restore : Function.update (Function.update S.R (r 0) tail) (r 8) (S.R (r 8)) = Function.update S.R (r 0) tail := by
      apply Function.update_eq_self_iff.mpr; simp
    simpa [replay,D,joinSlots,N,Function.update_comm (show r 8 ≠ r 0 by simp),
      Function.update_idem,restore] using Exec.seq write join

/-- Build the child directory and partition it by the mask retained from the payload split. -/
theorem split_exec (r : Fin 15 ↪ Fin T) (d : Fin 8 ↪ Fin T) (src : d 0 = r 14)
    (apart : ∀ i, d i ≠ r 0) (m w : ℕ) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool) (word : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (v : HS T Q prime U) (S : Stacks T prime) :
    let N := (S.R (r 9)).length
    let B := (prime^w)^(m*m)
    let W := (S.R (r 1)).length
    let L := w*(m*m)
    0 < L → (S.R (r 4)).length = B → (S.R (r 12)).length = N*B →
    S.R (r 0) = (List.range N).flatMap word ++ tail → (∀ i < N, (word i).length = W) →
    S.R (r 10) = (zeros prime_prime.two_le L).map digitSymbol → (S.R (r 11)).length = L →
    (∀ i ∈ ([2,3,5,6,7,13] : List (Fin 15)), S.R (r i) = []) →
    let ids := List.range (N*B)
    let keep := fun k => branch (LabelStock.residue m w 1 k)
    let entry := LabelDirectory.entry (fun k => word (k/B)) m w
    S.R (d 1) = (ids.map keep).map bitSymbol → (S.R (d 2)).length = W+L →
    (∀ i ∈ ([3,4,5,6] : List (Fin 8)), S.R (d i) = []) →
    let R := Function.update (Function.update S.R (r 0) tail) (r 14) (ids.flatMap entry ++ S.R (r 14))
    ∃ u n, u.user = v.user ∧ n ≤ N*B*(9*L+15)+6 + (N*(B*(8*W+11)+6*W+15)+6 +
      N*B*(6*(W+L)+13)+6) + 2*(N*B*(16*(W+L)+10)+16) ∧
      Exec body (.seq (program r) (LabelSplit.program (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7)))
        (mk v S) n (mk u {S with R := Function.update R (d 7) ((ids.filter keep).flatMap entry ++
          (ids.filter (fun k => !(keep k))).flatMap entry ++ S.R (d 7))}) := by
  intro N B W L pos hB hN hs hw seed hl fresh ids keep entry mask hwidth scratch R
  obtain ⟨u,n,hu,hn,he⟩ := build_exec (body := body) r m w word tail v S pos hB hN hs hw seed hl fresh
  let M : Stacks T prime := {S with R := R}
  have same (i : Fin 8) (hi : i ≠ 0) : M.R (d i) = S.R (d i) := by
    simp [M,R,← src,apart,hi]
  obtain ⟨u',t,hu',ht,run⟩ := LabelDirectory.split_exec (body := body)
    (src := d 0) (mask := d 1) (width := d 2) (symbols := d 3) (ts := d 4) (tm := d 5)
    (acc := d 6) (out := d 7) (by simp) ids m w W branch (fun k => word (k/B))
    (by intro k hk; exact hw _ ((Nat.div_lt_iff_lt_mul (pow_pos (pow_pos prime_prime.pos w) (m*m))).mpr
      (List.mem_range.mp hk))) u M (S.R (r 14)) (by simp [M,R,src,entry])
    ((same 1 (by decide)).trans mask) (by rwa [same 2 (by decide)]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> rw [same _ (by decide)] <;> apply scratch <;> simp)
  refine ⟨u',n+t,hu'.trans hu,Nat.add_le_add hn (by simpa [ids,L] using ht),?_⟩
  simpa only [same 7 (by decide)] using Exec.seq he run

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryBuild
