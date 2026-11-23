module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedReturnLoad
public import IntegerMultBounds.MathlibTM2.Host.EmitRun

/-! Prepare the return loader's unary fields from retained binary stage dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

def fieldSlot : Fin 4 ↪ Fin 8 := ⟨![0,3,5,6],by decide⟩

/-- Read the modulus width from the modulus word itself. The other three binary
dimensions supply the stage width, spectator count and transpose counter. -/
theorem returnFieldsFromBinary {T Q : ℕ} {A U : Type} (host : A → Pr A T Q prime U)
    (reg : Fin 8 ↪ Fin T) (source : Fin 4 → Fin T) (scratch : Fin 4 ↪ Fin T)
    (sourcesOff : ∀ i j, source i ≠ reg j) (scratchOff : ∀ i j, scratch i ≠ reg j)
    (separate : ∀ i j, source i ≠ scratch j) :
    ∃ code : Pr A T Q prime U, ∀ w W (parent : Fin 64 → ZMod (prime^(w+1))) u S,
      let M := prime^(w+1)
      let values := (![w+1,M,W,M^112*W] : Fin 4 → ℕ)
      0 < W → (∀ i, S.R (source i) = binSyms (values i).size (values i)) →
      S.R (reg 4) = (List.ofFn fun j => binSyms M.size (parent j).val).flatten →
      (∀ i, S.R (reg (fieldSlot i)) = []) → (∀ i, S.R (scratch i) = []) →
      ∃ z R t, Exec host code (mk u S) t (mk z {S with R := R}) ∧
        t ≤ 109*(M^128*W) ∧ z.user = u.user ∧
        (∀ i : Fin 8, i ≠ 1 → i ≠ 2 → i ≠ 7 →
          R (reg i) = returnSlotWord w (128*M.size) W 1 parent (returnSlots i)) ∧
        ∀ j, (∀ i, reg (fieldSlot i) ≠ j) → R j = S.R j := by
  let dst := fieldSlot.trans reg
  let emit (i : Fin 4) : Pr A T Q prime U :=
    if i = 1 then Node.umulSym 1 separator (source i) (dst i) (scratch 0)
    else emitRun (source i) (scratch 0) (dst i) (scratch 1) (scratch 2) (scratch 3) separator
  refine ⟨Cover.LabelTraversal.sequence emit (List.finRange 4),?_⟩
  intro w W parent u S M values positive binary archive empty free
  let V := M^128*W
  have hM : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have modulus : M ≤ V := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans
    (Nat.le_mul_of_pos_right _ positive)
  have width : w+1 ≤ V := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans modulus
  have spectator : W ≤ V := Nat.le_mul_of_pos_left _ (pow_pos hM _)
  have tail : M^112*W ≤ V := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hM (by decide : 112 ≤ 128))
  have sizeBound (i) : values i ≤ V := by fin_cases i <;> first | exact width | exact modulus | exact spectator | exact tail
  let count (i : Fin 4) := if i = 1 then (values i).size else values i
  obtain ⟨z,R,t,user,paid,exec,done,off⟩ := distinctTapeSequence host dst emit
    (List.finRange 4) (List.nodup_finRange _) (fun _ => []) (fun i => List.replicate (count i) separator)
    (fun _ => 27*V) u S empty (by
      intro i v F _ vacant keep
      have bin := (keep _ (fun j => (sourcesOff i (fieldSlot j)).symm)).trans (binary i)
      have blank j := (keep _ (fun k => (scratchOff j (fieldSlot k)).symm)).trans (free j)
      have digits : (values i).size ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (sizeBound i)
      by_cases h : i = 1
      · obtain ⟨y,same,run⟩ := Node.umulSym_exec (body := host) 1 separator
          (sourcesOff i (fieldSlot i)) (separate i 0) (scratchOff 0 (fieldSlot i)).symm v F (blank 0)
        change F.R (reg (fieldSlot i)) = [] at vacant
        rw [bin,length_binSyms,one_mul,vacant,List.append_nil] at run
        exact ⟨y,4*(values i).size+4,same,by omega,by simpa [emit,count,h,dst] using run⟩
      · have ports : [source i,scratch 0,dst i,scratch 1,scratch 2,scratch 3].Nodup := by
          simp [dst,List.nodup_cons,sourcesOff,scratchOff,separate,fun j k => (scratchOff j k).symm,scratch.injective.eq_iff]
        obtain ⟨y,k,same,bill,run⟩ := emitRun_exec (body := host) ports _ _ (Nat.lt_size_self _) separator v F bin
          (by intro j mem; simp only [List.mem_cons,List.not_mem_nil,or_false] at mem; rcases mem with rfl|rfl|rfl|rfl <;> exact blank _)
        rw [vacant,List.append_nil] at run
        exact ⟨y,k,same,by have := sizeBound i; omega,by simpa [emit,count,h,dst] using run⟩)
  have loaded (i) := done i (List.mem_finRange i)
  have frame j (away : ∀ i, dst i ≠ j) := off j (fun i _ => away i)
  refine ⟨z,R,t,exec,?_,user,?_,frame⟩
  · simp at paid
    omega
  · intro i a b c
    have dir := (frame (reg 4) (fun i => reg.injective.ne (by fin_cases i <;> decide))).trans archive
    fin_cases i <;> first | contradiction | exact dir | exact loaded 0 | exact loaded 1 | exact loaded 2 | exact loaded 3

/-- Run the physical stage from a parent directory and binary dimensions. -/
theorem runWithBinaryReturnFields {T N Q V : ℕ} {P A U : Type}
    (body : P → Pr P N Q prime U) (host : A → Pr A T Q prime U)
    (stage : Fin N ↪ Fin T) (label : P → A)
    (installed : ∀ p, host (label p) = embProg stage label (body p))
    (bank : Fin SweepFile.tapes ↪ Fin N) (src dst : Fin (142081+2) ↪ Fin N)
    (liveOff : ∀ i j, bank i ≠ src j)
    (reg : Fin 8 ↪ Fin T) (saved : Fin T)
    (apart : ∀ i j, stage i ≠ reg j) (saveOff : ∀ i, saved ≠ reg i)
    (saveBank : ∀ i, stage (bank i) ≠ saved) (source : Fin 4 → Fin T) (scratch : Fin 4 ↪ Fin T)
    (sourcesOff : ∀ i j, source i ≠ reg j) (scratchOff : ∀ i j, scratch i ≠ reg j)
    (separate : ∀ i j, source i ≠ scratch j) (piece : Pr P N Q prime U) :
    ∃ code : Pr A T Q prime U, ∀ w W (parent : Fin 64 → ZMod (prime^(w+1))) (seed : Stacks N prime) price effect,
      let M := prime^(w+1)
      let H := 128*M.size
      0 < W → seed.R ∘ bank = returnSeed w H W 1 parent →
      PackedPieceHandoff V effect body piece src dst seed price →
      ∀ x u S, ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk stage S) →
      (∀ j, (∀ i, src i ≠ j) → S.L (stage j) = seed.L j ∧
        ((∀ i, bank i ≠ j) → S.R (stage j) = seed.R j)) →
      (∀ i : Fin 4, let n := (![w+1,M,W,M^112*W] : Fin 4 → ℕ) i
        S.R (source i) = binSyms n.size n) →
      S.R (reg 4) = (List.ofFn fun j => binSyms M.size (parent j).val).flatten →
      (∀ i, S.R (reg (fieldSlot i)) = []) → (∀ i, S.R (scratch i) = []) →
      (∀ i, S.R (stage (bank i)) = []) → S.R (reg 1) = [] → S.R (reg 2) = [] →
      S.R (reg 7) = [] → S.R saved = [] →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ t ≤ 743*(M^128*W)+price ∧
        z.user = u.user ∧ ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk stage F) ∧ effect x y := by
  obtain ⟨build,prepare⟩ := returnFieldsFromBinary host reg source scratch sourcesOff scratchOff separate
  obtain ⟨call,run⟩ := runWithReturnFields body host stage label installed bank src dst liveOff
    reg saved apart saveOff saveBank piece
  refine ⟨build.seq call,?_⟩
  intro w W parent seed price effect M H positive seedBank pieceRun x u S words privateTapes binary archive vacant free blank hh hu ht hs
  obtain ⟨v,R,a,setup,cost,user,stock,off⟩ := prepare w W parent u S positive binary archive vacant free
  let D := {S with R := R}
  have stageR (j) := off (stage j) (fun i => (apart j (fieldSlot i)).symm)
  have project : embStk stage D = embStk stage S := by
    unfold embStk
    congr 1
    exact funext stageR
  have keep (j : Fin 8) (away : ∀ i, fieldSlot i ≠ j) := off (reg j) (fun i => reg.injective.ne (away i))
  obtain ⟨z,F,b,y,exec,paid,same,out,action⟩ := run w W parent seed price effect positive seedBank pieceRun x v D
    (project ▸ words) (fun j away => ⟨(privateTapes j away).1,fun h => (stageR j).trans ((privateTapes j away).2 h)⟩)
    stock (fun i => (stageR _).trans (blank i))
    ((keep 1 (by decide)).trans hh) ((keep 2 (by decide)).trans hu) ((keep 7 (by decide)).trans ht)
    ((off saved (fun i => (saveOff _).symm)).trans hs)
  refine ⟨z,F,_,y,setup.seq exec,?_,same.trans user,out,action⟩
  change a ≤ 109*(M^128*W) at cost
  change b ≤ 634*(M^128*W)+price at paid
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
