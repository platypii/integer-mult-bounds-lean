module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedReturnHeaders
public import IntegerMultBounds.MathlibTM2.M6.BitParkedPackedChild

/-! Load the return sweep from persistent caller words into a blank sweep file. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

def returnSlots : Fin 8 ↪ Fin 66 := ⟨returnSeedSlots, by decide⟩

/-- The archive digit count also determines a legal row-address width. -/
theorem returnHeight_fits {M : ℕ} (hm : 2 ≤ M) :
    M^128 < 2^(128*M.size) ∧ 128*M.size ≤ M^128+1 := by
  constructor
  · rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left (Nat.lt_size_self M) (by decide)
  · have factor : 128 ≤ M^127 :=
      (by decide : 128 ≤ 2^7) |>.trans ((Nat.pow_le_pow_left hm 7).trans
        (Nat.pow_le_pow_right (by omega) (by decide : 7 ≤ 127)))
    have digits : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
    have bound := Nat.mul_le_mul factor digits
    rw [pow_succ M 127]
    omega

/-- Both transpose counters at the packed stage read the same retained word. -/
def returnSource (reg : Fin 8 ↪ Fin T) (i : Fin 8) : Fin T :=
  if i = 7 then reg 6 else reg i

/-- Generate the row-address width and unit word from five retained header fields.
The last register is temporary during setup and can be reused by the loader. -/
theorem prepareReturnSources {T Q : ℕ} {A U : Type} (host : A → Pr A T Q prime U)
    (reg : Fin 8 ↪ Fin T) :
    ∃ code : Pr A T Q prime U, ∀ w W (parent : Fin 64 → ZMod (prime^(w+1))) u S,
      let M := prime^(w+1)
      let H := 128*M.size
      (∀ i : Fin 8, i ≠ 1 → i ≠ 2 → i ≠ 7 →
        S.R (reg i) = returnSlotWord w H W 1 parent (returnSlots i)) →
      S.R (reg 1) = [] → S.R (reg 2) = [] → S.R (reg 7) = [] →
      ∃ z R t, Exec host code (mk u S) t (mk z {S with R := R}) ∧ t ≤ 4*M.size+5 ∧
        z.user = u.user ∧ (∀ i, R (returnSource reg i) = returnSlotWord w H W 1 parent (returnSlots i)) ∧
        ∀ j, j ≠ reg 1 → j ≠ reg 2 → R j = S.R j := by
  let push : Pr A T Q prime U := .act (.push (.rt (reg 2)) (fun _ => separator) .done)
  refine ⟨(Node.umulSym 128 separator (reg 3) (reg 1) (reg 7)).seq push,?_⟩
  intro w W parent u S M H stock emptyHeight emptyUnit tmp
  have digits : (S.R (reg 3)).length = M.size := by
    rw [stock 3 (by decide) (by decide) (by decide)]
    exact List.length_replicate
  obtain ⟨v,user,build⟩ := Node.umulSym_exec (body := host) 128 separator
    (reg.injective.ne (by decide : (3 : Fin 8) ≠ 1)) (reg.injective.ne (by decide : (3 : Fin 8) ≠ 7))
    (reg.injective.ne (by decide : (1 : Fin 8) ≠ 7)) u S tmp
  rw [digits,emptyHeight,List.append_nil] at build
  let D := {S with R := Function.update S.R (reg 1) (List.replicate H separator)}
  let R := Function.update D.R (reg 2) [separator]
  have mark : Exec host push (mk v D) 1 (mk v {S with R := R}) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,update_rt,D,R,reg.injective.eq_iff,emptyUnit]
  refine ⟨v,R,_,build.seq mark,by omega,user,?_,?_⟩
  · intro i
    by_cases h : i = 7
    · subst i
      simpa [returnSource,R,D,reg.injective.eq_iff,returnSlots,returnSeedSlots,returnSlotWord] using
        stock 6 (by decide) (by decide) (by decide)
    by_cases a : i = 1
    · subst i
      simp [returnSource,R,D,reg.injective.eq_iff,returnSlotWord,returnSlots,returnSeedSlots]
    by_cases b : i = 2
    · subst i
      simp [returnSource,R,returnSlotWord,returnSlots,returnSeedSlots]
    simpa [returnSource,h,R,D,reg.injective.eq_iff,a,b] using stock i a b h
  · intro j a b
    simp [R,D,a,b]

theorem loadReturnHeaders {T Q : ℕ} {A U : Type} (host : A → Pr A T Q prime U)
    (bank : Fin SweepFile.tapes ↪ Fin T) (source : Fin 8 → Fin T) (tmp saved : Fin T)
    (apart : ∀ i j, bank (work (returnSlots i)) ≠ source j)
    (regs : ∀ i, [source i,bank (work (returnSlots i)),tmp,saved].Nodup) :
    ∃ code : Pr A T Q prime U, ∀ w H W (parent : Fin 64 → ZMod (prime^(w+1))),
      0 < W → H ≤ (prime^(w+1))^128+1 →
      ∀ u S, (∀ i, S.R (source i) = returnSlotWord w H W 1 parent (returnSlots i)) →
      (∀ i, S.R (bank i) = []) → S.R tmp = [] → S.R saved = [] →
      ∃ z R t, Exec host code (mk u S) t (mk z {S with R := R}) ∧
        t + (∑ i, 2*(R (bank (work (returnSlots i)))).length) ≤ 625*((prime^(w+1))^128*W) ∧
        z.user = u.user ∧ R ∘ bank = returnSeed w H W 1 parent ∧ ∀ j, (∀ i, bank i ≠ j) → R j = S.R j := by
  let target := (returnSlots.trans work).trans bank
  obtain ⟨code,run⟩ := reloadChildSeed host target source tmp saved apart regs
  refine ⟨code,?_⟩
  intro w H W parent positive height u S stock blank ht hs
  let word i := returnSlotWord w H W 1 parent (returnSlots i)
  obtain ⟨z,R,t,exec,paid,user,loaded,off⟩ := run word u S stock (fun i => blank _) ht hs
  have atFile (r : File) : R (bank (Fintype.equivFin File r)) = returnFileWord w H W 1 parent r := by
    by_cases hit : ∃ i, SweepFile.Register.work (returnSlots i) = r
    · obtain ⟨i,rfl⟩ := hit
      exact loaded i
    · rw [off _ (fun i => bank.injective.ne ((Fintype.equivFin File).injective.ne (fun eq => hit ⟨i,eq⟩))),blank]
      cases r with
      | work j => exact (returnSlotWord_empty _ _ _ _ _ _ (fun i eq => hit ⟨i,congrArg _ eq⟩)).symm
      | _ => rfl
  have view : R ∘ bank = returnSeed w H W 1 parent := by
    funext j
    obtain ⟨r,rfl⟩ := (Fintype.equivFin File).surjective j
    simpa [returnSeed] using atFile r
  refine ⟨z,R,t,exec,?_,user,view,
    fun j away => off j (fun i => away _)⟩
  change t + (∑ i, 2*(R (target i)).length) ≤ _
  simp only [loaded]
  rw [← List.sum_toFinset _ (List.nodup_finRange 8)] at paid
  have allSlots : (List.finRange 8).toFinset = Finset.univ := by ext; simp
  rw [allSlots] at paid
  have combined : (∑ i, (6*(word i).length+6)) + (∑ i, 2*(word i).length) =
      ∑ i, (8*(word i).length+6) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by omega)
  have bound : (∑ i, (8*(word i).length+6))+1 ≤ _ := returnSeed_copyCost_le w H W parent positive height
  omega

/-- Prepend return-file loading to a physical piece on an embedded stage bank. -/
theorem runWithReturnHeaders {T N Q V : ℕ} {P A U : Type}
    (body : P → Pr P N Q prime U) (host : A → Pr A T Q prime U)
    (stage : Fin N ↪ Fin T) (label : P → A)
    (installed : ∀ p, host (label p) = embProg stage label (body p))
    (bank : Fin SweepFile.tapes ↪ Fin N) (src dst : Fin (142081+2) ↪ Fin N)
    (liveOff : ∀ i j, bank i ≠ src j)
    (source : Fin 8 → Fin T) (tmp saved : Fin T)
    (apart : ∀ i j, stage (bank (work (returnSlots i))) ≠ source j)
    (regs : ∀ i, [source i,stage (bank (work (returnSlots i))),tmp,saved].Nodup)
    (piece : Pr P N Q prime U) :
    ∃ code : Pr A T Q prime U, ∀ w H W (parent : Fin 64 → ZMod (prime^(w+1))) (seed : Stacks N prime) price effect,
      0 < W → H ≤ (prime^(w+1))^128+1 → seed.R ∘ bank = returnSeed w H W 1 parent →
      PackedPieceHandoff V effect body piece src dst seed price →
      ∀ x u S, ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk stage S) →
      (∀ j, (∀ i, src i ≠ j) → S.L (stage j) = seed.L j ∧
        ((∀ i, bank i ≠ j) → S.R (stage j) = seed.R j)) →
      (∀ i, S.R (source i) = returnSlotWord w H W 1 parent (returnSlots i)) →
      (∀ i, S.R (stage (bank i)) = []) → S.R tmp = [] → S.R saved = [] →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ t ≤ 625*((prime^(w+1))^128*W)+price ∧
        z.user = u.user ∧ ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk stage F) ∧ effect x y := by
  obtain ⟨load,prepare⟩ := loadReturnHeaders host (bank.trans stage) source tmp saved apart regs
  refine ⟨load.seq (embProg stage label piece),?_⟩
  intro w H W parent seed price effect positive height seedBank run x u S words privateTapes stock empty ht hs
  obtain ⟨v,R,a,setup,bill,user,view,off⟩ := prepare w H W parent positive height u S stock empty ht hs
  let D := {S with R := R}
  have keep (j) (away : ∀ i, bank i ≠ j) : R (stage j) = S.R (stage j) :=
    off _ (fun i => stage.injective.ne (away i))
  have live (j) := keep (src j) (fun i => liveOff i j)
  obtain ⟨z,F,b,y,exec,paid,same,out,action⟩ := run x (embDn stage v) (embStk stage D)
    ⟨words.left,fun i => (live _).trans (words.right i),by
      intro j k
      simpa only [embStk,Function.comp_apply,D,live] using words.controls j k⟩ (by
        intro j away
        refine ⟨(privateTapes j away).1,?_⟩
        by_cases hit : ∃ i, bank i = j
        · obtain ⟨i,rfl⟩ := hit
          exact congrFun (view.trans seedBank.symm) i
        · have outside := fun i eq => hit ⟨i,eq⟩
          exact (keep j outside).trans ((privateTapes j away).2 outside))
  obtain ⟨q,G,lifted,_,sameUser,project,_⟩ := exec_emb stage.injective installed exec v rfl D rfl
  refine ⟨q,G,_,y,setup.seq lifted,by omega, sameUser.trans (same.trans user),?_,action⟩
  rw [project]
  exact out

/-- Run a stage from the five caller fields, generating the remaining return words. -/
theorem runWithReturnFields {T N Q V : ℕ} {P A U : Type}
    (body : P → Pr P N Q prime U) (host : A → Pr A T Q prime U)
    (stage : Fin N ↪ Fin T) (label : P → A)
    (installed : ∀ p, host (label p) = embProg stage label (body p))
    (bank : Fin SweepFile.tapes ↪ Fin N) (src dst : Fin (142081+2) ↪ Fin N)
    (liveOff : ∀ i j, bank i ≠ src j)
    (reg : Fin 8 ↪ Fin T) (saved : Fin T)
    (apart : ∀ i j, stage i ≠ reg j) (saveOff : ∀ i, saved ≠ reg i)
    (saveBank : ∀ i, stage (bank i) ≠ saved) (piece : Pr P N Q prime U) :
    ∃ code : Pr A T Q prime U, ∀ w W (parent : Fin 64 → ZMod (prime^(w+1))) (seed : Stacks N prime) price effect,
      let M := prime^(w+1)
      let H := 128*M.size
      0 < W → seed.R ∘ bank = returnSeed w H W 1 parent →
      PackedPieceHandoff V effect body piece src dst seed price →
      ∀ x u S, ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk stage S) →
      (∀ j, (∀ i, src i ≠ j) → S.L (stage j) = seed.L j ∧
        ((∀ i, bank i ≠ j) → S.R (stage j) = seed.R j)) →
      (∀ i : Fin 8, i ≠ 1 → i ≠ 2 → i ≠ 7 →
        S.R (reg i) = returnSlotWord w H W 1 parent (returnSlots i)) →
      (∀ i, S.R (stage (bank i)) = []) → S.R (reg 1) = [] → S.R (reg 2) = [] →
      S.R (reg 7) = [] → S.R saved = [] →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ t ≤ 634*(M^128*W)+price ∧
        z.user = u.user ∧ ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk stage F) ∧ effect x y := by
  obtain ⟨build,prepare⟩ := prepareReturnSources host reg
  have source (i) : ∃ j : Fin 8, returnSource reg i = reg j ∧ j ≠ 7 := by
    by_cases h : i = 7
    · exact ⟨6,by simp [returnSource,h],by decide⟩
    · exact ⟨i,by simp [returnSource,h],h⟩
  obtain ⟨load,run⟩ := runWithReturnHeaders body host stage label installed bank src dst liveOff (returnSource reg) (reg 7) saved
    (fun i j => by obtain ⟨k,eq,_⟩ := source j; rw [eq]; exact apart _ _)
    (fun i => by
      obtain ⟨k,eq,ne⟩ := source i
      simp [eq,List.nodup_cons,apart,fun i j => (apart i j).symm,
        fun i => (saveOff i).symm,saveBank,reg.injective.eq_iff,ne]) piece
  refine ⟨build.seq load,?_⟩
  intro w W parent seed price effect M H positive seedBank pieceRun x u S words privateTapes stock blank hh hu ht hs
  obtain ⟨v,R,a,setup,cost,user,fields,keep⟩ := prepare w W parent u S stock hh hu ht
  let D := {S with R := R}
  have stageR (i) := keep (stage i) (apart i 1) (apart i 2)
  have project : embStk stage D = embStk stage S := by
    unfold embStk
    congr 1
    exact funext stageR
  have modulus : 2 ≤ M := Shared50ModularControl.prime_prime.two_le.trans
    (Nat.le_self_pow (by omega : w+1 ≠ 0) _)
  obtain ⟨z,F,b,y,exec,paid,same,out,action⟩ := run w H W parent seed price effect positive
    (returnHeight_fits modulus).2 seedBank pieceRun x v D (project ▸ words) (by
      intro j away
      exact ⟨(privateTapes j away).1,fun h => (stageR j).trans ((privateTapes j away).2 h)⟩)
    fields (fun i => (stageR _).trans (blank i))
    ((keep _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans ht)
    ((keep _ (saveOff 1) (saveOff 2)).trans hs)
  refine ⟨z,F,_,y,setup.seq exec,?_,same.trans user,out,action⟩
  have digits : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have vol : M ≤ M^128*W := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans
    (Nat.le_mul_of_pos_right _ positive)
  change a ≤ 4*M.size+5 at cost
  change b ≤ 625*(M^128*W)+price at paid
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
