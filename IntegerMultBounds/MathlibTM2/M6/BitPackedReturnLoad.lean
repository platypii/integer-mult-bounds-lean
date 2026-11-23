module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedReturnHeaders
public import IntegerMultBounds.MathlibTM2.M6.BitParkedPackedChild

/-! Load the return sweep from persistent caller words into a blank sweep file. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

def returnSlots : Fin 8 ↪ Fin 66 := ⟨returnSeedSlots, by decide⟩

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

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
