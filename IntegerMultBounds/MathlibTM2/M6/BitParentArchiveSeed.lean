module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedHeaders
public import IntegerMultBounds.MathlibTM2.M6.BitParkedPackedChild
public import IntegerMultBounds.MathlibTM2.M6.BitCleanupBound

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

noncomputable def markArchivePorts {P U : Type} {T Q k : ℕ} (place : Fin k ↪ Fin T) (order : List (Fin k)) :
    Pr P T Q prime U :=
  Prog.seqList (order.map fun i => Prog.act (WordCmd.pushL (place i) [separator]))

private theorem markArchivePort_charge {T : ℕ} (S : Stacks T prime) (j : Fin T) (empty : S.L j = []) :
    CleanupBound S {S with L := Function.update S.L j [separator]} 1 5 := by
  let D := {S with L := Function.update S.L j [separator]}
  intro js distinct
  induction js with
  | nil => simp [tapeCharge]
  | cons i js ih =>
    change 1+(cleanupWeight (D.L i) (D.R i)+tapeCharge cleanupWeight js D) ≤
      cleanupWeight (S.L i) (S.R i)+tapeCharge cleanupWeight js S+5
    by_cases hit : i = j
    · subst i
      have tail : tapeCharge cleanupWeight js D = tapeCharge cleanupWeight js S := by
        unfold tapeCharge
        apply congrArg List.sum
        apply List.map_congr_left
        intro i mem
        have ne : i ≠ j := fun eq => distinct.notMem (eq ▸ mem)
        simp [D,Function.update_of_ne ne]
      rw [tail]
      simp [D,cleanupWeight,empty]
      omega
    · have head : cleanupWeight (D.L i) (D.R i) = cleanupWeight (S.L i) (S.R i) := by
        simp [D,Function.update_of_ne hit]
      have bound : 1+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+5 := ih distinct.tail
      rw [head]
      omega

theorem markArchivePorts_exec {P U : Type} {T Q k : ℕ} (body : P → Pr P T Q prime U)
    (place : Fin k ↪ Fin T) (order : List (Fin k)) (distinct : order.Nodup) (u : HS T Q prime U)
    (S : Stacks T prime) (free : ∀ i ∈ order, S.L (place i) = []) :
    ∃ L, Exec body (markArchivePorts place order) (mk u S) (order.length+1) (mk u {S with L := L}) ∧
      CleanupBound S {S with L := L} (order.length+1) (5*order.length+1) ∧
      (∀ i ∈ order, L (place i) = [separator]) ∧ ∀ j, (∀ i ∈ order, place i ≠ j) → L j = S.L j := by
  induction order generalizing S with
  | nil => exact ⟨S.L,Exec.act .done _,by intro js _; simp [Nat.add_comm],by simp,fun _ _ => rfl⟩
  | cons i rest ih =>
    let D := {S with L := Function.update S.L (place i) [separator]}
    have step : Exec body (Prog.act (WordCmd.pushL (place i) [separator])) (mk u S) 1 (mk u D) := by
      simpa only [WordCmd.pushL_run,List.reverse_singleton,free i List.mem_cons_self,List.append_nil,D] using
        Exec.act (body := body) (WordCmd.pushL (place i) [separator]) (mk u S)
    have away j (h : j ∈ rest) : j ≠ i := fun eq => distinct.notMem (eq ▸ h)
    obtain ⟨L,tail,bill,marked,off⟩ := ih distinct.tail D (fun j h =>
      (Function.update_of_ne (place.injective.ne (away j h)) ..).trans (free j (List.mem_cons_of_mem _ h)))
    refine ⟨L,?_,?_,?_,?_⟩
    · simpa only [markArchivePorts,List.map_cons,Prog.seqList,List.length_cons,Nat.add_comm 1] using step.seq tail
    · have paid := (markArchivePort_charge S (place i) (free i List.mem_cons_self)).seq bill
      convert paid using 1 <;> simp [Nat.mul_add] <;> omega
    · intro j h
      rcases List.mem_cons.mp h with rfl | h
      · exact (off _ (fun m hm => place.injective.ne (away m hm))).trans (Function.update_self ..)
      · exact marked j h
    · intro j h
      exact (off j (fun m hm => h m (List.mem_cons_of_mem _ hm))).trans
        (Function.update_of_ne (Ne.symm (h i List.mem_cons_self)) ..)

def parentArchivePorts : Fin 9 ↪ Fin (80+273) := ⟨![3,4,5,6,7,8,47,73,78],by decide⟩

/-- The source directory consists of the six descriptor headers followed by
the modulus, unit and unary width clock. -/
theorem parentArchiveSeed_words (node : Descriptor) (w : ℕ) :
    (fun i => (parentArchiveSeed node w).R (parentArchivePorts i)) =
      (fun j => Fin.addCases (motive := fun _ => List (Fin (prime+4))) (fun i : Fin 6 => (Routines.hdr node i).map bitSymbol)
        (![binSyms (prime^(w+1)).size (prime^(w+1)),binSyms 1 1,List.replicate w blank] :
          Fin 3 → List (Fin (prime+4))) j) := by
  funext i
  fin_cases i <;> rfl

theorem parentArchiveSeed_bill (node : Descriptor) (w : ℕ) :
    seedLoadBill (fun i => (parentArchiveSeed node w).R (parentArchivePorts i)) =
      seedLoadBill (fun i => (Routines.hdr node i).map bitSymbol)+8*((prime^(w+1)).size+1+w)+18 := by
  rw [parentArchiveSeed_words]
  unfold seedLoadBill
  rw [Fin.sum_univ_add (a := 6) (b := 3)]
  simp only [Fin.addCases_left,Fin.addCases_right]
  simp only [Fin.sum_univ_succ (n := 2),Fin.sum_univ_succ (n := 1),Fin.sum_univ_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ,length_binSyms,List.length_replicate]
  omega

private def descriptorMarks := (Fin.castAddEmb 3 (n := 6)).trans parentArchivePorts

private theorem archiveSeedRight_off (node : Descriptor) (w : ℕ) (j : Fin (80+273))
    (off : ∀ i, parentArchivePorts i ≠ j) : (parentArchiveSeed node w).R j = [] := by
  induction j using Fin.addCases with
  | right j => simp [parentArchiveSeed]
  | left j =>
    have miss (i : Fin 9) : (parentArchivePorts i).val ≠ j.val := fun h => off i (Fin.ext h)
    have outside : ¬ (3 ≤ j.val ∧ j.val < 9) := by
      have a := miss 0; have b := miss 1; have c := miss 2
      have d := miss 3; have e := miss 4; have f := miss 5
      change 3 ≠ j.val at a; change 4 ≠ j.val at b; change 5 ≠ j.val at c
      change 6 ≠ j.val at d; change 7 ≠ j.val at e; change 8 ≠ j.val at f
      omega
    have a : 47 ≠ j.val := miss 6
    have b : 73 ≠ j.val := miss 7
    have c : 78 ≠ j.val := miss 8
    simp [parentArchiveSeed,outside,Ne.symm a,Ne.symm b,Ne.symm c]

private theorem archiveSeedLeft_off (node : Descriptor) (w : ℕ) (j : Fin (80+273))
    (off : ∀ i, descriptorMarks i ≠ j) : (parentArchiveSeed node w).L j = [] := by
  induction j using Fin.addCases with
  | right j => simp [parentArchiveSeed]
  | left j =>
    have outside : ¬ (3 ≤ j.val ∧ j.val < 9) := by
      rintro ⟨lo,hi⟩
      let i : Fin 6 := ⟨j.val-3,by omega⟩
      have h (k : Fin 6) : (descriptorMarks k).val = 3+k.val := by fin_cases k <;> rfl
      exact off i (Fin.ext ((h i).trans (by dsimp [i]; omega)))
    simp [parentArchiveSeed,outside]

/-- Materialize the exact parent archive seed from the six descriptor words,
modulus, unit and width clock on the caller's tapes. -/
theorem loadParentArchiveSeed {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (80+273) ↪ Fin T) (source : Fin 9 → Fin T) (tmp saved : Fin T)
    (apart : ∀ i j, bank (parentArchivePorts i) ≠ source j)
    (regs : ∀ i, [source i,bank (parentArchivePorts i),tmp,saved].Nodup) :
    ∃ code, ∀ (node : Descriptor) (w : ℕ) u S, let seed := parentArchiveSeed node w
      (∀ i, S.R (source i) = seed.R (parentArchivePorts i)) →
      (∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (seedLoadBill (fun i => seed.R (parentArchivePorts i))+31) ∧
        (∀ j, F.L (bank j) = seed.L j ∧ F.R (bank j) = seed.R j) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let marks := descriptorMarks.trans bank
  let order := List.finRange 6
  obtain ⟨copy,load⟩ := installChildSeed body bank parentArchivePorts source tmp saved apart regs
  refine ⟨copy.seq (markArchivePorts marks order),?_⟩
  intro node w u S seed words free ht hs
  obtain ⟨v,R,t,start,user,price,stored,frame⟩ := load seed u S words (fun i => (free _).2) ht hs
  let D := {S with R := R}
  obtain ⟨L,finish,markBill,marked,off⟩ := markArchivePorts_exec body marks order (List.nodup_finRange _) v D (fun i _ => (free _).1)
  refine ⟨v,_,_,start.seq finish,user,?_,?_,?_⟩
  · exact (show CleanupBound S D t (seedLoadBill (fun i => seed.R (parentArchivePorts i))) from price).seq markBill
  · intro j
    refine ⟨?_,stored j (fun absent => (free j).2.trans (archiveSeedRight_off node w j absent).symm)⟩
    by_cases hit : ∃ i, descriptorMarks i = j
    · obtain ⟨i,rfl⟩ := hit
      have h := marked i (List.mem_finRange _)
      have eq : seed.L (descriptorMarks i) = [separator] := by fin_cases i <;> rfl
      exact h.trans eq.symm
    · exact (off _ (fun i _ eq => hit ⟨i,bank.injective eq⟩)).trans
        ((free j).1.trans (archiveSeedLeft_off node w j (fun i eq => hit ⟨i,eq⟩)).symm)
  · intro j away
    exact ⟨off j (fun i _ => away _),frame j (fun i => away _)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
