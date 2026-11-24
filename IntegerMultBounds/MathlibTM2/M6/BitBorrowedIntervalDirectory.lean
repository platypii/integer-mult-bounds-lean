module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalPackEntry
public import IntegerMultBounds.MathlibTM2.M6.BitCleanupBound

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
variable {P U : Type}

/-- A payload worker can borrow the directory in place. The enclosing call
restores every other tape and charges setup and release once each. -/
theorem withIntervalDirectory {T Q : ℕ} (body : P → Pr P T Q prime U) (bank : Fin 72 ↪ Fin T)
    (worker : Pr P T Q prime U) :
    let hdr := (copyRecordSources.trans intervalDirectoryPorts).trans bank
    ∃ code : Pr P T Q prime U, ∀ w W (v : HS T Q prime U) (S : Stacks T prime) (price : ℕ)
      (post : List (Fin (prime+4)) → List (Fin (prime+4)) → Prop),
      S.R (bank 2) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (bank 53) = binSyms W.size W → S.R (bank 28) = binSyms 1 1 →
      (∀ i, S.L (hdr i) = []) → (S.R (bank 71)).length = w+1 →
      (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (bank i) = []) →
      (∀ (a : HS T Q prime U) D, a.user = v.user →
        IntervalHeaderInputs (intervalDirectoryPorts.trans bank) (bank 59) w W D →
        (∀ j, (∀ i, hdr i ≠ j) → D.L j = S.L j) → (∀ j, bank 59 ≠ j → D.R j = S.R j) →
        ∃ z F n, Exec body worker (mk a D) n (mk z F) ∧ z.user = a.user ∧ CleanupBound D F n price ∧
          post (F.L (bank 24)) (F.R (bank 24)) ∧ ∀ j, j ≠ bank 24 → F.L j = D.L j ∧ F.R j = D.R j) →
      ∃ z F n, Exec body code (mk v S) n (mk z F) ∧ z.user = v.user ∧
        CleanupBound S F n (price+21*(w+1)+2*(w+1).size+18) ∧ post (F.L (bank 24)) (F.R (bank 24)) ∧
        ∀ j, j ≠ bank 24 → F.L j = S.L j ∧ F.R j = S.R j := by
  intro hdr
  obtain ⟨setup,init⟩ := intervalDirectorySetup_exec body bank
  obtain ⟨release,finish⟩ := intervalDirectoryRelease_exec body bank
  refine ⟨setup.seq (worker.seq release),?_⟩
  intro w W v S price post base suffix unit blankLeft clock empty run
  obtain ⟨a,D,t,start,paid,user,inputs,marked,left,right⟩ :=
    init w W v S base suffix unit blankLeft clock empty
  obtain ⟨y,E,k,work,same,bound,result,frame⟩ := run a D user inputs left right
  have away (i : Fin 3) : hdr i ≠ bank 24 := bank.injective.ne
    ((by decide : ∀ i, intervalDirectoryPorts (copyRecordSources i) ≠ 24) i)
  have width := frame _ (bank.injective.ne (by decide : (59 : Fin 72) ≠ 24))
  obtain ⟨z,F,done,final,clear,gone,offL,offR⟩ := finish y E
    (fun i => (frame _ (away i)).1.trans (marked i))
  have length : (E.R (bank 59)).length = (w+1).size := by rw [width.2,inputs.2,length_binSyms]
  have preserved (j) (ne : j ≠ bank 24) : F.L j = S.L j ∧ F.R j = S.R j := by
    constructor
    · by_cases h : ∃ i, hdr i = j
      · obtain ⟨i,rfl⟩ := h
        exact (clear i).trans (blankLeft i).symm
      · have off : ∀ i, hdr i ≠ j := fun i eq => h ⟨i,eq⟩
        exact (offL j off).trans ((frame j ne).1.trans (left j off))
    · by_cases h : bank 59 = j
      · subst j
        exact gone.trans (empty 59 (by decide) (by decide)).symm
      · exact (offR j h).trans ((frame j ne).2.trans (right j h))

  have afterL := offL _ away
  have afterR := offR _ (bank.injective.ne (by decide : (59 : Fin 72) ≠ 24))
  refine ⟨z,F,_,start.seq (work.seq done),final.trans (same.trans user),?_,by
    rwa [afterL,afterR],preserved⟩
  intro js distinct
  have bill := bound js distinct
  let wt := fun (l r : List (Fin (prime+4))) => 4*l.length+2*r.length+4
  have balance (xs : List (Fin T)) :
      tapeCharge wt xs F + tapeCharge wt xs D = tapeCharge wt xs S + tapeCharge wt xs E := by
    induction xs with
    | nil => rfl
    | cons j xs ih =>
      simp only [tapeCharge,List.map_cons,List.sum_cons] at ih ⊢
      by_cases h : j = bank 24
      · subst j
        rw [afterL,afterR,left _ away,right _ (bank.injective.ne (by decide : (59 : Fin 72) ≠ 24))]
        omega
      · rw [(preserved j h).1,(preserved j h).2,(frame j h).1,(frame j h).2]
        omega
  have eq := balance js
  change k + tapeCharge wt js E ≤ tapeCharge wt js D + price at bill
  change _ + tapeCharge wt js F ≤ tapeCharge wt js S + _
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
