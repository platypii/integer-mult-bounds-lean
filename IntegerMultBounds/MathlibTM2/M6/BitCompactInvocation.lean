module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffNode

/-! Shared owner tapes for both scalar phases and the intervening COPY sweep. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

/-- The three compiled child lists charge the exact contiguous invocation range. -/
theorem compactInvocation_bill (n : Fin 9) (p : Fin 32 × Fin 5) (time : ℕ → ℕ) :
    let phase := fun b => (List.ofFn (fun j =>
      time (phaseChildPositions.choose (n,p,selectedPhaseIndex b j)).val)).sum
    phase false + ((List.ofFn (fun j : CopyIndex => time (copyChildPosition (n,p,j)).val)).sum + phase true) =
      ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map time).sum := by
  intro phase
  have first (j) := (selectedPhaseIndex_spec false j).1
  have last (j) := (selectedPhaseIndex_spec true j).1
  have length_eq (gs : List RawGate) (cur : ℕ → ℕ) :
      (phaseMoveBlocks gs cur).1.length = ((Frames.edges gs cur).filter positiveMove).length := by
    simpa only [List.length_map] using congrArg List.length (phaseMoveBlocks_spec gs cur).1
  have len : (selectedPhaseSchedule false).1.length =
      ((Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length := by
    unfold selectedPhaseSchedule
    exact length_eq _ _
  have sum := invocationComponentChildSum n p time (selectedPhaseIndex false) (selectedPhaseIndex true)
    (fun j => by simpa only [Bool.false_eq_true,ite_false,Nat.zero_add] using first j)
    (fun j => by rw [len]; exact last j) selectedPhaseCount
  dsimp only at sum
  rw [← List.ofFn_eq_map,← List.ofFn_eq_map] at sum
  exact sum

/-- Place the three programs on disjoint private banks. Their owner charges
telescope and their ordered effects give the borrowed invocation. -/
theorem compactInvocation_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5)
    (tapes : Fin 3 → ℕ) (owners : ∀ j, Fin (142081+2) ↪ Fin (tapes j)) :
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    (∀ j i, bank j (owners j i) = fan i) ∧
    (∀ z, (∀ h, fan h ≠ z) → ∃ i l, (∀ h, owners i h ≠ l) ∧ bank i l = z) ∧
    (∀ i l, (∀ h, owners i h ≠ l) → (∀ h, fan h ≠ bank i l) ∧ ∀ j, j ≠ i → ∀ m, bank j m ≠ bank i l) ∧
    ∀ {P : Fin 3 → Type} {U : Type} {Q : ℕ} (body : ∀ j, P j → Pr (P j) (tapes j) Q prime U)
      (program : ∀ j, Pr (P j) (tapes j) Q prime U),
      let host := fun f : Σ j, P j => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
      ∃ code : Pr (Σ j, P j) T Q prime U, ∀ (w B K : ℕ),
      let V := (prime^w)^16*(B*prime^(64*(w*64))*K)
      ∀ (shared : Stacks (142081+2) prime) (seed : ∀ j, Stacks (tapes j) prime),
      ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
      (∀ i l, (∀ h, owners i h ≠ l) → prepared.L (bank i l) = (seed i).L l ∧ prepared.R (bank i l) = (seed i).R l) ∧
      ∀ price : Fin 3 → ℕ,
      (∀ j (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan (owners j) x S →
        (∀ k, (∀ h, owners j h ≠ k) → S.L k = (seed j).L k ∧ S.R k = (seed j).R k) →
        ∃ z F t y, Exec (body j) (program j) (mk u S) t (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots (owners j)) F)
            (price j+tapeCharge cleanupWeight (frameSlots (owners j)) S) ∧ HelperFan (owners j) y F ∧
          InvocationComponentEffect n p w B K j x y) →
      ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan x S →
        (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
        ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
            (price 0+(price 1+price 2)+tapeCharge cleanupWeight (frameSlots fan) S) ∧
          HelperFan fan y F ∧ BorrowedStep n w B K p x y := by
  obtain ⟨T,fan,bank,atOwner,cover,prepare,apart⟩ := copyWindowBanks tapes owners
  refine ⟨T,fan,bank,atOwner,cover,apart,?_⟩
  intro P U Q body program host
  let placed := fun j => embProg (bank j) (Sigma.mk j) (program j)
  refine ⟨(placed 0).seq ((placed 1).seq (placed 2)),?_⟩
  intro w B K V shared seed
  obtain ⟨prepared,view,initial⟩ := prepare shared seed
  refine ⟨prepared,view,initial,?_⟩
  intro price component x u S ready fresh
  let stock := fun D : Stacks T prime => tapeCharge cleanupWeight (frameSlots fan) D
  let saved := fun j (D : Stacks T prime) => ∀ k, (∀ h, owners j h ≠ k) →
    D.L (bank j k) = (seed j).L k ∧ D.R (bank j k) = (seed j).R k
  have project j (D : Stacks T prime) : embStk (owners j) (embStk (bank j) D) = embStk fan D := by
    simp only [embStk,Function.comp_def,atOwner]
  have charge j (D : Stacks T prime) : tapeCharge cleanupWeight (frameSlots (owners j)) (embStk (bank j) D) = stock D := by
    simp [stock,tapeCharge,frameSlots,List.map_reverse,Function.comp_def,embStk,atOwner]
  have start (j : Fin 3) : saved j S := fun k h => by
    obtain ⟨left,right⟩ := fresh _ (apart j k h).1
    exact ⟨left.trans (initial j k h).1,right.trans (initial j k h).2⟩
  have step (j : Fin 3) (a : Fin 142081 → Fin V → ZMod 2) v D (live : HelperFan fan a D) (privateSeed : saved j D) :
      ∃ z F t b, Exec host (placed j) (mk v D) t (mk z F) ∧ z.user = v.user ∧
        CleanupBound D F (t+stock F) (price j+stock D) ∧ HelperFan fan b F ∧
        InvocationComponentEffect n p w B K j a b ∧ ∀ i, i ≠ j → saved i D → saved i F := by
    obtain ⟨y,G,t,b,exec,user,paid,out,effect⟩ := component j a (embDn (bank j) v)
      (embStk (bank j) D) (by simpa only [HelperFan,project] using live) privateSeed
    obtain ⟨z,F,run,_,same,projection,off⟩ := exec_emb (body' := host) (ι := Sigma.mk j)
      (bank j).injective (fun _ => rfl) exec v rfl D rfl
    rw [← projection] at paid out
    rw [charge,charge] at paid
    refine ⟨z,F,t,b,run,same.trans user,CleanupBound.place (bank j) off paid,?_,effect,?_⟩
    · simpa only [HelperFan,project] using out
    · intro i ne keep k h
      obtain ⟨left,right⟩ := off (bank i k) ((apart i k h).2 j ne.symm)
      exact ⟨left.trans (keep k h).1,right.trans (keep k h).2⟩
  obtain ⟨v,D,l,a,left,userA,billA,liveA,effectA,keepA⟩ := step 0 x u S ready (start 0)
  obtain ⟨y,G,m,b,middle,userB,billB,liveB,effectB,keepB⟩ := step 1 a v D liveA (keepA 1 (by decide) (start 1))
  obtain ⟨z,F,t,out,right,userC,billC,done,effectC,_⟩ := step 2 b y G liveB
    (keepB 2 (by decide) (keepA 2 (by decide) (start 2)))
  refine ⟨z,F,_,out,left.seq (middle.seq right),userC.trans (userB.trans userA),?_,done,
    invocationComponentEffects n p x a b out effectA effectB effectC⟩
  intro js nd
  have ha := billA js nd
  have hb := billB js nd
  have hc := billC js nd
  change l+(m+t)+stock F+_ ≤ _+(price 0+(price 1+price 2)+stock S)
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
