module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedCall

/-! Place the allocated COPY workers on a shared borrowed-row owner bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout Certificates.PR589

/-- All COPY workers share the permanent payload and controls. Each worker's
private initialization survives the earlier windows, and each scheduled
child is charged once in its own window. -/
theorem borrowedWindows_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    let J := Fin Copy.lifecycles.length
    ∃ (tapes : J → ℕ) (regs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j))
      (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (localBody : ∀ j, P → Pr P (tapes j) Q prime U) (proc : J → P),
    let body := fun f : J × P => embProg (bank f.1) (fun g => (f.1,g)) (localBody f.1 f.2)
    ∃ base swaps leaf fixed : J → ℕ, ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := fun j : J => scheduledChild prime node (copyChildPosition (n,p,j))
    let view := fun (x : Fin 142081 → Fin V → ZMod 2) k i => x k (Fin.cast (copyLabel_volume (w+1) blocks K) i)
    0 < W → ∃ position : ∀ j, Fin (volume prime (desc j)) ≃ Fin V,
      (∀ j k, (position j k).val = (CopyChildLayout.packActive (desc j) k).val) ∧
      ∀ record : J → List (Fin (prime+4)), ∀ shared : Stacks (142081+2) prime,
      ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧ ∀ budget : J → ℕ,
      (∀ j, ScheduledChildExec node (desc j) w W (regs j) (record j) (position j) (localBody j) (proc j) (budget j)) →
      let work := fun j => (base j+swaps j*swapVolumeRate w)*V + leaf j*LeafCore.coreCost V ((w+1)*64) + fixed j
      ∃ code, ∀ data u S, HelperFan fan data S →
        (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
        ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
          t ≤ (List.ofFn work).sum+(List.ofFn budget).sum+1 ∧ z.user = u.user ∧ HelperFan fan out F ∧
          CopyScheduleEffect n p.1 p.2 (w+1) blocks K Copy.lifecycles (view data) (view out) := by
  classical
  intro J
  choose tapes qs regs owners window using borrowedWindow_host n p
  obtain ⟨T,fan,bank,sharedAt,prepare,apart⟩ := copyWindowBanks tapes owners
  refine ⟨tapes,regs,T,Finset.univ.sup qs,fan,bank,?_⟩
  intro P U Q cap localBody proc body
  choose base swaps leaf fixed build using fun j : J =>
    window j ((Finset.le_sup (Finset.mem_univ j)).trans cap) (localBody j) (proc j)
  refine ⟨base,swaps,leaf,fixed,?_⟩
  intro node w B rows width split label M K blocks W V desc view pos
  choose position coords run using fun j => build j node w B rows width split label pos
  refine ⟨position,coords,?_⟩
  intro record shared
  choose init worker using fun j => run j (record j)
  obtain ⟨prepared,sharedEq,stored⟩ := prepare shared init
  refine ⟨prepared,sharedEq,?_⟩
  intro budget recurse work
  choose code step using fun j => worker j (budget j) (recurse j)
  let saved := fun j (S : Stacks T prime) => ∀ k, (∀ h, owners j h ≠ k) →
    S.L (bank j k) = (init j).L k ∧ S.R (bank j k) = (init j).R k
  have project (j : J) (S : Stacks T prime) : embStk (owners j) (embStk (bank j) S) = embStk fan S := by
    simp only [embStk,Function.comp_def,sharedAt]
  let price := fun j => work j + budget j
  obtain ⟨all,exec⟩ := copyWindows_exec body n p.1 p.2 (w+1) blocks K view (HelperFan fan) saved price (fun j => by
    refine ⟨embProg (bank j) (fun g => (j,g)) (code j),?_⟩
    intro data u S rep fresh
    obtain ⟨v,D,t,out,run,paid,user,done,act⟩ := step j data (embDn (bank j) u) (embStk (bank j) S)
      (by simpa only [HelperFan,project] using rep) fresh
    obtain ⟨z,F,placed,_,same,projection,off⟩ := exec_emb (ι := fun g => (j,g)) (body' := body)
      (bank j).injective (fun _ => rfl) run u rfl S rfl
    rw [← projection] at done
    refine ⟨z,F,t,out,placed,paid,same.trans user,?_,act,?_⟩
    · simpa only [HelperFan,project] using done
    · intro i ne keep k priv
      obtain ⟨l,r⟩ := off (bank i k) ((apart i k priv).2 j ne.symm)
      exact ⟨l.trans (keep k priv).1,r.trans (keep k priv).2⟩) (List.finRange _) (List.nodup_finRange _)
  rw [← List.ofFn_eq_map,← List.ofFn_eq_map,List.ofFn_getElem] at exec
  refine ⟨all,?_⟩
  intro data u S rep fresh
  obtain ⟨z,F,t,out,run,paid,user,done,act⟩ := exec data u S rep (fun i _ k priv => by
    obtain ⟨l,r⟩ := fresh _ (apart i k priv).1
    exact ⟨l.trans (stored i k priv).1,r.trans (stored i k priv).2⟩)
  refine ⟨z,F,t,out,run,?_,user,done,act⟩
  simpa only [price,List.sum_ofFn,Finset.sum_add_distrib] using paid

end IntegerMultBounds.MathlibTM2.M6.BitNode
