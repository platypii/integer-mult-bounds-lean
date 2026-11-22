module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleCall

/-! Schedule the strictly smaller remainder calls on their represented owners. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

theorem flatIdleSchedule_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (node : Descriptor) (i : Fin 9) (w rows : ℕ) (hw : 0 < w)
    (width : node.width = 64*w) (split : node.rows = 142080*rows)
    (fan : Fin (142081+2) ↪ Fin T) (initial : Stacks T prime)
    (proc : (Fin 32 × Fin 5) × Fin 222 → P) (budget : Fin nodeChildren5.length → ℕ) :
    let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
    let V := (prime^w)^128*W
    let index := fun k => idleDirectoryIndex (i,idleCopyIndex k)
    let child := fun k => scheduledChild prime node (index k)
    let outside := fun (S : Stacks T prime) => ∀ t, (∀ l, fan l ≠ t) →
      S.L t = initial.L t ∧ S.R t = initial.R t
    ∃ position : ∀ k, Fin (volume prime (child k)) ≃ Fin V,
      (∀ k, IdleChildPositions i k.2 w W (child k) (position k)) ∧
      ((∀ k (x : Fin 142081 → Fin V → ZMod 2) u S, let port := fan ((idleTape i k).castAdd 2)
        (child k).width < node.width → HelperFan fan x S → outside S →
        ∃ z F n changed, Exec body (body (proc k)) (mk u S) n (mk z F) ∧ n ≤ budget (index k) ∧
          z.user = u.user ∧ RecordPayload port (fun _ => blank) 0 changed F ∧
          (∀ t, t ≠ port → F.L t = S.L t ∧ F.R t = S.R t) ∧
          ∀ a, changed (position k a) = Shared50RecursiveNodeRows.transpose (one_dvd (child k).rows)
            (x (idleTape i k) ∘ position k) a) →
      ∀ x u S, HelperFan fan x S → outside S →
        ∃ z F n y, Exec body (Prog.seqList (idleCopies.map fun k => .call (proc k))) (mk u S) n (mk z F) ∧
          n ≤ (idleCopies.map fun k => budget (index k)+2).sum+1 ∧
          z.user = u.user ∧ HelperFan fan y F ∧
          (∀ k, intervalChildRead i k.2 w W (x (idleTape i k)) (y (idleTape i k))) ∧
          ∀ t, (∀ k, t ≠ idleTape i k) → y t = x t) := by
  intro W V index child outside
  choose position coords call using fun k => flatIdleCall_exec body (proc k) node i (idleCopyIndex k) w rows hw width split
  refine ⟨position,fun k => ?_,?_⟩
  · simpa only [idleCopyIndex_get] using coords k
  intro recurse x u S rep fresh
  obtain ⟨y,D,z,n,exec,cost,user,ready,acts,off⟩ := idleCopies_exec i body (fun k => .call (proc k))
    (fun k => ((budget (index k)+2 : ℕ) : ℝ)) (fun _ _ _ => True)
    (fun _ data A => HelperFan fan data A ∧ outside A) (fun k => intervalChildRead i k.2 w W)
    (by
      intro k past rest data A ctrl _ live _
      let owner := idleTape i k
      let port := fan (owner.castAdd 2)
      let stored := fun (word : Fin V → ZMod 2) (F : Stacks T prime) => RecordPayload port (fun _ => blank) 0 word F ∧
        ∀ t, t ≠ port → F.L t = A.L t ∧ F.R t = A.R t
      obtain ⟨v,F,m,word,run,paid,user,⟨payload,keep⟩,act⟩ :=
        call k stored ctrl A (data owner) (budget (index k)) (by
          intro smaller
          obtain ⟨v,F,m,word,run,paid,user,payload,keep,read⟩ := recurse k data ctrl A smaller live.1 live.2
          exact ⟨v,F,m,word,run,paid,user,⟨payload,keep⟩,read⟩)
      refine ⟨Function.update data owner word,F,v,m,run,by exact_mod_cast paid,user,
        ⟨fanUpdate owner word live.1 payload (fun t ne => keep _ (fan.injective.ne ne)),?_⟩,
        fun _ _ _ => trivial,?_,fun t ne => Function.update_of_ne ne ..⟩
      · intro t away
        have kept := keep t (away _).symm
        exact ⟨kept.1.trans (live.2 t away).1,kept.2.trans (live.2 t away).2⟩
      · simpa only [owner,Function.update_self,idleCopyIndex_get] using act)
    x S u ⟨rep,fresh⟩ (fun _ => trivial)
  refine ⟨z,D,n,y,exec,?_,user,ready.1,acts,off⟩
  apply (Nat.cast_le (α := ℝ)).mp
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_list_sum,List.map_map,Function.comp_apply,Function.comp_def,Nat.cast_ofNat] using cost

end IntegerMultBounds.MathlibTM2.M6.BitNode
