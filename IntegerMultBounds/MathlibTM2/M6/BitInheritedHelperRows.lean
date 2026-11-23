module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatNodeHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitHelperChildCall

/-! Return an inherited recursive node's role words to the cyclic merge. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Run the recursive node on an inherited lane and recover the merge input
on its returned bank, for arbitrary row-length and group-count headers. -/
theorem inheritedHelperRows_exec {P U : Type} {T N Q price : ℕ} (lane : Descriptor)
    {body : P → Pr P N Q prime U} {code src dst seed}
    (child : PackedPieceHandoff (volume prime lane) (fun x y => ∀ r : Fin 142080,
      y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
      body code src dst seed price)
    (place : Fin (((1+142080)+2)+2) ↪ Fin T) (live : Fin (142080+2) ↪ Fin T)
    (clockPort : live ((0 : Fin 2).natAdd 142080) = place ((0 : Fin 2).natAdd ((1+142080)+2)))
    (volumeFresh : ∀ i, place i ≠ live ((1 : Fin 2).natAdd 142080)) :
    let H := 142082+T+N
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let V := volume prime lane
    ∃ (mergePlace : Fin (((1+142080)+2)+2) ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
      (program : Pr (Empty ⊕ P) H Q prime U), mergePlace 0 = caller (place 0) ∧
    ∀ (owner : ℤ → Fin (prime+4)) (input : Fin 142080 → Fin V → ZMod 2) bs gs u S,
      let roles := fun data j => putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encoded (a := prime) data j))
      let rows := fun data => CyclicRowSplit.bank (CyclicRowCopy.bank owner (roles data) 0 (fun _ => 0) bs) gs
      RepT (rows input) (embStk (place.trans caller) S).L (embStk (place.trans caller) S).R →
      HelperFan (live.trans caller) input S →
      (∀ i : Fin 142082, let j := (i.castAdd T).castAdd N
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := i.natAdd (142082+T)
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧ n ≤ 142081*(8*V+10)+1+price ∧
        z.user = u.user ∧ RepT (rows (fun r => Shared50RecursiveNodeRows.transpose
          (one_dvd lane.rows) (input r))) (embStk mergePlace F).L (embStk mergePlace F).R ∧
        ∀ j, (∀ i : Fin 2, live (i.natAdd 142080) ≠ j) →
          F.L (caller j) = S.L (caller j) ∧ F.R (caller j) = S.R (caller j) := by
  intro H caller V
  obtain ⟨bank,host,program,apart,run⟩ := runInheritedChild lane child live
  obtain ⟨mergePlace,target,merge⟩ := inheritedChildMerge place caller bank live (childReturnFan dst)
    clockPort volumeFresh apart
  refine ⟨mergePlace,host,program,target,?_⟩
  intro owner input bs gs u S roles rows ready fan empty prepared
  obtain ⟨z,F,n,_,ran,paid,user,_,returned,frame⟩ := run input u S fan empty prepared
  exact ⟨z,F,n,ran,paid,user,merge owner input _ bs gs S F ready returned frame,frame⟩

open RecursiveInterchangeRows Shared50RecursiveNodeRows FlatCoordinateSchedule in
/-- Split an inherited word, execute the child on its rows and merge the
transposes. The volume header is computed from the splitter's two descriptors. -/
theorem inheritedHelperTranspose_exec {P U : Type} {T N Q price : ℕ} (physical : Descriptor)
    (positive : physical.Positive) (stock : 142080 ∣ physical.rows)
    {body : P → Pr P N Q prime U} {code src dst seed}
    (child : let lane := role physical 142080
      PackedPieceHandoff (volume prime lane) (fun x y => ∀ r : Fin 142080,
        y r.castSucc = transpose (one_dvd lane.rows) (x r.castSucc)) body code src dst seed price)
    (place : Fin (((1+142080)+2)+2) ↪ Fin T) (live : Fin (142080+2) ↪ Fin T)
    (atRole : ∀ j : Fin 142080, live (j.castAdd 2) = place (((j.natAdd 1).castAdd 2).castAdd 2))
    (atClock : live ((0 : Fin 2).natAdd 142080) = place ((0 : Fin 2).natAdd ((1+142080)+2)))
    (product : Fin 6 ↪ Fin T)
    (atRow : product 3 = place (((1 : Fin 2).natAdd (1+142080)).castAdd 2))
    (atGroups : product 5 = place ((1 : Fin 2).natAdd ((1+142080)+2)))
    (atVolume : live ((1 : Fin 2).natAdd 142080) = product 1)
    (apart : ∀ k : Fin 6, k ≠ 3 → k ≠ 5 → ∀ i, place i ≠ product k)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let H := 142082+T+N
    let lane := role physical 142080
    let V := volume prime lane
    let W := volume prime physical
    let bs := bits (rowLength prime physical)
    let gs := bits (groups 142080 physical)
    let rows := fun owner tapes => CyclicRowSplit.bank (CyclicRowCopy.bank owner tapes 0 (fun _ => 0) bs) gs
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
      (program : Pr (Empty ⊕ P) H Q prime U),
    ∀ (word : Fin W → ZMod 2) u S,
      let owner := putWord (fun _ => blank) 0 (List.ofFn fun k => SparseRoleCircuit.encode (a := prime) (word k))
      RepT (rows owner (fun _ _ => blank)) (embStk (place.trans caller) S).L (embStk (place.trans caller) S).R →
      (∀ k : Fin 6, k ≠ 3 → k ≠ 5 → S.L (caller (product k)) = [] ∧ S.R (caller (product k)) = []) →
      (∀ i : Fin 142082, let j := (i.castAdd T).castAdd N
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := i.natAdd (142082+T)
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧ z.user = u.user ∧
        n ≤ 298*W*(142085+5)+((53*V+28)*11+6+(142081*(8*V+10)+1+price))+12 ∧
        WordAtZero (transpose (one_dvd physical.rows) word)
          (F.L (caller (place 0))) (F.R (caller (place 0))) := by
  intro caller H lane V W bs gs rows
  have fresh i : place i ≠ live ((1 : Fin 2).natAdd 142080) := atVolume ▸ apart 1 (by decide) (by decide) i
  obtain ⟨mergePlace,host,worker,target,run⟩ := inheritedHelperRows_exec lane child place live atClock fresh
  let bank := place.trans caller
  let split : Pr (Empty ⊕ P) H Q prime U := embProg bank Empty.elim (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
  let merge : Pr (Empty ⊕ P) H Q prime U := embProg mergePlace Empty.elim (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity))
  have room : 40 ≤ Q := by
    apply Nat.le_trans _ capacity
    decide
  let setup : Pr (Empty ⊕ P) H Q prime U := embProg (product.trans caller) Empty.elim
    (foreign (liftQ (DimensionProductDescriptor.program (q := prime)) room))
  refine ⟨host,split.seq ((setup.seq worker).seq merge),?_⟩
  intro word u S owner ready scratch empty prepared
  apply Exists.elim (helperRows_exec physical positive (by decide : 0 < 142080) stock word
    (fun _ => blank) (fun _ _ => blank) 0 (fun _ => 0) host (setup.seq worker) _ bank mergePlace (fun _ => False)
    (fun _ h => h.elim) (fun _ h => h.elim) capacity u S ready ?_)
  · rintro z ⟨F,n,ran,paid,user,result,_⟩
    refine ⟨z,F,n,ran,user,paid,?_⟩
    intro a
    have h := result (((0 : Fin 1).castAdd 142080).castAdd 2 |>.castAdd 2) a
    simp only [CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,CountedLoopReuseAlphabet.bank,
      Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,sub_zero] at h
    rw [show (((0 : Fin 1).castAdd 142080).castAdd 2 |>.castAdd 2) = 0 from Fin.ext rfl,target,
      FlatControlledShiftArray.overwrite _ _ _ _ (by simp)] at h
    exact h.symm
  · intro v D splitReady keep
    obtain ⟨x,E,k,built,buildCost,xv,fan,retained,productFrame⟩ :=
      helperFanVolume_exec host bank (live.trans caller) (product.trans caller) physical positive room
        (fun j => congrArg caller (atRole j)) (congrArg caller atRow) (congrArg caller atGroups)
        (congrArg caller atClock) (congrArg caller atVolume)
        (fun i => caller.injective.ne (apart 1 (by decide) (by decide) i)) owner _ v D splitReady (by
          intro j hr hg
          obtain ⟨left,right⟩ := keep _ (fun i => caller.injective.ne (apart j hr hg i))
          exact ⟨left.trans (scratch j hr hg).1,right.trans (scratch j hr hg).2⟩)
    have unchanged j (off : ∀ t, caller t ≠ j) : E.L j = S.L j ∧ E.R j = S.R j := by
      obtain ⟨l,r⟩ := keep j (fun i => off (place i))
      obtain ⟨l',r'⟩ := productFrame j (fun i => off (product i))
      exact ⟨l'.trans l,r'.trans r⟩
    apply Exists.elim (run owner _ bs gs x E retained fan ?_ ?_)
    · rintro z ⟨F,n,ran,paid,user,result,_⟩
      exact ⟨z,F,_,built.seq ran,Nat.add_le_add buildCost paid,user.trans xv,result,fun _ h => h.elim⟩
    · intro i
      have h := unchanged ((i.castAdd T).castAdd N) (by
        intro j eq
        have v := congrArg Fin.val eq
        change 142082+j.val = i.val at v
        omega)
      exact ⟨h.1.trans (empty i).1,h.2.trans (empty i).2⟩
    · intro i
      have h := unchanged (i.natAdd (142082+T)) (by
        intro j eq
        have v := congrArg Fin.val eq
        change 142082+j.val = 142082+T+i.val at v
        omega)
      exact ⟨h.1.trans (prepared i).1,h.2.trans (prepared i).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
