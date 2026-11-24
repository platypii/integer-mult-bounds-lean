module

public import IntegerMultBounds.MathlibTM2.M6.BitBandMoveOnBank

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Install the stopping-band child and the stopped leaf in the same procedure
table. The parent record carries the spectator word followed by the cutoff. -/
theorem dispatchedBandMove {U : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ N : ℕ, ∀ {H : ℕ} (ports : Fin (N+35) ↪ Fin H) (rank : ℕ), 0 < rank → rank ≤ 7 →
      ∃ (P : Type) (table : P → Pr P H Q prime U) (code : Pr P H Q prime U) (rate : ℕ),
      ∀ (p : CutoffNodeInput) (blocks : ℕ) (i : Fin nodeChildren5.length),
        let child := scheduledChild prime p.node i
        let V := (prime^(p.w+1))^16*p.stageWidth
        let n := CopyChildLayout.spectators child
        let archive := binSyms n.size n ++ separator :: binSyms p.root.width.size p.cutoff
        p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
        p.root.beforeH = blocks*prime^(64*p.root.width) → nodeChildren5[i.val] = rank →
        49*(p.w+1) ≤ 64*p.cutoff →
        ∀ position : Fin (volume prime child) ≃ Fin V,
          (∀ j, (position j).val = (CopyChildLayout.packActive child j).val) →
          let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
          ∀ R : ℝ, 391*(163+core) ≤ R →
          let price := if p.cutoff < child.width then
            cutoffTreeBudget D leafRate p.cutoff (p.depth-(p.path.length+1)) child
            else ⌊(R*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
          let bank := scheduledRecordPorts ports
          let stored := RecordReady (b := prime) (w := p.w) (W := p.stageWidth) (d := 16) bank
            (prime^(p.w+1)).size p.stageWidth.size archive SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
          let clean := fun S : Stacks H prime => ∀ j : Fin (N+35), 35 ≤ j.val → S.L (ports j) = [] ∧ S.R (ports j) = []
          child.width < p.node.width → ∀ u S word, stored word S → clean S →
            ∃ z F t y, Exec table code (mk u S) t (mk z F) ∧
              CleanupBound S F t (price+rate*p.cells) ∧
              z.user = u.user ∧ stored y F ∧ clean F ∧
              (∀ j, (∀ k, ports k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
              ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h := by
  intro inst
  obtain ⟨q,compile⟩ := scheduledBandMoveOnBank (U := U)
  refine ⟨max q columnCapacity,?_⟩
  intro Q enough
  obtain ⟨minimum,R,build⟩ := compile ((le_max_left ..).trans enough)
  refine ⟨minimum,R,?_⟩
  intro D large
  obtain ⟨N,space,worker⟩ := build D large
  refine ⟨N+1,?_⟩
  intro H ports rank pos fits
  let slice : Fin (N+35) ↪ Fin H := (Fin.castLEEmb (by omega : N+35 ≤ N+1+35)).trans ports
  let last : Fin (N+1+35) := ⟨N+35,by omega⟩
  let spectator := ports last
  have apart (i : Fin (N+35)) : slice i ≠ spectator := ports.injective.ne (fun eq =>
    i.isLt.ne (congrArg Fin.val eq))
  obtain ⟨P,childTable,move,rate,active⟩ := worker slice rank fits
  let Label := P ⊕ Bool
  have room : 44+LeafCore.small ≤ N+35 := by have := moveLeafFitsWithSpare; omega
  obtain ⟨leaf,mixed⟩ := twoFieldMoveProgram (P := Label) (U := U) slice spectator apart room
    ((le_max_right ..).trans enough) rank pos true (fun _ => by omega)
  let embed := fun (c : Pr P H Q prime U) => embProg (Function.Embedding.refl (Fin H)) (Sum.inl : P → Label) c
  let table : Label → Pr Label H Q prime U := Sum.elim (fun f => embed (childTable f)) (fun b => if b then embed move else leaf)
  refine ⟨Label,table,twoFieldDispatch slice spectator rank (table (.inr true)) (table (.inr false)),rate+2000,?_⟩
  intro p blocks i child V n archive positive rows label kind band position packed core leafRate expensive price
  have shape : child.width = (p.w+1)*rank := by
    change nodeChildren5[i.val]*(p.node.width/64) = _
    rw [kind,p.width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
  have rootBound (path : List (Fin nodeChildren5.length)) := directoryDigits_bound prime p.root path
  have parentBound := rootBound p.path
  have next := rootBound (p.path++[i])
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil] at next
  have cb : p.cutoff < 2^p.root.width.size := by
    have h := p.active
    exact (h.trans (by omega)).trans_lt (Nat.lt_size_self p.root.width)
  have digits : child.width.size ≤ p.root.width.size := Nat.size_le_size (by dsimp only [child,CutoffNodeInput.node]; omega)
  have cells : 0 < p.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos p.idlePositive (by decide : 0 < 142080))
  have W := Nat.pos_of_mul_pos_left (p.stageCells ▸ cells)
  intro bank stored clean smaller u S word ready free
  have sliceClean (j : Fin (N+35)) (hi : 35 ≤ j.val) := free (Fin.castLE (by omega : N+35 ≤ N+1+35) j) hi
  obtain ⟨z,F,t,y,run,paid,user,out,clear,empty,left,frame,read⟩ :=
    mixed table (.inr true) (.inr false) rfl p.node child p.w p.stageWidth p.root.width.size p.cutoff
      (cutoffTreeBudget D R p.cutoff (p.depth-(p.path.length+1)) child+rate*p.cells) shape cb digits
      position packed W leafRate expensive smaller (fun h q A x stored clear _ => by
        obtain ⟨v,B,k,y,exec,cost,same,out,blank,_,keep,action⟩ :=
          active p blocks i positive rows label kind h band position packed smaller q A x stored clear
        obtain ⟨b,G,lift,_,user,view,_⟩ := exec_emb (Function.Embedding.refl (Fin H)).injective (body' := table)
          (ι := Sum.inl) (fun _ => rfl) exec q (by cases q; simp [embDn,Function.comp_def]) A rfl
        change G = B at view
        subst B
        exact ⟨b,G,k,y,lift,cost,user.trans same,out,blank,keep,action⟩)
      word u S ready sliceClean (free last (by change 35 ≤ N+35; omega)).2
  refine ⟨z,F,t,y,run,?_,user,out,?_,?_,read⟩
  · have setup := p.remainderSetup_le 1
    have ticks : p.w+1 ≤ p.cells := by
      rw [← p.stageCells]
      exact (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans
        ((Nat.le_self_pow (by decide : 16 ≠ 0) _).trans (Nat.le_mul_of_pos_right _ W))
    have precision : p.root.width.size ≤ 32*p.cells := by omega
    have spec : n ≤ p.cells := by
      rw [← scheduledChildVolume p i]
      have mass : volume prime child = (prime^child.width*prime^child.width)*n := by
        dsimp only [volume,n,CopyChildLayout.spectators]; ring
      change n ≤ volume prime child
      rw [mass]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) (pow_pos Shared50ModularControl.prime_prime.pos _))
    have size : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    have span := Nat.mul_le_mul_left (p.w+1) fits
    rw [← shape] at span
    intro js nd
    apply (paid js nd).trans (Nat.add_le_add_left ?_ _)
    dsimp only [price]
    rw [Nat.add_mul]
    change _ + 4*p.w + 23*child.width + 22*p.root.width.size + 8*n.size + 61 ≤ _
    by_cases live : p.cutoff < child.width <;> simp only [live,ite_true,ite_false] <;> omega
  · intro j hi
    by_cases h : j.val < N+35
    · exact clear ⟨j.val,h⟩ hi
    · have e : j = last := Fin.ext (by have := j.isLt; change j.val = N+35; omega)
      subst j; exact ⟨left.trans (free last hi).1,empty⟩
  · intro j off
    exact frame j (off last).symm (fun i => off (Fin.castLE (by omega : N+35 ≤ N+1+35) i))

end IntegerMultBounds.MathlibTM2.M6.BitNode
