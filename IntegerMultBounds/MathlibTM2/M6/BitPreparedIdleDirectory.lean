module

public import IntegerMultBounds.MathlibTM2.M6.BitIdleWindowBoard

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

/-- Install the parent header initializer and every active idle entry on the
same machine. The entries address their payloads on the parent's owner fan. -/
theorem preparedIdleDirectory [M8.Machine.Net] {P U : Type} {N Q : ℕ}
    {body : P → Pr P N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ}
    {permits : {c : CutoffNodeInput // c.cutoff < c.node.width} → ℕ → ℕ → Prop}
    (family : RecordTreeFamily Subtype.val body dst leafRate permits)
    (swapCap : (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states ≤ Q)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (headerCap : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (i : Fin 9) :
    let Job := Fin idleCopies.length
    let Label := Job ⊕ (Σ _ : Job, Option (Empty ⊕ P))
    ∃ (H : ℕ) (fan : Fin 142081 ↪ Fin H) (master : Fin 12 ↪ Fin H)
      (raw : Job → Fin 72 ↪ Fin H) (fields : Job → Fin 6 ↪ Fin H) (scratch : List (Fin H))
      (table : Label → Pr Label H Q prime U) (setup : Pr Label H Q prime U)
      (seedRate fixed base swaps : ℕ) (minimum : ℝ), 0 ≤ minimum ∧
      (∀ j, raw j 24 = fan (idleTape i idleCopies[j.val])) ∧
      (∀ j k, k ≠ 24 → ∀ r, raw j k ≠ fan r) ∧
      (∀ j k r, fields j k ≠ fan r) ∧ (∀ t ∈ scratch, ∀ r, t ≠ fan r) ∧
      (∀ p u (S : Stacks H prime), (∀ k, S.R (master k) = nodeSeedWords p k) →
        (∀ t, (∀ k, master k ≠ t) → S.L t = [] ∧ S.R t = []) →
        ∃ z F n, Exec table setup (mk u S) n (mk z F) ∧ z.user = u.user ∧ CleanupBound S F n (seedRate*p.cells) ∧
          (∀ j, IdleDispatchReady (raw j) p.w p.idleWidth p.root.width.size p.cutoff F) ∧
          (∀ j k, F.R (fields j k) = (Routines.hdr (role p.node 142080) k).map bitSymbol) ∧
          (∀ t ∈ scratch, F.L t = [] ∧ F.R t = []) ∧ ∀ k, F.L (master k) = S.L (master k) ∧ F.R (master k) = S.R (master k)) ∧
      ∀ D : ℝ, minimum ≤ D → ∀ j, ScheduledIdleRecordRun table (.call (.inl j))
        (raw j) (fields j) scratch i j D leafRate permits fixed base swaps := by
  intro Job Label
  let owner : Job ↪ Fin 142081 := ⟨fun j => idleTape i idleCopies[j.val],fun {a b} eq =>
    (idleCopyIndex_at a).symm.trans ((congrArg idleCopyIndex ((idleTape_injective i) eq)).trans (idleCopyIndex_at b))⟩
  obtain ⟨L,fan,raw,origin,shared,_,offRaw,build⟩ := prepareIdleCallerBoards (N := 0) (P := Empty) (U := U) owner headerCap
  let bank := Fin.castAddEmb 12 (n := L+(80+273))
  let master := Fin.natAddEmb (L+(80+273)) (m := 12)
  let window := (Fin.castAddEmb (80+273)).trans bank
  obtain ⟨board,init,seedRate,rawAt,_,offRole,prepare⟩ := build (fun e => Empty.elim e) bank master
    (fun r k => (suffixApart k r).symm)
  let size := intervalHostSize (113+intervalSplitTapes) N
  let place := Fin.castAddEmb size (n := (L+(80+273))+12)
  let rawBank j := ((Fin.castAddEmb 6 (n := 72)).trans (board j)).trans place
  let fields j := ((Fin.natAddEmb 72 (m := 6)).trans (board j)).trans place
  obtain ⟨table,scratch,minimum,fixed,base,swaps,nonneg,run⟩ :=
    installedIdleWindow family swapCap capacity i board
  refine ⟨_,(fan.trans window).trans place,master.trans place,rawBank,fields,
    scratch.map (Fin.natAddEmb _),table,embProg place Empty.elim init,seedRate,fixed,base,swaps,minimum,nonneg,
    fun j => congrArg place ((rawAt j 24).trans (congrArg window (shared j))),?_,?_,?_,?_,run⟩
  · intro j k ne r
    apply place.injective.ne
    change board j (k.castAdd 6) ≠ window (fan r)
    rw [rawAt]
    exact window.injective.ne (offRaw j k ne r)
  · exact fun j k r => place.injective.ne (offRole j k r)
  · intro t mem r
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp mem
    exact suffixApart k _
  intro p u S words empty
  obtain ⟨a,E,n,exec,user,paid,ready,roles,_,keep⟩ := prepare p (embDn place u) (embStk place S) words
    (fun r => empty (place (bank r)) (fun k => place.injective.ne (suffixApart k r)))
  obtain ⟨z,F,lifted,_,last,view,off⟩ := exec_emb place.injective (body' := table)
    (ι := Empty.elim) (fun e => Empty.elim e) exec u rfl S rfl
  rw [← view] at paid ready roles keep
  have bound : CleanupBound S F n (seedRate*p.cells) := CleanupBound.place place off paid
  rw [embDn_user] at user
  have same : z.user = u.user := Eq.trans (b := a.user) last user
  refine ⟨z,F,n,lifted,same,bound,?_,?_,?_,?_⟩
  · exact fun j k ne => ready j k ne
  · exact fun j k => roles j k
  · intro t mem
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp mem
    have outside (r : Fin ((L+(80+273))+12)) := (suffixApart k r).symm
    have unchanged := off _ outside
    have blank := empty _ (fun j => outside (master j))
    exact ⟨unchanged.1.trans blank.1,unchanged.2.trans blank.2⟩
  · intro k
    exact keep (master k) (fun r => (suffixApart k r).symm)

end IntegerMultBounds.MathlibTM2.M6.BitNode
