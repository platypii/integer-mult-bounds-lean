module

public import IntegerMultBounds.MathlibTM2.M6.BitStoppedRoleHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitChartCutoff

/-! Tape-level cutoff dispatch for a pair of programs with common owner ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)

/-- A single comparison program serves every cutoff and header length.
Both branches receive the original owner words and private stacks. -/
theorem packedCutoff_exec {T Q V : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (large leaf : Pr P T Q prime U) (src largeDst leafDst : Fin (142081+2) ↪ Fin T) (rank : ℕ) :
    let base := Fin.castAddEmb 10 (n := T)
    let cmp := Fin.natAddEmb T (m := 10)
    let host := fun f => embProg base id (body f)
    let code := (ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7)))
      (embProg base id large) (embProg base id leaf))
    ∀ w L cutoff, cutoff < 2^L → ((w+1)*rank).size ≤ L → ∀ effect price (seed : Stacks T prime),
    (cutoff < (w+1)*rank → PackedPieceHandoff V effect body large src largeDst seed price) →
    ((w+1)*rank ≤ cutoff → PackedPieceHandoff V effect body leaf src leafDst seed price) →
    let dst := if cutoff < (w+1)*rank then largeDst else leafDst
    ∃ prepared, PackedPieceHandoff V effect host code (src.trans base) (dst.trans base) prepared
      ((4*w+23*((w+1)*rank)+22*L+51)+price) := by
  intro base cmp host code w L cutoff cutFits fits effect price seed active stopped dst
  let headers (j : Fin 10) : List (Fin (prime+4)) :=
    if j = 0 then List.replicate w (bitSymbol false) else if j = 1 then binSyms L cutoff else []
  let controls : Stacks 10 prime := ⟨[],[],fun _ => [],headers⟩
  let prepared := adjacentStageStacks seed controls
  refine ⟨prepared,?_⟩
  intro x u S words stock
  have right j : S.R (cmp j) = headers j := by
    have keep := stock (cmp j) (by
      intro t eq
      have h := congrArg Fin.val eq
      change (src t).val = T+j.val at h
      have := (src t).isLt
      omega)
    simpa [cmp,prepared,adjacentStageStacks,controls] using keep.2
  let post (F : Stacks (T+10) prime) := ∃ y, ParentStageWords (fun i => base (dst (i.castAdd 2)))
    (dst.trans base) V y F ∧ effect x y
  obtain ⟨z,F,n,user,paid,ran,y,out,result⟩ := chartCutoff_exec host cmp rank w L cutoff cutFits fits
    (embProg base id large) (embProg base id leaf) u S (by simp [right,headers])
    (by simp [right,headers]) (by intro j hj; rw [right]; simp [headers,show j ≠ 0 by intro e; subst j; contradiction,
      show j ≠ 1 by intro e; subst j; contradiction]) post price (by
    intro v
    have selected : PackedPieceHandoff V effect body (if cutoff < (w+1)*rank then large else leaf) src dst seed price := by
      dsimp only [dst]
      split_ifs with h
      · exact active h
      · exact stopped (Nat.le_of_not_gt h)
    obtain ⟨b,D,k,y,exec,cost,same,returned,act⟩ := selected x (embDn base v) (embStk base S)
      ⟨words.left,words.right,words.controls⟩ (by
        intro j away
        have keep := stock (base j) (fun i e => away i (base.injective e))
        simpa [base,prepared,adjacentStageStacks,embStk] using keep)
    obtain ⟨b',G,placed,_,user,view,_⟩ := exec_emb (body' := host) (ι := id) base.injective
      (fun _ => rfl) exec v rfl S rfl
    rw [← view] at returned
    refine ⟨b',G,k,user.trans same,by exact_mod_cast cost,?_,y,⟨returned.left,returned.right,returned.controls⟩,act⟩
    split_ifs at placed ⊢ <;> exact placed)
  exact ⟨z,F,n,y,ran,by exact_mod_cast paid,user,out,result⟩

private theorem placeHandoff {m T Q V price : ℕ} {P R U : Type}
    (bank : Fin m ↪ Fin T) (label : P → R) (body : P → Pr P m Q prime U) (host : R → Pr R T Q prime U)
    (calls : ∀ f, host (label f) = embProg bank label (body f))
    (src dst : Fin (142081+2) ↪ Fin m) (input : Fin (142081+2) ↪ Fin T)
    (shared : ∀ i, bank (src i) = input i)
    (seed : Stacks m prime) (prepared : Stacks T prime)
    (stock : ∀ j, (∀ i, src i ≠ j) → prepared.L (bank j) = seed.L j ∧ prepared.R (bank j) = seed.R j)
    {effect code} (run : PackedPieceHandoff V effect body code src dst seed price) :
    PackedPieceHandoff V effect host (embProg bank label code) input (dst.trans bank) prepared price := by
  intro x u S words fresh
  obtain ⟨z,F,n,y,exec,paid,user,out,act⟩ := run x (embDn bank u) (embStk bank S)
    (words.next bank src (fun i => shared (i.castAdd 2)) (fun j => shared (j.natAdd 142081))) (by
      intro j away
      have keep := fresh (bank j) (fun i eq => away i (bank.injective ((shared i).trans eq)))
      exact ⟨keep.1.trans (stock j away).1,keep.2.trans (stock j away).2⟩)
  obtain ⟨v,G,ran,_,same,view,_⟩ := exec_emb bank.injective calls exec u rfl S rfl
  rw [← view] at out
  exact ⟨v,G,n,y,ran,paid,same.trans user,⟨out.left,out.right,out.controls⟩,act⟩

/-- Place independently compiled branches around the same owner input.
The comparator and program do not depend on the width or cutoff. -/
theorem placedRoleCutoff {m n Q V : ℕ} {P R U : Type}
    (left : P → Pr P m Q prime U) (right : R → Pr R n Q prime U)
    (large : Pr P m Q prime U) (leaf : Pr R n Q prime U)
    (src dst : Fin (142081+2) ↪ Fin m) (input output : Fin (142081+2) ↪ Fin n) (rank : ℕ) :
    ∃ (host : P ⊕ R → Pr (P ⊕ R) ((m+n)+10) Q prime U), ∃ program common largeOut leafOut,
    ∀ w L cutoff, cutoff < 2^L → ((w+1)*rank).size ≤ L → ∀ effect price A B,
    (cutoff < (w+1)*rank → PackedPieceHandoff V effect left large src dst A price) →
    ((w+1)*rank ≤ cutoff → PackedPieceHandoff V effect right leaf input output B price) →
    ∃ seed, PackedPieceHandoff V effect host program common
      (if cutoff < (w+1)*rank then largeOut else leafOut) seed ((4*w+23*((w+1)*rank)+22*L+51)+price) := by
  obtain ⟨bank,shared,privateTape⟩ := adjacentStagePlacement src input
  let front := Fin.castAddEmb n (n := m)
  let base := Fin.castAddEmb 10 (n := m+n)
  let host := Sum.elim (fun f => embProg front Sum.inl (left f)) (fun f => embProg bank Sum.inr (right f))
  have dispatch := packedCutoff_exec (V := V) host (embProg front Sum.inl large) (embProg bank Sum.inr leaf)
    (src.trans front) (dst.trans front) (output.trans bank) rank
  let cmp := Fin.natAddEmb (m+n) (m := 10)
  let program := (ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7)))
    (embProg base id (embProg front Sum.inl large)) (embProg base id (embProg bank Sum.inr leaf)))
  refine ⟨fun f => embProg base id (host f),program,(src.trans front).trans base,(dst.trans front).trans base,(output.trans bank).trans base,?_⟩
  intro w L cutoff cutFits fits effect price A B active stopped
  obtain ⟨seed,run⟩ := dispatch w L cutoff cutFits fits effect price (adjacentStageStacks A B)
    (fun h => placeHandoff front Sum.inl left host (fun _ => rfl) src dst _ (fun _ => rfl) A _
      (by intro j _; simp [front,adjacentStageStacks]) (active h))
    (fun h => placeHandoff bank Sum.inr right host (fun _ => rfl) input output _ shared B _
      (by intro j away; simp [privateTape j away,adjacentStageStacks]) (stopped h))
  refine ⟨seed,?_⟩
  split_ifs at run ⊢ <;> exact run

end IntegerMultBounds.MathlibTM2.M6.BitNode
