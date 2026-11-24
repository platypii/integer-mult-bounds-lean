module

public import IntegerMultBounds.MathlibTM2.M6.BitBandHeaderDivision
public import IntegerMultBounds.MathlibTM2.M6.BitArchiveModulus
public import IntegerMultBounds.MathlibTM2.DFT.HenselHost

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)

/-- Use the width word as the clock for copying the child's cutoff precision. -/
theorem bandCutoffWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 5 ↪ Fin T) (width cutoff L : ℕ) (fits : width.size ≤ L) u (S : Stacks T prime)
    (digits : S.R (r 1) = binSyms width.size width) (cut : S.R (r 0) = binSyms L cutoff)
    (free : ∀ i : Fin 5, 2 ≤ i.val → S.R (r i) = []) :
    let F := {S with R := Function.update S.R (r 2) (binSyms width.size cutoff)}
    ∃ z, Exec body (DFT.bcopyLow (r 0) (r 1) (r 2) (r 3) (r 4)) (mk u S) (6*width.size+6) (mk z F) ∧
      z.user = u.user ∧ CleanupBound S F (6*width.size+6) (8*width.size+6) := by
  intro F
  obtain ⟨z,user,run⟩ := DFT.bcopyLow_exec (body := body) (s := r 0) (wR := r 1) (d := r 2)
    (t₁ := r 3) (t₂ := r 4) (by simp [r.injective.eq_iff]) (m := width.size) (e := L-width.size)
    u S (by rw [show width.size+(L-width.size) = L by omega]; exact cut) (digits ▸ length_binSyms ..)
    (free 3 (by decide)) (free 4 (by decide))
  rw [free 2 (by decide),List.append_nil] at run
  refine ⟨z,run,user,?_⟩
  intro js nd
  have growth := prependedWordCharge S (r 2) (binSyms width.size cutoff) js nd
  simp only [free 2 (by decide),List.append_nil,length_binSyms] at growth
  change tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+2*width.size at growth
  change 6*width.size+6+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  omega

def bandPowerPorts : Fin 10 ↪ Fin 17 := ⟨![1,7,8,9,10,11,12,13,14,15],by decide⟩

def bandAuxPorts : Fin 6 → Fin 17 := ![16,7,0,9,2,1]

/-- Generate the six auxiliary inputs for the header directory from the
canonical width and the cutoff padded to that width. -/
theorem bandAuxWords_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U) (bank : Fin 17 ↪ Fin T) :
    ∃ code, ∀ (a : ActiveBandRecord) u (S : Stacks T prime),
      let width := a.input.node.width
      let atom := width/64
      S.R (bank 0) = binSyms width.size width → S.R (bank 16) = binSyms width.size a.input.cutoff →
      (∀ i : Fin 17, i ≠ 0 → i ≠ 16 → S.R (bank i) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t ((18*atom+11*atom.size+17)+(47*prime^atom+15)) ∧
        (∀ i, F.R (bank (bandAuxPorts i)) = (![binSyms width.size a.input.cutoff,binSyms 1 1,binSyms width.size width,
          binSyms (prime^atom).size (prime^atom),List.replicate (atom-1) blank,List.replicate atom blank] : Fin 6 → _) i) ∧
        ∀ j, (∀ i : Fin 17, i.val ∈ [1,2,7,9] → bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let clock := (Fin.castAddEmb 10 (n := 7)).trans bank
  let power := bandPowerPorts.trans bank
  obtain ⟨code,run⟩ := widthArchiveWords body clock power rfl
    (fun j => bank.injective.ne ((by decide : ∀ j, (2 : Fin 17) ≠ bandPowerPorts j) j))
  refine ⟨code,?_⟩
  intro a u S width atom digits cut free
  have shape : width = 64*(a.input.w+1) := a.input.width
  have atoms : atom = a.input.w+1 := by dsimp [atom]; rw [shape,Nat.mul_div_cancel_left _ (by decide)]
  obtain ⟨z,F,t,exec,user,paid,long,short,unit,radix,frame⟩ := run a.input.w u S (shape ▸ digits)
    (fun j ne => free _ ((Fin.castAddEmb 10).injective.ne ne) ((by decide : ∀ j : Fin 7, j.castAdd 10 ≠ 16) j))
    (fun j ne => free _ ((by decide : ∀ j, bandPowerPorts j ≠ 0) j) ((by decide : ∀ j, bandPowerPorts j ≠ 16) j))
  have keep (j : Fin T) (off : ∀ i : Fin 17, i.val ∈ [1,2,7,9] → bank i ≠ j) :=
    frame j (off 1 (by decide)).symm (off 2 (by decide)).symm (off 7 (by decide)).symm (off 9 (by decide)).symm
  refine ⟨z,F,t,exec,user,atoms ▸ paid,?_,keep⟩
  intro i
  rw [atoms]
  have preserved (j : Fin 17) (hj : j.val ∉ [1,2,7,9]) := (keep (bank j)
    (fun i hi => bank.injective.ne (fun eq => hj (eq ▸ hi)))).2
  fin_cases i
  · exact (preserved 16 (by decide)).trans cut
  · exact unit
  · exact (preserved 0 (by decide)).trans digits
  · exact radix
  · exact short
  · exact long

/-- Borrow cutoff, unit, child width, child radix and the two clocks.
The unit word serves three logical slots. -/
def bandHeaderPorts {T : ℕ} (bank : Fin 15 ↪ Fin T) (aux : Fin 6 → Fin T) : Fin 12 → Fin T :=
  ![aux 0,aux 1,bank 1,bank 12,aux 2,aux 1,bank 11,aux 3,aux 1,aux 4,bank 13,aux 5]

private theorem flattenBandWords {α : Type} (cut : α) (field : Fin 6 → α)
    (radix unit clock idle next : α) :
    (fun i : Fin 12 => Fin.addCases (motive := fun _ => α)
      (Fin.cons cut (fun j => Fin.addCases (motive := fun _ => α) field (![radix,unit,clock] : Fin 3 → α) j))
      (![idle,next] : Fin 2 → α) i) =
    ![cut,field 0,field 1,field 2,field 3,field 4,field 5,radix,unit,clock,idle,next] := by
  funext i
  fin_cases i <;> rfl

private theorem bandSeedWords_eq (width cut n : ℕ) :
    let v := bandRoot width cut n
    let atom := width/64
    let M := prime^atom
    let idle := n/142080^2
    bandSeedWords width cut n = ![binSyms width.size cut,binSyms 1 1,binSyms v.rows.size v.rows,
      binSyms v.beforeH.size v.beforeH,binSyms width.size width,binSyms 1 1,binSyms v.afterD.size v.afterD,
      binSyms M.size M,binSyms 1 1,List.replicate (atom-1) blank,binSyms idle.size idle,List.replicate atom blank] := by
  intro v atom M idle
  have field (i : Fin 6) : (Routines.hdr v i).map (bitSymbol (a := prime)) =
      binSyms (RecursiveDimensionBank.values v i).size (RecursiveDimensionBank.values v i) :=
    canonicalBits_symbols _
  unfold bandSeedWords
  dsimp only
  rw [flattenBandWords]
  change ![_,(Routines.hdr v 0).map bitSymbol,(Routines.hdr v 1).map bitSymbol,(Routines.hdr v 2).map bitSymbol,
    (Routines.hdr v 3).map bitSymbol,(Routines.hdr v 4).map bitSymbol,(Routines.hdr v 5).map bitSymbol,_,_,_,_,_] = _
  rw [field 0,field 1,field 2,field 3,field 4,field 5]
  change ![_,binSyms (Nat.size 1) 1,_,_,_,binSyms (Nat.size 1) 1,_,_,_,_,_,_] = _
  rw [Nat.size_one]
  rfl

private theorem readBandPorts {T : ℕ} {α : Type} (read : Fin T → α) (bank : Fin 15 ↪ Fin T)
    (aux : Fin 6 → Fin T) (i : Fin 12) :
    read (bandHeaderPorts bank aux i) = ![read (aux 0),read (aux 1),read (bank 1),read (bank 12),
      read (aux 2),read (aux 1),read (bank 11),read (aux 3),read (aux 1),read (aux 4),
      read (bank 13),read (aux 5)] i := by
  fin_cases i <;> rfl

theorem bandHeaders_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (cmp : Fin 10 ↪ Fin T) (bank : Fin 15 ↪ Fin T) (rank : ℕ) (fits : rank ≤ 8)
    (aux : Fin 6 → Fin T) (apart : ∀ j i, i.val ∈ [1,2,11,12,13] → bank i ≠ aux j) :
    ∃ code : Pr P T Q prime U, ∀ (a : ActiveBandRecord) (w L : ℕ) u (S : Stacks T prime),
      let width := a.input.node.width
      let n := CopyChildLayout.spectators a.input.node
      let v := bandRoot width a.input.cutoff n
      let M := prime^(w+1)
      let atom := width/64
      width = (w+1)*rank → ((w+1)*rank).size ≤ L → a.input.cutoff < 2^L →
      (S.R (cmp 0)).length = w → S.R (cmp 1) = binSyms L a.input.cutoff →
      (∀ i : Fin 10, 2 ≤ i.val → S.R (cmp i) = []) →
      S.R (bank 0) = binSyms M.size M → S.R (bank 10) = binSyms n.size n →
      (∀ i : Fin 15, i ≠ 0 → i ≠ 10 → S.R (bank i) = []) →
      (∀ i, S.R (aux i) = (![binSyms width.size a.input.cutoff,binSyms 1 1,binSyms width.size width,
        binSyms (prime^atom).size (prime^atom),List.replicate (atom-1) blank,List.replicate atom blank] : Fin 6 → _) i) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (6*(4*w+23*((w+1)*rank*42^5)+22*(30+L)+53)+1+2*v.rows.size+8000468*n) ∧
        (∀ i, F.R (bandHeaderPorts bank aux i) = bandSeedWords width a.input.cutoff n i) ∧
        F.L = S.L ∧ ∀ j, (∀ i : Fin 15, i.val ∈ [1,2,11,12,13] → bank i ≠ j) → F.R j = S.R j := by
  obtain ⟨code,stock⟩ := bandStockWords_exec body cmp bank rank fits
  refine ⟨code,?_⟩
  intro a w L u S width n v M atom shape precision cutFits clock cut empty base count free read
  obtain ⟨z,F,t,run,user,paid,rows,tail,labels,idle,left,keep⟩ :=
    stock a w L u S shape precision cutFits clock cut empty base count free
  refine ⟨z,F,t,run,user,paid,?_,left,keep⟩
  have borrow (j : Fin 6) := (keep _ (apart j)).trans (read j)
  intro i
  rw [readBandPorts F.R bank aux i,bandSeedWords_eq,rows,labels,tail,idle,borrow 0,borrow 1,borrow 2,
    borrow 3,borrow 4,borrow 5]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

/-- Assemble the full directory with separate work banks for width conversion
and stock arithmetic. Copy the parent's cutoff to the child precision before generating the radix. -/
theorem prepareBandHeaders_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (cmp : Fin 10 ↪ Fin T) (bank : Fin 15 ↪ Fin T) (aux : Fin 17 ↪ Fin T)
    (separate : ∀ i j, bank i ≠ aux j) (away : ∀ i j, cmp i ≠ aux j)
    (rank : ℕ) (fits : rank ≤ 8) :
    ∃ code, ∀ (a : ActiveBandRecord) (w L : ℕ) u (S : Stacks T prime),
      let width := a.input.node.width
      let atom := width/64
      let n := CopyChildLayout.spectators a.input.node
      let v := bandRoot width a.input.cutoff n
      let M := prime^(w+1)
      width = (w+1)*rank → ((w+1)*rank).size ≤ L → a.input.cutoff < 2^L →
      (S.R (cmp 0)).length = w → S.R (cmp 1) = binSyms L a.input.cutoff →
      (∀ i : Fin 10, 2 ≤ i.val → S.R (cmp i) = []) →
      S.R (bank 0) = binSyms M.size M → S.R (bank 10) = binSyms n.size n →
      (∀ i : Fin 15, i ≠ 0 → i ≠ 10 → S.R (bank i) = []) →
      S.R (aux 0) = binSyms width.size width →
      (∀ i : Fin 17, i ≠ 0 → S.R (aux i) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t ((8*width.size+6)+(((18*atom+11*atom.size+17)+(47*prime^atom+15))+
          (6*(4*w+23*((w+1)*rank*42^5)+22*(30+L)+53)+1+2*v.rows.size+8000468*n))) ∧
        (∀ i, F.R (bandHeaderPorts bank (aux ∘ bandAuxPorts) i) = bandSeedWords width a.input.cutoff n i) ∧
        ∀ j, (∀ i : Fin 17, i.val ∈ [1,2,7,9,16] → aux i ≠ j) →
          (∀ i : Fin 15, i.val ∈ [1,2,11,12,13] → bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨first,make⟩ := bandAuxWords_exec body aux
  obtain ⟨last,stock⟩ := bandHeaders_exec body cmp bank rank fits (aux ∘ bandAuxPorts)
    (fun _ i _ => separate i _)
  let slots : Fin 4 ↪ Fin 17 := ⟨![0,16,5,6],by decide⟩
  let field : Fin 5 ↪ Fin T := ⟨Fin.cons (cmp 1) (aux ∘ slots),by
    intro i j eq
    induction i using Fin.cases <;> induction j using Fin.cases
    · rfl
    · exact (away 1 _ eq).elim
    · exact (away 1 _ eq.symm).elim
    · exact congrArg Fin.succ (slots.injective (aux.injective eq))⟩
  refine ⟨(DFT.bcopyLow (field 0) (field 1) (field 2) (field 3) (field 4)).seq (first.seq last),?_⟩
  intro a w L u S width atom n v M shape precision cutFits clock cut empty base count free digits vacant
  have wf : width.size ≤ L := shape ▸ precision
  obtain ⟨q,crop,qu,qp⟩ := bandCutoffWord_exec body field width a.input.cutoff L wf u S digits cut (fun i hi => by
    fin_cases i <;> first | contradiction | (apply vacant; decide))
  let B := {S with R := Function.update S.R (aux 16) (binSyms width.size a.input.cutoff)}
  have cb (j : Fin T) (ne : j ≠ aux 16) : B.R j = S.R j := Function.update_of_ne ne ..
  obtain ⟨y,D,k,run,user,price,words,keep⟩ := make a q B
    ((cb _ (aux.injective.ne (by decide))).trans digits) (Function.update_self ..)
    (fun i h ne => (cb _ (aux.injective.ne ne)).trans (vacant i h))
  have compare i := ((keep (cmp i) (fun j _ => (away i j).symm)).2).trans (cb _ (away i 16))
  have saved i := ((keep (bank i) (fun j _ => (separate i j).symm)).2).trans (cb _ (separate i 16))
  obtain ⟨z,F,t,finish,same,cost,headers,left,frame⟩ := stock a w L y D shape precision cutFits
    (by rwa [compare]) ((compare 1).trans cut) (fun i h => (compare i).trans (empty i h))
    ((saved 0).trans base) ((saved 10).trans count) (fun i h j => (saved i).trans (free i h j)) words
  refine ⟨z,F,_,crop.seq (run.seq finish),same.trans (user.trans qu),qp.seq (price.seq cost),headers,?_⟩
  intro j off clear
  have preserved := keep j (fun i hi => off i ((by decide : ∀ i : Fin 17, i.val ∈ [1,2,7,9] →
    i.val ∈ [1,2,7,9,16]) i hi))
  exact ⟨(congrFun left j).trans preserved.1,(frame j clear).trans (preserved.2.trans (cb _ (off 16 (by decide)).symm))⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
