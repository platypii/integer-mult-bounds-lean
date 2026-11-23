module

public import IntegerMultBounds.MathlibTM2.M6.BitParentArchiveSeed
public import IntegerMultBounds.MathlibTM2.M6.BitIdleDispatchClocks

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor)

def activeArchiveSources {T : ℕ} (source : Fin 8 → Fin T) (r : Fin 7 ↪ Fin T) (i : Fin 9) : Fin T :=
  Fin.lastCases (motive := fun _ => Fin T) (r 2) source i

/-- Read the inherited descriptor's width and install the archive. The two
clock outputs stay on the caller's tapes for the idle dispatch. -/
theorem loadActiveArchive {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (80+273) ↪ Fin T) (source : Fin 8 → Fin T) (r : Fin 7 ↪ Fin T) (tmp saved : Fin T)
    (widthPort : r 0 = source 3)
    (sourceOff : ∀ i, source i ≠ r 1 ∧ source i ≠ r 2)
    (bankOff : ∀ i, bank i ≠ r 1 ∧ bank i ≠ r 2)
    (tmpOff : tmp ≠ r 1 ∧ tmp ≠ r 2) (savedOff : saved ≠ r 1 ∧ saved ≠ r 2) :
    let src := activeArchiveSources source r
    (∀ i j, bank (parentArchivePorts i) ≠ src j) →
    (∀ i, [src i,bank (parentArchivePorts i),tmp,saved].Nodup) →
    ∃ code, ∀ (node : Descriptor) w, node.width = 64*(w+1) →
    ∀ u (S : Stacks T prime), let seed := parentArchiveSeed node w
      (∀ i : Fin 8, S.R (source i) = seed.R (parentArchivePorts i.castSucc)) →
      (∀ j, j ≠ 0 → S.R (r j) = []) →
      (∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t ((18*(w+1)+11*(w+1).size+17)+(seedLoadBill (fun i => seed.R (parentArchivePorts i))+31)) ∧
        (∀ j, F.L (bank j) = seed.L j ∧ F.R (bank j) = seed.R j) ∧
        F.R (r 1) = List.replicate (w+1) blank ∧ F.R (r 2) = List.replicate w blank ∧
        ∀ j, j ≠ r 1 → j ≠ r 2 → (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro src apart regs
  obtain ⟨clock,read⟩ := idleDispatchClocks body r
  obtain ⟨load,run⟩ := loadParentArchiveSeed body bank src tmp saved apart regs
  refine ⟨clock.seq load,?_⟩
  intro node w width u S seed words free empty ht hs
  have digit := words 3
  change S.R (source 3) = (Routines.hdr node 3).map bitSymbol at digit
  have h := digit.trans (canonicalBits_symbols node.width)
  rw [width] at h
  obtain ⟨v,n,start,user,paid⟩ := read w u S (widthPort ▸ h) free
  let D := {S with R := Function.update (Function.update S.R (r 1) (List.replicate (w+1) blank)) (r 2) (List.replicate w blank)}
  have keep j (a : j ≠ r 1) (b : j ≠ r 2) : D.R j = S.R j := by simp [D,a,b]
  have inputs (i : Fin 9) : D.R (src i) = seed.R (parentArchivePorts i) := by
    induction i using Fin.lastCases with
    | last => exact Function.update_self ..
    | cast j =>
      simpa only [src,activeArchiveSources,Fin.lastCases_castSucc] using (keep _ (sourceOff j).1 (sourceOff j).2).trans (words j)
  obtain ⟨z,F,t,finish,same,charge,stock,frame⟩ := run node w v D inputs
    (fun j => ⟨(empty j).1,(keep _ (bankOff j).1 (bankOff j).2).trans (empty j).2⟩)
    ((keep _ tmpOff.1 tmpOff.2).trans ht) ((keep _ savedOff.1 savedOff.2).trans hs)
  refine ⟨z,F,n+t,start.seq finish,same.trans user,paid.seq charge,stock,?_,?_,?_⟩
  · rw [(frame _ (fun i => (bankOff i).1)).2]
    simp [D,r.injective.eq_iff]
  · exact (frame _ (fun i => (bankOff i).2)).2.trans (Function.update_self ..)
  · intro j a b off
    exact ⟨(frame j off).1,(frame j off).2.trans (keep j a b)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
