module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffNode
public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationWord
import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordVolumeHeaders

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

private theorem bitPrefix (bs : List Bool) (p : ℤ) (positive : 0 < p)
    (xs : List (Fin (prime+4)))
    (rep : ∀ m : ℕ, (xs[m]?).getD blank =
      CountedLoopAlphabet.putBits CountedLoopReuseAlphabet.empty p bs (p+m)) :
    ∃ rest, xs = bs.map bitSymbol ++ rest ∧ rest.head?.getD blank = blank := by
  induction bs generalizing p xs with
  | nil =>
    refine ⟨xs,rfl,?_⟩
    cases xs <;> simpa [CountedLoopAlphabet.putBits,CountedLoopReuseAlphabet.empty,ne_of_gt positive] using rep 0
  | cons b bs ih =>
    have first : (xs[0]?).getD blank = bitSymbol b := by
      simpa only [Nat.cast_zero,add_zero,CountedLoopAlphabet.putBits_head] using rep 0
    cases xs with
    | nil => cases b <;> contradiction
    | cons x xs =>
      change x = bitSymbol b at first
      obtain ⟨rest,tail,stop⟩ := ih (p+1) (by omega) xs (fun m => by
        have h := rep (m+1)
        simpa only [List.getElem?_cons_succ,Nat.cast_add,Nat.cast_one,CountedLoopAlphabet.putBits,
          Function.update_of_ne (show p+(m+1 : ℤ) ≠ p by omega),add_left_comm,add_comm,add_assoc] using h)
      exact ⟨rest,by simp [first,tail],stop⟩

/-- A logical binary length followed by a blank delimiter or the end of the stack. -/
def LengthControl (word : List (Fin (prime+4))) (V : ℕ) : Prop :=
  ∃ rest, word = binSyms V.size V ++ rest ∧ rest.head?.getD blank = blank

/-- The shared control tape contains the binary length at the head, including
when the physical right stack has trailing blank symbols. -/
theorem helperFan_lengthWord {k T V : ℕ} {fan : Fin (k+2) ↪ Fin T} {x : Fin k → Fin V → ZMod 2}
    {S : Stacks T prime} (live : HelperFan fan x S) :
    LengthControl (S.R (fan ((1 : Fin 2).natAdd k))) V := by
  unfold LengthControl
  rw [← canonicalBits_symbols]
  apply bitPrefix _ 1 (by decide)
  intro m
  have h := live ((1 : Fin 2).natAdd k) (1+(m : ℤ))
  simpa [PointwiseRoleGate.bank,Tapes.append,CountedLoopReuseAlphabet.controls,
    CountedLoopReuseAlphabet.binary,embStk,readAt] using h.symm

/-- Read a canonical length up to its first blank and restore the entire source stack. -/
theorem copyLengthPrefix {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (src dst tmp saved : Fin T) (ports : [src,dst,tmp,saved].Nodup) :
    ∃ code, ∀ (V : ℕ) u (S : Stacks T prime),
      LengthControl (S.R src) V →
      S.R dst = [] → S.R tmp = [] → S.R saved = [] →
      let F := {S with R := Function.update S.R dst (binSyms V.size V)}
      ∃ v, Exec body code (mk u S) (6*V.size+6) (mk v F) ∧ v.user = u.user := by
  regs_ne ports
  refine ⟨(Routing.configurationScan src tmp saved WordCmd.isBit).seq
    ((moveR tmp dst id).seq (moveR saved src id)),?_⟩
  intro V u S lengthWord hd ht hs F
  let word := binSyms (A := prime) V.size V
  obtain ⟨rest,source,stop⟩ := lengthWord
  change S.R src = word ++ rest at source
  have bits : ∀ e ∈ word, WordCmd.isBit e = true := by
    dsimp only [word]
    rw [binSyms_eq]
    exact WordCmd.isBit_bits _
  have endWord : (rest.head?.map WordCmd.isBit).getD false = false := by
    cases h : rest.head? with
    | none => rfl
    | some v =>
      rw [h] at stop
      change v = blank at stop
      subst v
      rfl
  obtain ⟨v,user,scan⟩ := Routing.configurationScan_exec body src tmp saved ‹src ≠ tmp› ‹src ≠ saved›
    ‹tmp ≠ saved› _ word rest bits endWord u S source
  let D := {S with R := Routing.configurationScanned S.R src tmp saved word rest}
  obtain ⟨y,same,copy⟩ := moveR_exec body tmp dst ‹dst ≠ tmp›.symm id v D
  let E := {D with R := movedR D.R tmp dst id (D.R tmp)}
  obtain ⟨z,last,restore⟩ := moveR_exec body saved src ‹src ≠ saved›.symm id y E
  have ht' : D.R tmp = word.reverse := by simp [D,Routing.configurationScanned,ht,‹tmp ≠ saved›]
  have hs' : E.R saved = word.reverse := by simp [E,movedR,D,Routing.configurationScanned,hs,‹tmp ≠ saved›.symm,‹dst ≠ saved›.symm]
  have final : movedR E.R saved src id (E.R saved) = F.R := by
    funext j
    by_cases a : j = src <;> by_cases b : j = dst <;> by_cases c : j = tmp <;> by_cases d : j = saved <;>
      simp_all [D,E,F,Routing.configurationScanned,movedR,Function.update_apply]
    rfl
  rw [final] at restore
  refine ⟨z,?_,last.trans (same.trans user)⟩
  apply (scan.seq (copy.seq restore)).cast _ rfl
  simp [ht',hs',word,length_binSyms]
  omega

/-- The node initializer can derive either spectator width from the logical length
on the fan control even if the right stack contains padding. -/
theorem spectatorFromControl {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (division : Fin 11 ↪ Fin T) (control base : Fin T) (outside : ∀ i, control ≠ division i)
    (baseOff : ∀ i, division i ≠ base) (stage : Bool) :
    ∃ code, ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
      LengthControl (S.R control) c.cells →
      S.R base = binSyms (prime^(c.w+1)).size (prime^(c.w+1)) →
      (∀ i, S.R (division i) = []) →
      let W := c.spectatorWidth stage
      let F := {S with R := Function.update S.R (division 2) (binSyms W.size W)}
      ∃ z t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (2000255*c.cells) := by
  obtain ⟨read,run⟩ := copyLengthPrefix body control (division 0) (division 3) (division 4)
    (by simp [outside,division.injective.eq_iff])
  refine spectatorFromLengthReader body division base baseOff stage (fun V S => LengthControl (S.R control) V) read ?_
  intro V u S lengthWord free
  obtain ⟨v,exec,user⟩ := run V u S lengthWord (free 0) (free 3) (free 4)
  have size : V.size ≤ V := Nat.size_le.mpr Nat.lt_two_pow_self
  exact ⟨v,_,user,by omega,exec⟩

/-- Obtain the stage spectator width from the represented fan, independently
of the amount of physical blank padding on its payload lanes. -/
theorem spectatorFromFan {P U : Type} {k T Q : ℕ} (body : P → Pr P T Q prime U)
    (fan : Fin (k+2) ↪ Fin T) (division : Fin 11 ↪ Fin T) (base : Fin T)
    (controlOff : ∀ i, fan ((1 : Fin 2).natAdd k) ≠ division i)
    (baseOff : ∀ i, division i ≠ base) :
    ∃ code, ∀ (c : CutoffNodeInput) (x : Fin k → Fin c.cells → ZMod 2) u (S : Stacks T prime),
      HelperFan fan x S → S.R base = binSyms (prime^(c.w+1)).size (prime^(c.w+1)) →
      (∀ i, S.R (division i) = []) →
      let F := {S with R := Function.update S.R (division 2) (binSyms c.stageWidth.size c.stageWidth)}
      ∃ z t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (2000255*c.cells) := by
  obtain ⟨code,run⟩ := spectatorFromControl body division _ base controlOff baseOff true
  exact ⟨code,fun c x u S fan => run c u S (helperFan_lengthWord fan)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
