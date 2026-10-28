module

public import IntegerMultBounds.MathlibTM2.Host.GatherPrefix
public import IntegerMultBounds.MathlibTM2.Host.ExpandMask
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Linear selection of fixed-width records, preserving source, selectors and borrowed suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem gatherSymbols_append {α : Type*} (xs ys : List α) (ms ns : List Bool) (hlen : xs.length = ms.length) :
    gatherSymbols (xs++ys) (ms++ns) = gatherSymbols xs ms++gatherSymbols ys ns := by
  induction xs generalizing ms with
  | nil => obtain rfl : ms = [] := List.eq_nil_of_length_eq_zero hlen.symm; rfl
  | cons x xs ih =>
    cases ms with
    | nil => simp at hlen
    | cons m ms =>
      have hl : xs.length = ms.length := by simpa using hlen
      cases m <;> simp [gatherSymbols,ih ms hl]

theorem gatherSymbols_map {α β : Type*} (f : α → β) (xs : List α) (ms : List Bool) :
    gatherSymbols (xs.map f) ms = (gatherSymbols xs ms).map f := by
  induction xs generalizing ms with
  | nil => cases ms <;> rfl
  | cons x xs ih => cases ms with
    | nil => rfl
    | cons m ms => cases m <;> simp [gatherSymbols,ih]

theorem gatherSymbols_filter {α β : Type*} (f : α → β) (b : α → Bool) (xs : List α) :
    gatherSymbols (xs.map f) (xs.map b) = (xs.filter b).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hb : b x <;> simp [gatherSymbols,hb,ih]

theorem gatherSymbols_replicate {α : Type*} (xs : List α) (b : Bool) :
    gatherSymbols xs (List.replicate xs.length b) = if b then xs else [] := by
  induction xs with
  | nil => cases b <;> rfl
  | cons x xs ih => cases b <;> simp [gatherSymbols,List.replicate_succ,ih]

theorem gatherSymbols_flatten {α : Type*} (words : List (List α)) (flags : List Bool) (w : ℕ)
    (hlen : words.length = flags.length) (hwidth : ∀ x ∈ words, x.length = w) :
    gatherSymbols words.flatten (flags.flatMap (List.replicate w)) = (gatherSymbols words flags).flatten := by
  induction words generalizing flags with
  | nil => obtain rfl : flags = [] := List.eq_nil_of_length_eq_zero hlen.symm; rfl
  | cons x words ih =>
    cases flags with
    | nil => simp at hlen
    | cons b flags =>
      have hx := hwidth x (by simp)
      have hl : words.length = flags.length := by simpa using hlen
      have hw : ∀ y ∈ words, y.length = w := fun y hy => hwidth y (by simp [hy])
      simp only [List.flatten_cons,List.flatMap_cons]
      rw [gatherSymbols_append x words.flatten (List.replicate w b) _ (by simpa using hx)]
      have hrep : gatherSymbols x (List.replicate w b) = if b then x else [] := by
        simpa only [hx] using gatherSymbols_replicate x b
      rw [hrep,ih flags hl hw]
      cases b <;> simp [gatherSymbols]

theorem expandedMask_bits (w : ℕ) (f : Fin (A+4) → Bool) (ms : List (Fin (A+4))) :
    expandedMask w f ms = ((ms.map f).flatMap (List.replicate w)).map bitSymbol := by
  simp [expandedMask,List.flatMap_map,List.map_flatMap,Function.comp_def]

def gatherRecords (src mask width symbols ts tm acc out cs : Fin T) (f : Fin (A+4) → Bool) : Pr P T Q A U :=
  .seq (expandMask mask width ts tm acc symbols f)
    (.seq (gather src symbols ts tm acc out cs) (uclear symbols))

theorem gatherRecords_pushBound (src mask width symbols ts tm acc out cs : Fin T) (f : Fin (A+4) → Bool) :
    mnNativePushBound 3 (gatherRecords (P := P) (Q := Q) (U := U) src mask width symbols ts tm acc out cs f) := by
  simp [gatherRecords,expandMask,repeatMaskWord,umulSym,scanR,keepIn,eachSym,popPush,
    gather,gatherStep,moveR,whileR,moveStep,peekR,uclear,drainR,popDo,pushN,
    mnNativePushBound,mnActPush]

theorem gatherRecords_exec {src mask width symbols ts tm acc out cs : Fin T}
    (hreg : [src,mask,width,symbols,ts,tm,acc,out].Nodup)
    (ms : List (Fin (A+4))) (words : List (List (Fin (A+4)))) (w : ℕ) (f : Fin (A+4) → Bool)
    (hlen : words.length = ms.length) (hwidth : ∀ x ∈ words, x.length = w)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = words.flatten++tail) (hmask : S.R mask = ms) (hw : (S.R width).length = w)
    (hfresh : ∀ k ∈ [symbols,ts,tm,acc], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ ms.length*(16*w+10)+16 ∧
      Exec body (gatherRecords src mask width symbols ts tm acc out cs f) (mk v S) m
        (mk v' {S with R := Function.update S.R out ((gatherSymbols words (ms.map f)).flatten++S.R out)}) := by
  have hr := hreg
  regs_ne hr
  let flags := (ms.map f).flatMap (List.replicate w)
  have hflags : flags.map bitSymbol = expandedMask w f ms := (expandedMask_bits w f ms).symm
  have hflagsLen : flags.length = ms.length*w := by
    have hh := expandedMask_length w f ms
    rw [← hflags,List.length_map] at hh
    exact hh
  have hwordLen : words.flatten.length = words.length*w := by
    calc
      words.flatten.length = (words.map List.length).sum := List.length_flatten
      _ = (words.map (fun _ => w)).sum := by
        congr 1
        apply List.map_congr_left
        intro x hx
        exact hwidth x hx
      _ = words.length*w := by simp
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := expandMask_exec (body := body)
    (show [mask,width,ts,tm,acc,symbols].Nodup by simp_all [ne_comm]) w f v S hw
    (by intro k hk; apply hfresh k; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl <;> simp)
  let S₁ : Stacks T A := {S with R := Function.update S.R symbols (expandedMask w f ms)}
  have he₁' : Exec body (expandMask mask width ts tm acc symbols f) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hmask,hfresh symbols (by simp)] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := gatherPrefix_exec (body := body)
    (show GSRegs src symbols ts tm acc out by simp_all [GSRegs,ne_comm]) flags words.flatten tail
    (by rw [hflagsLen,hwordLen,hlen]) v₁ S₁ (by simp [S₁,hflags])
    (by simpa [S₁,‹src ≠ symbols›] using hsrc)
    (by simpa [S₁,‹symbols ≠ ts›.symm] using hfresh ts (by simp))
    (by simpa [S₁,‹symbols ≠ tm›.symm] using hfresh tm (by simp))
    (by simpa [S₁,‹symbols ≠ acc›.symm] using hfresh acc (by simp))
  let output := (gatherSymbols words (ms.map f)).flatten++S.R out
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R out output}
  have hsem : gatherSymbols words.flatten flags = (gatherSymbols words (ms.map f)).flatten :=
    gatherSymbols_flatten words (ms.map f) w (by simpa using hlen) hwidth
  have he₂' : Exec body (gather src symbols ts tm acc out cs) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,output,hsem,S₁,‹symbols ≠ out›.symm] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) symbols v₂ S₂
  have hslen : (S₂.R symbols).length = ms.length*w := by
    simp [S₂,S₁,‹symbols ≠ out›,expandedMask_length]
  refine ⟨v₃,m₁+m₂+(2*(ms.length*w)+2),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by rw [hslen]; omega) ?_⟩
  · rw [hmask] at hm₁
    rw [hflagsLen] at hm₂
    nlinarith only [hm₁,hm₂]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hs : k = symbols
    · subst k; simp [S₂,S₁,‹symbols ≠ out›,hfresh symbols (by simp)]
    simp [S₂,S₁,output,hs,Function.update_apply]

theorem gatherRecords_within {src mask width symbols ts tm acc out cs : Fin T}
    (hreg : [src,mask,width,symbols,ts,tm,acc,out].Nodup)
    (ms : List (Fin (A+4))) (words : List (List (Fin (A+4)))) (w : ℕ) (f : Fin (A+4) → Bool)
    (hlen : words.length = ms.length) (hwidth : ∀ x ∈ words, x.length = w)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = words.flatten++tail) (hmask : S.R mask = ms) (hw : (S.R width).length = w)
    (hfresh : ∀ k ∈ [symbols,ts,tm,acc], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ ms.length*(16*w+10)+16 ∧
      ExecWithin body
        (fun depth z => mnSize z+depth ≤ mnSize (mk v S)+3*(ms.length*(16*w+10)+16)) 0
        (gatherRecords src mask width symbols ts tm acc out cs f) (mk v S) m
        (mk v' {S with R := Function.update S.R out ((gatherSymbols words (ms.map f)).flatten++S.R out)}) := by
  obtain ⟨v',m,hu,hm,he⟩ := gatherRecords_exec (body := body) hreg ms words w f hlen hwidth tail v S hsrc hmask hw hfresh
  exact ⟨v',m,hu,hm,mn_native_exec_within he 3
    (gatherRecords_pushBound src mask width symbols ts tm acc out cs f) 0 _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Host
