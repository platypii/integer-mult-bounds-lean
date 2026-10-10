import IntegerMultBounds.Machine.EqualWordSwap
import IntegerMultBounds.Machine.WordBankCleanup

/-! Physical equal-word exchange on any two fixed caller ports. All heads,
all complementary tapes and the full word exteriors are retained literally. -/
namespace IntegerMultBounds.Machine.WordBankSwap
noncomputable section
open WordBankCleanup (write pairPlace pairSlot)
variable {a t : ℕ}

private theorem replace_pair (v : Tapes t a) (src dst : Fin t) (hne : src≠dst) (ht : 2≤t)
    (f g : ℤ → Fin (a+4)) :
    Placement.replace (pairPlace src dst hne ht) v
      (CopyWord.cfg f g (v.head src) (v.head dst)).tapes=write (write v src f) dst g := by
  let e := pairPlace src dst hne ht
  have he (i : Fin 2) : e (Fin.castAdd (t-2) i)=pairSlot src dst i :=
    InjectivePlacement.active_slot _ _ _ i
  have hextra (i : Fin (t-2)) (j : Fin 2) : e (Fin.natAdd 2 i)≠pairSlot src dst j := by
    rw [←he j]
    intro h
    have hv := congrArg Fin.val (e.injective h)
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  change Placement.replace e v _=write (write v src f) dst g
  apply congrArg₂ Tapes.mk
  · funext j
    obtain ⟨i,rfl⟩ := e.surjective j
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine e _ _).head (e (Fin.castAdd (t-2) i))=_
      rw [Placement.combine_head_active]
      fin_cases i <;> simp [write,he,CopyWord.cfg,Config.tapes,pairSlot]
    | right i =>
      change (Placement.combine e _ _).head (e (Fin.natAdd 2 i))=_
      rw [Placement.combine_head_extra]
      rfl
  · funext j
    obtain ⟨i,rfl⟩ := e.surjective j
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine e _ _).tape (e (Fin.castAdd (t-2) i))=_
      rw [Placement.combine_tape_active]
      fin_cases i
      · change _ = (write (write v src f) dst g).tape (e (Fin.castAdd (t-2) 0))
        rw [he 0]
        simp [write,CopyWord.cfg,Config.tapes,pairSlot,hne]
      · change _ = (write (write v src f) dst g).tape (e (Fin.castAdd (t-2) 1))
        rw [he 1]
        simp [write,CopyWord.cfg,Config.tapes,pairSlot]
    | right i =>
      have hsrc : e (Fin.natAdd 2 i)≠src := by simpa only [pairSlot,Matrix.cons_val_zero] using hextra i 0
      have hdst : e (Fin.natAdd 2 i)≠dst := by simpa [pairSlot] using hextra i 1
      change (Placement.combine e _ _).tape (e (Fin.natAdd 2 i))=_
      rw [Placement.combine_tape_extra]
      simp [Placement.extra,write,hsrc,hdst]

def program (src dst : Fin t) (hne : src≠dst) (ht : 2≤t) (a : ℕ) :=
  Placement.placed (EqualWordSwap.program a) (pairPlace src dst hne ht)

/-- Derive the placed physical exchange directly from original caller words;
no local machine specification is supplied. -/
theorem runs (v : Tapes t a) (src dst : Fin t) (hne : src≠dst) (ht : 2≤t)
    (f g : ℤ → Fin (a+4)) (xs ys : List (Fin (a+4))) (hlen : xs.length=ys.length)
    (hs : v.tape src=putWord f (v.head src) xs)
    (hd : v.tape dst=putWord g (v.head dst) ys)
    (hx : ∀ x∈xs,x≠blank) (hy : ∀ y∈ys,y≠blank)
    (hf : f (v.head src-1)=blank) (hf' : f (v.head src+xs.length)=blank)
    (hg : g (v.head dst-1)=blank) :
    HoareTime (program src dst hne ht a) (fun w => w=v)
      (fun w => w=write (write v src (putWord f (v.head src) ys)) dst
        (putWord g (v.head dst) xs)) (3*xs.length+6) := by
  have h := Placement.hoare_at
    (EqualWordSwap.runs f g (v.head src) (v.head dst) xs ys hlen hx hy hf hf' hg)
    (pairPlace src dst hne ht) v (by rw [WordBankCleanup.pair_active,hs,hd])
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  rw [replace_pair]

end
end IntegerMultBounds.Machine.WordBankSwap
