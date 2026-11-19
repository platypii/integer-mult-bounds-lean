module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPayload

/-! One complete anchor record on the payload and sign queues. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8 AtomSegment AtomBank ActualAffineScaling Mult.ShortConv Mult.PhaseCellToeplitz
variable {T n f b W : ℕ} {P U : Type}
local instance : NeZero (modulus b) := ⟨(modulus_pos b).ne'⟩

abbrev size (n : ℕ) := 22 + anchorSlots n
abbrev arraySlot (n T : ℕ) := Fin.castAdd T (17 : Fin (size n))
abbrev port (n : ℕ) (r : Fin 6 ↪ Fin T) (i : Fin 6) := Fin.natAdd (size n) (r i)

private theorem separate (i : Fin (size n)) (j : Fin T) : Fin.castAdd T i ≠ Fin.natAdd _ j := by
  intro h
  have v := congrArg Fin.val h
  simp at v
  omega

def Ready (n f b W : ℕ) (S : Stacks (size n+T) prime) :=
  ∀ i j, (outer (anchorSlots n) (neutral b W) (fun _ => blank) f).tape i j =
    readAt blank (S.L (Fin.castAdd T i)) (S.R (Fin.castAdd T i))
      (j-(outer (anchorSlots n) (neutral b W) (fun _ => blank) f).head i)

def program (n : ℕ) (r : Fin 6 ↪ Fin T) :=
  Prog.seq (movePrefix (port n r 0) (port n r 1) (arraySlot n T) (port n r 2) (port n r 3))
    (.seq (framedAnchor (P := P) (U := U) n (r 4))
      (transfer (port n r 0) (arraySlot n T) (port n r 5) (port n r 3)))

theorem runs (r : Fin 6 ↪ Fin T) (negative : Bool) (hf : 0 < f) (hb : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array ((n+1)*f) b W) (body : P → Pr P _ _ prime U)
    (u : HS _ _ prime U) (S : Stacks _ prime) (rest signs : List (Fin (prime+4)))
    (ready : Ready n f b W S) (count : (S.R (port n r 0)).length = (modulus b)^((n+1)*f)*W)
    (queue : S.R (port n r 1) = payloadWord a ++ rest)
    (saved : S.R (port n r 2) = []) (tmp : S.R (port n r 3) = [])
    (sign : S.R (port n r 4) = bitSymbol negative :: signs) :
    let K := (modulus b)^((n+1)*f)*W
    ∃ a' : FlatCoordinateStages.Array ((n+1)*f) b W, ∃ z F t,
      Exec body (program n r) (mk u S) t (mk z F) ∧ Ready n f b W F ∧
      z.user = u.user ∧ F.inp = S.inp ∧ F.out = S.out ∧
      F.L (port n r 1) = S.L (port n r 1) ∧
      t ≤ 10*K+10+(chainConst (anchorOps n negative)*f*K+1)*(size n+T+5)+2*T+8 ∧
      (∀ j : Fin T, F.R (Fin.natAdd (size n) j) =
        if j = r 5 then (payloadWord a').reverse ++ S.R (port n r 5)
        else if j = r 4 then signs else if j = r 1 then rest else S.R (Fin.natAdd (size n) j)) ∧
      ∀ (x : Fin (n+1) → Fin f → ZMod (modulus b)) (j : Fin W),
        a' (FlatCoordinateLayout.index (AtomOps.refine
          (Fin.cons (fun k => if negative then -x 0 k else x 0 k) (fun i => x i.succ))) j) =
          a (FlatCoordinateLayout.index (AtomOps.refine x) j) := by
  have mod17 : 17 % size n = 17 := Nat.mod_eq_of_lt (by unfold size; omega)
  have dist (i : Fin 6) := separate (17 : Fin (size n)) (r i)
  obtain ⟨v,B,vu,load,eqB,arr⟩ := loadPayload_exec body (count := port n r 0)
    (dst := arraySlot n T) (by simp [dist,Ne.symm,port,arraySlot,r.injective.eq_iff])
    a rest u S queue count (fun j => by simpa [outer,Fin.val_ofNat,mod17,size] using (ready 17 j).symm)
    saved tmp
  have active (i : Fin (size n)) (j : ℤ) := ready i j
  obtain ⟨a',z,G,t,dispatch,tc,zu,zi,zo,caller,bank,act⟩ := framedAnchor_exec (r 4) negative hf hb hW a
    body v B (by
      intro i j
      by_cases h : i.val = 17
      · have e : i = 17 := Fin.ext (by change i.val = 17 % size n; rwa [mod17])
        subst i
        simpa [outer,Fin.val_ofNat,mod17,size] using arr j
      · simpa [eqB,outer,h,Function.update_of_ne,separate,arraySlot,
          show i ≠ 17 by intro e; subst i; simp [mod17] at h] using active i j)
    signs (by simpa [eqB,port,arraySlot,(separate _ _).symm,r.injective.eq_iff] using sign)
  have cr (i : Fin 6) := (caller (r i)).2
  obtain ⟨y,yu,collect,blanked⟩ := collectPayload_exec body (count := port n r 0) (src := arraySlot n T)
    (dst := port n r 5) (tmp := port n r 3)
    (by simp [port,arraySlot,separate,(separate _ _).symm,r.injective.eq_iff])
    a' z G (by simpa [port,eqB,arraySlot,(separate _ _).symm,r.injective.eq_iff] using (congrArg List.length (cr 0)).trans (by simpa [eqB,port,arraySlot,(separate _ _).symm,r.injective.eq_iff] using count))
    (by simpa [eqB,port,arraySlot,(separate _ _).symm,r.injective.eq_iff,tmp] using cr 3)
    (fun j => by simpa [outer,Fin.val_ofNat,mod17,size] using bank 17 j)
  refine ⟨a',y,_,_,Exec.seq load (Exec.seq dispatch collect),?_,yu.trans (zu.trans vu),?_,?_,?_,by unfold size; omega,?_,act⟩
  · intro i j
    by_cases h : i.val = 17
    · have e : i = 17 := Fin.ext (by change i.val = 17 % size n; rwa [mod17])
      subst i
      simpa [outer,Fin.val_ofNat,mod17,size] using (blanked j).symm
    · simpa [outer,h,port,arraySlot,separate,
        show i ≠ 17 by intro e; subst i; simp [mod17] at h] using bank i j
  · simpa [eqB] using zi
  · simpa [eqB] using zo
  · simpa only [eqB] using (caller (r 1)).1
  · intro j
    have cj := (caller j).2
    by_cases h : j = r 5 <;> simp_all [port,arraySlot,(separate _ _).symm,r.injective.eq_iff,Function.update_apply]

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
