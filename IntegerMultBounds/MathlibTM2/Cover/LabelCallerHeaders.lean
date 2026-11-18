module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDecode
public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap

/-! Read the seven physical headers of the caller's label bank on placed host stacks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelCallerHeaders
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Host Node LabelDecode
open RecursiveInterchangeLayout (Descriptor)
open FlatCoordinateSchedule (bits)
variable {T K Q : ℕ} {P U : Type}

/-- The two row tapes precede the twenty-two arithmetic tapes. -/
def port (K : ℕ) (i : Fin 7) : Fin (K+24) := Fin.natAdd K (![0,1,5,12,13,14,8] i : Fin 24)

def caller (roles : Tapes K prime) (v : Descriptor) (w : ℕ) :=
  LabelCall.bank roles v (M8.Stage2Machine.Straight.words (LabelSchedule.base v w))

theorem header (roles : Tapes K prime) (v : Descriptor) (w : ℕ) (i : Fin 7) :
    (caller roles v w).head (port K i) = 1 ∧
    (caller roles v w).tape (port K i) = RadixZeroFill.encodedBinary (bits (field v w i)) := by
  simp only [caller, LabelCall.bank, Tapes.append, port, Fin.addCases_right]
  fin_cases i <;> exact ⟨rfl,rfl⟩

def ports (r : Fin 26 ↪ Fin T) := (List.finRange 7).map (source r)
def load (r : Fin 26 ↪ Fin T) : Pr P T Q prime U := .seq (normList (ports r)) (shiftList (ports r))

def cost (r : Fin 26 ↪ Fin T) (S : Stacks T prime) :=
  ((ports r).map fun k => 6*((S.L k).length+(S.R k).length)+6).sum + 9

/-- Arbitrary stacks representing the header tapes may have explicit blank padding on either end. -/
def Represents (r : Fin 26 ↪ Fin T) (S : Stacks T prime) (roles : Tapes K prime) (v : Descriptor) (w : ℕ) :=
  ∀ i z, (caller roles v w).tape (port K i) z = readAt blank (S.L (source r i)) (S.R (source r i))
    (z - (caller roles v w).head (port K i))

theorem load_exec (body : P → Pr P T Q prime U) (r : Fin 26 ↪ Fin T) (roles : Tapes K prime)
    (v : Descriptor) (w : ℕ) (u : HS T Q prime U) (S : Stacks T prime) (rep : Represents r S roles v w) :
    ∃ z F c, z.user = u.user ∧ c ≤ cost r S ∧
      (∀ i, F.R (source r i) = (bits (field v w i)).map bitSymbol ∧ F.L (source r i) = [separator]) ∧
      (∀ k, k ∉ ports r → F.R k = S.R k ∧ F.L k = S.L k) ∧ Exec body (load r) (mk u S) c (mk z F) := by
  have inj : Function.Injective (source r) := fun i j h => Fin.ext (by
    have e := congrArg Fin.val (r.injective h); change 19+i.val = 19+j.val at e; omega)
  have hd := (List.nodup_finRange 7).map inj
  have mem (i : Fin 7) : source r i ∈ ports r := List.mem_map_of_mem (List.mem_finRange i)
  have sweepAt (i : Fin 7) : sweep (S.L (source r i)) (S.R (source r i)) =
      separator :: (bits (field v w i)).map bitSymbol := by
    apply filter_window _ _ (1 : ℤ)
    · simp [separator,blank,bitSymbol,Fin.ext_iff]
    · intro j
      have h := rep i j
      rwa [(header roles v w i).1,(header roles v w i).2,encodedBinary_eq] at h
  obtain ⟨u₁,c,hu,hc,he⟩ := normList_exec body (ports r) hd u S
  let M : Stacks T prime := {S with
    L := fun k => if k ∈ ports r then [] else S.L k
    R := fun k => if k ∈ ports r then sweep (S.L k) (S.R k) else S.R k}
  obtain ⟨z,hz,he'⟩ := shiftList_exec body (ports r) hd u₁ M
  refine ⟨z,_,c+((ports r).length+1),hz.trans hu,?_,?_,?_,Exec.seq he he'⟩
  · have hlen : (ports r).length = 7 := by simp [ports]
    unfold cost
    omega
  · intro i; simp [M,mem,sweepAt]
  · intro k hk; simp [M,hk]

private theorem port_injective (K : ℕ) : Function.Injective (port K) := by
  have h : Function.Injective (![0,1,5,12,13,14,8] : Fin 7 → Fin 24) := by decide
  exact (Fin.natAdd_injective 24 K).comp h

/-- Wire the seven binary sources to their actual caller ports, retaining any disjoint work layout. -/
def wiring (call : Fin (K+24) ↪ Fin T) (work : Fin 19 ↪ Fin T)
    (hd : ∀ i j, work i ≠ call (port K j)) : Fin 26 ↪ Fin T where
  toFun := fun i => Fin.addCases (m := 19) (n := 7) (motive := fun _ => Fin T) work (fun j => call (port K j)) i
  inj' := by
    intro i j h
    change Fin (19+7) at i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp only
      [Fin.addCases_left,Fin.addCases_right] at h
    · exact congrArg _ (work.injective h)
    · exact (hd _ _ h).elim
    · exact (hd _ _ h.symm).elim
    · exact congrArg _ (port_injective K (call.injective h))

theorem represents_of_caller (call : Fin (K+24) ↪ Fin T) (work : Fin 19 ↪ Fin T) (hd)
    (roles : Tapes K prime) (v : Descriptor) (w : ℕ) (S : Stacks T prime)
    (rep : RepT (caller roles v w) (S.L ∘ call) (S.R ∘ call)) :
    Represents (wiring call work hd) S roles v w := by
  intro i z
  simpa only [source,wiring,Function.Embedding.coeFn_mk,Fin.addCases_right,Function.comp_apply]
    using rep (port K i) z

open RecursiveInterchangeLayout (volume)

/-- A single host program accepts the placed representation of the caller's header tapes. -/
theorem realizes (body : P → Pr P T Q prime U) (r : Fin 26 ↪ Fin T) (m : ℕ) (hm : 0 < m)
    (rs : List (LabelTraversal.Pair T)) (hk : rs.length = m*m) (hd : (LabelTraversal.slots rs).Nodup)
    (apart : ∀ i, r i ∉ LabelTraversal.slots rs) :
    ∃ p : Pr P T Q prime U, ∀ (roles : Tapes K prime) (v : Descriptor) (w B : ℕ), 0 < w → v.Positive →
      v.beforeH = B*prime^(m*(w*m)) → ∀ (bit : ℕ → Bool) (u : HS T Q prime U) (S : Stacks T prime),
      Represents r S roles v w → (∀ i : Fin 26, i.val ≤ 16 → S.R (r i) = []) →
      (∀ k ∈ LabelTraversal.slots rs, S.R k = []) →
      let xs := List.range (volume prime v)
      let keep := LabelStock.live m w (LabelTransport.payload v)
      S.R (r 17) = ((xs.filter keep).map bit).map bitSymbol →
      ∃ z F c, z.user = u.user ∧
        F.R (r 18) = (xs.map (fun i => bitSymbol (if keep i then bit i else false))) ++ S.R (r 18) ∧
        F.R (r 17) = S.R (r 17) ∧ F.R (r 16) = (xs.map keep).map bitSymbol ∧
        c ≤ cost r S + (434+10*(m*m))*volume prime v ∧ Exec body p (mk u S) c (mk z F) := by
  obtain ⟨pad,hpad⟩ := LabelDecode.realizes body r m hm rs hk hd apart
  refine ⟨.seq (load r) pad, ?_⟩
  intro roles v w B hw hp hv bit u S rep hf hs
  dsimp only
  intro hx
  obtain ⟨u₁,M,n,hu,hn,hin,hout,he⟩ := load_exec body r roles v w u S rep
  have same (i : Fin 26) (hi : i.val < 19) : M.R (r i) = S.R (r i) := by
    apply (hout _ ?_).1
    intro h
    obtain ⟨j,_,e⟩ := List.mem_map.mp h
    have h' := congrArg Fin.val (r.injective e)
    change 19+j.val = i.val at h'
    omega
  obtain ⟨z,F,c,hz,ho,hsrc,hmask,hc,hr⟩ := hpad v w B hw hp hv bit u₁ M (fun i => (hin i).1)
    (fun i hi => (same i (by omega)).trans (hf i hi)) (by
      intro k h
      apply Eq.trans (hout k ?_).1 (hs k h)
      intro h'
      obtain ⟨i,_,e⟩ := List.mem_map.mp h'
      exact apart _ (e.symm ▸ h)) ((same 17 (by decide)).trans hx)
  exact ⟨z,F,n+c,hz.trans hu,ho.trans (congrArg (_ ++ ·) (same 18 (by decide))),
    hsrc.trans (same 17 (by decide)),hmask,Nat.add_le_add hn hc,Exec.seq he hr⟩

end
end IntegerMultBounds.MathlibTM2.Cover.LabelCallerHeaders
