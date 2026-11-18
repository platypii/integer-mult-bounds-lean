module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackAnchor
public import IntegerMultBounds.MathlibTM2.Cover.FallbackClass
public import IntegerMultBounds.MathlibTM2.Host.Placed

/-! Run the anchor machine on the host, reading the sign stream at the current record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8 AtomSegment AtomBank ActualAffineScaling
variable {T n b f W : ℕ}
local instance : NeZero (modulus b) := ⟨(modulus_pos b).ne'⟩
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

/-- After the preceding records have been consumed, the emitted symbol under the
head selects the anchor sign of this label's full-width itinerary. -/
theorem projectorSign_head {m w : ℕ} (hw : 0 < w) (e : (Fin m ⊕ Fin m) ≃ Fin n)
    (P : Matrix (Fin m) (Fin m) ℚ) (hp : P*P = P) (adm : Swap.Modular.Admissible prime P)
    (α α' : Fin m → ZMod (prime^w)) (ha : ∀ i, α i * α' i = 1)
    (g : LabelPadding.Label m w) (hg : IsUnit g.det) (p N : ℕ) (tail : List (Fin (prime+4)))
    (index : p*(prime^w)^(m*m)+(LabelAddress.address g).val < N) :
    let φ := LabelRing.res prime w hw
    let table := projectorResidual e (Swap.Modular.reduce prime P) (φ ∘ α) (φ ∘ α')
    let G := projectorResidual e (Swap.Modular.reduce (prime^w) P) α α' g
    let pivots := classPivots (table (φ.mapMatrix g))
    let j := p*(prime^w)^(m*m)+(LabelAddress.address g).val
    ∃ negative, ((signStream table w N ++ tail).drop j).head? = some (bitSymbol negative) ∧
      Itinerary.Valid pivots G n ∧ (Itinerary.run pivots G n).det = if negative then -1 else 1 := by
  obtain ⟨neg,sym,valid,det⟩ := projectorSign_at (A := prime) hw e P hp adm α α' ha g hg p N index
  refine ⟨neg,?_,valid,det⟩
  rw [List.head?_drop,List.getElem?_append_left (by simpa [signStream] using index)]
  exact sym

private theorem extend_idle {t q A : ℕ} (M : Program t q A) :
    Idle (extend M T) (fun i => ∃ j, i = Fin.natAdd t j) := by
  intro st sy st' act h i hi
  obtain ⟨j,rfl⟩ := hi
  obtain ⟨⟨_,_⟩,_,e⟩ := Option.map_eq_some_iff.mp h
  cases e
  simp

private theorem branch_idle {t q r A : ℕ} {M : Program t q A} {N : Program t r A}
    (test : (Fin t → Fin (A+4)) → Bool) {I : Fin t → Prop} (hm : Idle M I) (hn : Idle N I) :
    Idle (branch test M N) I := by
  intro st sy st' act h i hi
  induction st using Fin.addCases with
  | left st =>
    induction st using Fin.addCases with
    | left st =>
      simp only [branch,Fin.addCases_left] at h
      obtain ⟨⟨s,a⟩,step,e⟩ := Option.map_eq_some_iff.mp h
      cases e
      exact hm _ _ _ _ step _ hi
    | right st =>
      simp only [branch,Fin.addCases_left,Fin.addCases_right] at h
      obtain ⟨⟨s,a⟩,step,e⟩ := Option.map_eq_some_iff.mp h
      cases e
      exact hn _ _ _ _ step _ hi
  | right st =>
    simp only [branch,Fin.addCases_right] at h
    split at h <;> cases h <;> rfl

/-- The foreign call reads the next sign directly from the represented right stack,
including when that stack carries more records after the current one. -/
theorem anchorHost_exec {P U : Type} (sign : Fin T) (caller : Tapes T prime) (negative : Bool)
    (hf : 0 < f) (hb : 0 < b) (hW : 0 < W) (a : FlatCoordinateStages.Array ((n+1)*f) b W)
    (body : P → Pr P _ _ prime U) (u : HS _ _ prime U) (S : Stacks _ prime)
    (rep : RepT ((outer (anchorSlots n) (neutral b W) (arrTape a) f).append caller) S.L S.R)
    (head : (S.R (Fin.natAdd (22+anchorSlots n) sign)).head? = some (bitSymbol negative)) :
    let cost := chainConst (anchorOps n negative) * f * ((modulus b)^((n+1)*f)*W) + 1
    ∃ a' : FlatCoordinateStages.Array ((n+1)*f) b W, ∃ z, ∃ (F : Stacks (22+anchorSlots n+T) prime), ∃ t,
      Exec body (foreign (anchorDispatch n sign)) (mk u S) t (mk z F) ∧
      t ≤ cost * (22+anchorSlots n+T+5)+6 ∧ z.user = u.user ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ j : Fin T, let i := Fin.natAdd (22+anchorSlots n) j
        F.L i = S.L i ∧ (S.R i ≠ [] → F.R i = S.R i)) ∧
      RepT ((outer (anchorSlots n) (neutral b W) (arrTape a') f).append caller) F.L F.R ∧
      ∀ (x : Fin (n+1) → Fin f → ZMod (modulus b)) (j : Fin W),
        a' (FlatCoordinateLayout.index (AtomOps.refine
          (Fin.cons (fun k => if negative then -x 0 k else x 0 k) (fun i => x i.succ))) j) =
          a (FlatCoordinateLayout.index (AtomOps.refine x) j) := by
  have read := rep (Fin.natAdd _ sign) (caller.head sign)
  simp only [Tapes.append,Fin.addCases_right,sub_self,readAt] at read
  have hs : caller.reads sign = bitSymbol negative := by
    rw [List.head?_eq_getElem?] at head
    simpa [Tapes.reads,head] using read
  obtain ⟨a',run,action⟩ := anchorDispatch_runs caller sign negative hs hf hb hW a
  obtain ⟨z,F,_,rfl,hrep,hu,hi,ho,_,frame,t,ht,he⟩ :=
    foreign_exec_frame body _ (branch_idle _ (extend_idle _) (extend_idle _)) run u S _ rfl rep
  refine ⟨a',z,F,t,he,ht,hu,hi,ho,?_,hrep,action⟩
  intro j
  have h := frame _ ⟨j,rfl⟩
  exact ⟨h.1,fun ne => (idle_stacks_eq h ne).2⟩

/-- Dispatch on one sign and remove it from the stream before the next record. -/
def anchorRecord {P U : Type} (n : ℕ) (sign : Fin T) :=
  Prog.seq (foreign (P := P) (U := U) (anchorDispatch n sign)) (.act (.pop (.rt (Fin.natAdd (22+anchorSlots n) sign))
    (fun v _ => v) .done))

theorem anchorRecord_exec {P U : Type} (sign : Fin T) (caller : Tapes T prime) (negative : Bool)
    (hf : 0 < f) (hb : 0 < b) (hW : 0 < W) (a : FlatCoordinateStages.Array ((n+1)*f) b W)
    (body : P → Pr P _ _ prime U) (u : HS _ _ prime U) (S : Stacks _ prime)
    (rep : RepT ((outer (anchorSlots n) (neutral b W) (arrTape a) f).append caller) S.L S.R)
    (tail : List (Fin (prime+4))) (stream : S.R (Fin.natAdd (22+anchorSlots n) sign) = bitSymbol negative :: tail) :
    let cost := chainConst (anchorOps n negative) * f * ((modulus b)^((n+1)*f)*W) + 1
    ∃ a' : FlatCoordinateStages.Array ((n+1)*f) b W, ∃ z, ∃ (F : Stacks (22+anchorSlots n+T) prime), ∃ t,
      Exec body (anchorRecord n sign) (mk u S) t
        (mk z {F with R := Function.update F.R (Fin.natAdd (22+anchorSlots n) sign) tail}) ∧
      t ≤ cost * (22+anchorSlots n+T+5)+7 ∧ z.user = u.user ∧ F.inp = S.inp ∧ F.out = S.out ∧
      RepT ((outer (anchorSlots n) (neutral b W) (arrTape a') f).append caller) F.L F.R ∧
      ∀ (x : Fin (n+1) → Fin f → ZMod (modulus b)) (j : Fin W),
        a' (FlatCoordinateLayout.index (AtomOps.refine
          (Fin.cons (fun k => if negative then -x 0 k else x 0 k) (fun i => x i.succ))) j) =
          a (FlatCoordinateLayout.index (AtomOps.refine x) j) := by
  obtain ⟨a',z,F,t,run,bound,hu,hi,ho,keep,hrep,act⟩ :=
    anchorHost_exec sign caller negative hf hb hW a body u S rep (by simp [stream])
  refine ⟨a',z,F,t+1,Exec.seq run ?_,by omega,hu,hi,ho,hrep,act⟩
  have kept := (keep sign).2 (by simp [stream])
  simpa [Action.run,kept,stream,update_rt,store_mk] using (Exec.act (body := body)
    (.pop (.rt (Fin.natAdd (22+anchorSlots n) sign)) (fun v _ => v) .done) (mk z F))

/-- Mark every caller register except the sign, then drop one symbol from each.
This consumes the sign and restores even an initially empty queue or scratch register. -/
def framedAnchor {P U : Type} (n : ℕ) (sign : Fin T) :=
  let ports := (List.finRange T).map (Fin.natAdd (22+anchorSlots n))
  let marks := ports.erase (Fin.natAdd (22+anchorSlots n) sign)
  Prog.seq (markList (P := P) (U := U) marks)
    (.seq (foreign (anchorDispatch n sign)) (dropList ports))

theorem framedAnchor_exec {P U : Type} (sign : Fin T) (negative : Bool)
    (hf : 0 < f) (hb : 0 < b) (hW : 0 < W) (a : FlatCoordinateStages.Array ((n+1)*f) b W)
    (body : P → Pr P _ _ prime U) (u : HS _ _ prime U) (S : Stacks _ prime)
    (active : ∀ i j, (outer (anchorSlots n) (neutral b W) (arrTape a) f).tape i j =
      readAt blank (S.L (Fin.castAdd T i)) (S.R (Fin.castAdd T i))
        (j-(outer (anchorSlots n) (neutral b W) (arrTape a) f).head i))
    (tail : List (Fin (prime+4))) (stream : S.R (Fin.natAdd (22+anchorSlots n) sign) = bitSymbol negative :: tail) :
    let cost := chainConst (anchorOps n negative) * f * ((modulus b)^((n+1)*f)*W) + 1
    ∃ a' : FlatCoordinateStages.Array ((n+1)*f) b W, ∃ z F t,
      Exec body (framedAnchor n sign) (mk u S) t (mk z F) ∧
      t ≤ cost * (22+anchorSlots n+T+5)+2*T+8 ∧ z.user = u.user ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ j : Fin T, let i := Fin.natAdd (22+anchorSlots n) j
        F.L i = S.L i ∧ F.R i = if j = sign then tail else S.R i) ∧
      (∀ i j, (outer (anchorSlots n) (neutral b W) (arrTape a') f).tape i j =
        readAt blank (F.L (Fin.castAdd T i)) (F.R (Fin.castAdd T i))
          (j-(outer (anchorSlots n) (neutral b W) (arrTape a') f).head i)) ∧
      ∀ (x : Fin (n+1) → Fin f → ZMod (modulus b)) (j : Fin W),
        a' (FlatCoordinateLayout.index (AtomOps.refine
          (Fin.cons (fun k => if negative then -x 0 k else x 0 k) (fun i => x i.succ))) j) =
          a (FlatCoordinateLayout.index (AtomOps.refine x) j) := by
  let N := 22+anchorSlots n
  let ports := (List.finRange T).map (Fin.natAdd N)
  let marks := ports.erase (Fin.natAdd N sign)
  have nd : ports.Nodup := (List.nodup_finRange T).map (Fin.natAdd_injective _ _)
  have mem (j : Fin T) : Fin.natAdd N j ∈ ports := by simp [ports]
  have outside (i : Fin N) : Fin.castAdd T i ∉ ports := by
    intro h
    obtain ⟨j,_,eqn⟩ := List.mem_map.mp h
    have v := congrArg Fin.val eqn
    simp at v
    omega
  have marked (i : Fin (N+T)) : i ∈ marks ↔ i ≠ Fin.natAdd N sign ∧ i ∈ ports := nd.mem_erase_iff
  let B : Stacks (N+T) prime := {S with R := fun i => if i ∈ marks then blank :: S.R i else S.R i}
  let caller : Tapes T prime := ⟨fun _ => 0,fun j => readAt blank (B.L (Fin.natAdd N j)) (B.R (Fin.natAdd N j))⟩
  have rep : RepT ((outer (anchorSlots n) (neutral b W) (arrTape a) f).append caller) B.L B.R := by
    intro i j
    induction i using Fin.addCases with
    | left i => simpa [Tapes.append,B,marked,outside] using active i j
    | right i => simp [caller,Tapes.append,N]
  have sig : B.R (Fin.natAdd N sign) = bitSymbol negative :: tail := by simp [B,marked,stream,N]
  obtain ⟨a',z,F,t,run,c,hu,hin,hout,keep,rep',action⟩ :=
    anchorHost_exec sign caller negative hf hb hW a body u B rep (show (B.R (Fin.natAdd N sign)).head? = _ by rw [sig]; rfl)
  have start := markList_exec body marks (nd.erase _) u S
  have finish := dropList_exec body ports nd z F
  refine ⟨a',z,_,_,Exec.seq start (Exec.seq run finish),?_,hu,hin,hout,?_,?_,action⟩
  · have l : ports.length = T := by simp [ports]
    have le := List.length_erase_le (a := Fin.natAdd N sign) (l := ports)
    dsimp only [marks] at *
    omega
  · intro j
    have ne : B.R (Fin.natAdd N j) ≠ [] := by
      by_cases eqn : j = sign
      · subst j; simp [sig]
      · simp [B,marked,mem,eqn]
    have h := keep j
    refine ⟨h.1,?_⟩
    change (if Fin.natAdd N j ∈ ports then (F.R _).tail else F.R _) = _
    rw [ite_eq_left (mem j),h.2 ne]
    by_cases eqn : j = sign
    · subst j; simp [sig,N]
    · simp [B,marked,mem,eqn,N]
  · intro i j
    simpa [Tapes.append,outside] using rep' (Fin.castAdd T i) j

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
