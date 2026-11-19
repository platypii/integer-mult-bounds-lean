module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackCleanPairShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPlacedShear

/-! Run a weighted shear on the swap host, preserving the other work tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A d W b w : ℕ} {P U α : Type} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def placedPairShear (bank : Fin 35 ↪ Fin T) (capacity : 217 ≤ Q) (b : ℕ)
    (i k t : Fin d) (inverse negative : Bool) (useOne : Bool := false) : Pr P T Q A U :=
  statePlacedNormalized bank capacity (by decide) Empty.elim
    (cleanPairShear b i k t inverse (Function.Embedding.refl _) negative useOne)

theorem placedPairShear_exec (bank : Fin 35 ↪ Fin T) (capacity : 217 ≤ Q) (i k t : Fin d) (hk : k < t)
    (inverse negative : Bool) (a : Fin d → ZMod M) (unit : IsUnit (a i)) (hb : b.Prime)
    (body : P → Pr P T Q A U) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))) (sym : α → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → α) (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (ready : ColumnReady bank H J (Matrix.diagonal a) tail sym source dest p q original addr S) (useOne : Bool := false) :
    let weight := if useOne then 1 else a i
    let c := if negative then -Ring.inverse weight else if inverse then Ring.inverse weight else weight
    ∃ z F n, z.user = v.user ∧ n ≤ 1 + cleanPairShearTime (P := Empty) (U := U) (A := A)
      Empty.elim (Function.Embedding.refl _) i k t b w W H J inverse negative useOne ∧
      Exec body (placedPairShear bank capacity b i k t inverse negative useOne) (mk v S) n (mk z F) ∧
      ColumnReady bank H J (Matrix.diagonal a) tail sym source dest p q original
        (fun x => Function.update (addr x) t (addr x t+c*addr x k)) F ∧
      ∀ j, (∀ h, bank h ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro weight c
  obtain ⟨word,layout,atAddr⟩ := (columnReady_project ..).mp ready
  obtain ⟨u,D,n,out,hu,hn,run,next,effect⟩ := cleanPairShear_exec (P := Empty) Empty.elim i k t hk inverse
    (Function.Embedding.refl _) a unit hb H J hm hw hW (stateLiftDown (by decide : 0 < 217) (embDn bank v))
    (embStk bank S) tail sym source dest p q word empty layout negative useOne
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized bank bank.injective capacity (by decide) Empty.elim
    (body' := body) (fun e => nomatch e) v S run
  refine ⟨z,_,_,hz.trans hu,Nat.add_le_add_left hn 1,placed,(columnReady_project ..).mpr ?_,fun j hj => embOvr_off _ _ hj⟩
  rw [embStk_ovr bank.injective]
  exact ⟨out,next,fun x j => (effect (addr x) j).trans (atAddr x j)⟩

def childHeaderPorts : Fin 35 ↪ Fin 36 := Fin.castLEEmb (by decide)

def placedChildShear {m : ℕ} (bank : Fin 36 ↪ Fin T) (capacity : 217 ≤ Q)
    (b j i : ℕ) (k t : Fin m) (negative : Bool) : Pr P T Q A U :=
  statePlacedNormalized bank capacity (by decide) Empty.elim
    (cleanChildShear b j i k t negative (Function.Embedding.refl _))

theorem placedChildShear_exec {m n : ℕ} (bank : Fin 36 ↪ Fin T) (capacity : 217 ≤ Q)
    (k t : Fin m) (hk : k < t) (negative : Bool) (parent : Fin n → ZMod M) (j : Fin n) (inv : ZMod M)
    (reciprocal : parent j * inv = 1) (pivot : Fin d → ZMod M) (i : Fin d) (unit : IsUnit (pivot i))
    (hb : b.Prime) (body : P → Pr P T Q A U) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T Q A U) (S : Stacks T A) (tail rest : List (Fin (A+4))) (sym : α → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (empty : ∀ z, q ≤ z → z < q+(M^m*W : ℕ) → dest z = blank)
    (original : Fin (M^m*W) → α) (addr : (Fin m → ZMod M) → Fin m → ZMod M)
    (weights : S.R (bank 35) = (List.ofFn fun h => binSyms H (parent h).val).flatten ++ rest) :
    let record := (List.ofFn fun h => binSyms (A := A) H (pivot h).val).flatten ++ tail
    let ready := ColumnRecordReady (childHeaderPorts.trans bank) H J record sym source dest p q original
    let c := if negative then -(inv * Ring.inverse (pivot i)) else parent j * pivot i
    ready addr S → ∃ z F l, z.user = v.user ∧ l ≤ 1 + cleanChildShearTime (P := Empty) (U := U)
      (A := A) Empty.elim (Function.Embedding.refl _) b j.val i.val k t negative w W H J ∧
      Exec body (placedChildShear bank capacity b j.val i.val k t negative) (mk v S) l (mk z F) ∧
      ready (fun x => Function.update (addr x) t (addr x t+c*addr x k)) F ∧ F.R (bank 35) = S.R (bank 35) ∧
      ∀ h, (∀ a, bank a ≠ h) → F.L h = S.L h ∧ F.R h = S.R h := by
  intro record ready c ⟨word,layout,atAddr⟩
  have work : childWork = shearWork.map childHeaderPorts := by decide
  obtain ⟨u,D,l,hu,hl,run,clean,keep,dst,out,src,effect⟩ := cleanChildShear_exec k t hk negative
    (P := Empty) Empty.elim (Function.Embedding.refl _) parent j inv reciprocal pivot i unit hb H hm
    (stateLiftDown (by decide : 0 < 217) (embDn bank v)) (embStk bank S) tail rest weights layout.archive
    layout.modulus layout.padded layout.clock J hw hW layout.width layout.one
    (by intro h hh; rw [work,List.mem_map] at hh; obtain ⟨a,ha,rfl⟩ := hh; exact layout.scratch a ha)
    sym source dest p q word empty (fun z => (layout.src z).symm) (fun z => (layout.dst z).symm)
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized bank bank.injective capacity (by decide) Empty.elim
    (body' := body) (fun e => nomatch e) v S run
  let F := embOvr bank D.get S
  have eq : embStk bank F = D := embStk_ovr bank.injective _ _
  rw [← eq] at keep clean dst src
  refine ⟨z,F,_,hz.trans hu,Nat.add_le_add_left hl 1,placed,⟨out,?_,fun x h => (effect (addr x) h).trans (atAddr x h)⟩,
    keep 35 (by decide),fun h off => embOvr_off _ _ off⟩
  exact ⟨(keep 2 (by decide)).trans layout.modulus,(keep 27 (by decide)).trans layout.width,
    (keep 28 (by decide)).trans layout.one,(keep 32 (by decide)).trans layout.padded,
    (congrArg List.length (keep 33 (by decide))).trans layout.clock,(keep 34 (by decide)).trans layout.archive,
    fun a ha => clean (childHeaderPorts a) (work ▸ List.mem_map.mpr ⟨a,ha,rfl⟩),src,dst⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
