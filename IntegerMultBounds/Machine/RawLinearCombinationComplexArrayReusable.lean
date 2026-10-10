import IntegerMultBounds.Machine.RawLinearCombinationComplexArray
import IntegerMultBounds.Machine.BlankWordPairRecycleBank

/-! The fixed polynomial scalar stream has normalized, reusable physical
endpoints: computed records replace original source arrays, every head returns
to zero, and every generated stream, control and arithmetic tape is blank. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationComplexArrayReusable
noncomputable section
open ButterflyStreamData (Coefficient full prefixTape position encoded)
open RawLinearCombinationComplexArray (result state counted)
open RadixLinearCombinationRefresh (Expr Size)
open RadixLinearCombinationBootstrap (empty)
variable {c S n : ℕ}

abbrev count (c S : ℕ) := RawLinearCombinationComplexCoefficient.count c S

def serialized (data : Fin n → Coefficient) : List (Fin 6) := (List.ofFn (fun i => encoded (data i))).flatten

theorem serialized_length (data : Fin n → Coefficient) (w : ℕ)
    (hw : ∀ i,(data i).1.length=w ∧ (data i).2.length=w) :
    (serialized data).length=n*(2*(w+1)) := by
  have h := ButterflyStreamEndpoint.position_all 0 data w hw
  simp only [position,CyclicRowCycle.prefix_all,zero_add] at h
  exact_mod_cast h

theorem serialized_nonblank (data : Fin n → Coefficient) :
    ∀ x∈serialized data,x≠blank := by
  intro x hx
  obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hxs
  simp only [encoded,DelimitedRadixRecord.complex,DelimitedRadixRecord.field,List.mem_append,
    List.mem_map,List.mem_singleton] at hx
  rcases hx with (⟨d,_,rfl⟩|rfl)|(⟨d,_,rfl⟩|rfl)
  all_goals
    intro h
    have hv := congrArg Fin.val h
    dsimp only [RadixDigits.digitSymbol,blank,separator] at hv
    omega

def normalized (data : Fin c → Fin n → Coefficient) : Tapes (count c S) 2 :=
  (⟨fun _ => 0,fun j => full (fun _ => blank) 0 (data j)⟩ : Tapes c 2).append
    ((empty c).append ((empty c).append ((empty c).append (empty S))))

def placement (c S : ℕ) : Fin (count c S) ≃ Fin (count c S) where
  toFun := Fin.addCases (Fin.castAdd (c+(c+(c+S))))
    (Fin.addCases (fun i => Fin.natAdd c (Fin.natAdd c (Fin.natAdd c (Fin.castAdd S i))))
      (Fin.addCases (fun i => Fin.natAdd c (Fin.castAdd (c+(c+S)) i))
        (Fin.addCases (fun i => Fin.natAdd c (Fin.natAdd c (Fin.castAdd (c+S) i)))
          (fun i => Fin.natAdd c (Fin.natAdd c (Fin.natAdd c (Fin.natAdd c i)))))))
  invFun := Fin.addCases (Fin.castAdd (c+(c+(c+S))))
    (Fin.addCases (fun i => Fin.natAdd c (Fin.natAdd c (Fin.castAdd (c+S) i)))
      (Fin.addCases (fun i => Fin.natAdd c (Fin.natAdd c (Fin.natAdd c (Fin.castAdd S i))))
        (Fin.addCases (fun i => Fin.natAdd c (Fin.castAdd (c+(c+S)) i))
          (fun i => Fin.natAdd c (Fin.natAdd c (Fin.natAdd c (Fin.natAdd c i)))))))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => simp
    | right i =>
      induction i using Fin.addCases with
      | left i => simp
      | right i =>
        induction i using Fin.addCases with
        | left i => simp
        | right i => induction i using Fin.addCases <;> simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => simp
    | right i =>
      induction i using Fin.addCases with
      | left i => simp
      | right i =>
        induction i using Fin.addCases with
        | left i => simp
        | right i => induction i using Fin.addCases <;> simp

private theorem active_final (hc : 0<c) (es : Fin c → Expr c) (data : Fin c → Fin n → Coefficient)
    :
    Placement.active (u:=0) (placement c S)
      (state hc es (fun _ _ => blank) (fun _ _ => blank) (fun _ => 0) (fun _ => 0) data n)=
      BlankWordPairRecycleBank.bank (fun j => serialized (data j))
        (fun j => serialized (result hc es data j)) ∅
        ((empty c).append ((empty c).append (empty S))) := by
  apply Placement.Tapes.ext'
  all_goals
    intro j
    induction j using Fin.addCases with
    | left j =>
      simp only [Placement.active,Fin.castAdd_zero,Fin.cast_eq_self,placement,Equiv.coe_fn_mk,state,BlankWordPairRecycleBank.bank,Tapes.append,
        Fin.addCases_left,Finset.notMem_empty,ite_false,full,serialized,position,CyclicRowCycle.prefix_all,zero_add]
    | right j =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Placement.active,Fin.castAdd_zero,Fin.cast_eq_self,placement,Equiv.coe_fn_mk,state,BlankWordPairRecycleBank.bank,Tapes.append,
          Fin.addCases_right,Fin.addCases_left,Finset.notMem_empty,ite_false,position,prefixTape,
          CyclicRowCycle.prefix_all,zero_add,serialized]
      | right j =>
        induction j using Fin.addCases with
        | left j => simp only [Placement.active,Fin.castAdd_zero,Fin.cast_eq_self,placement,Equiv.coe_fn_mk,state,BlankWordPairRecycleBank.bank,Tapes.append,
            Fin.addCases_right,Fin.addCases_left]
        | right j =>
          induction j using Fin.addCases <;>
            simp only [Placement.active,Fin.castAdd_zero,Fin.cast_eq_self,placement,Equiv.coe_fn_mk,state,BlankWordPairRecycleBank.bank,Tapes.append,
              Fin.addCases_right,Fin.addCases_left]

private theorem active_normalized (hc : 0<c) (es : Fin c → Expr c) (data : Fin c → Fin n → Coefficient) :
    Placement.active (u:=0) (placement c S) (normalized (S:=S) (result hc es data))=
      BlankWordPairRecycleBank.output (fun j => serialized (result hc es data j))
        ((empty c).append ((empty c).append (empty S))) := by
  apply Placement.Tapes.ext'
  all_goals
    intro j
    induction j using Fin.addCases with
    | left j => simp only [Placement.active,Fin.castAdd_zero,Fin.cast_eq_self,placement,Equiv.coe_fn_mk,normalized,BlankWordPairRecycleBank.output,Tapes.append,
        Fin.addCases_left,full,serialized]
    | right j =>
      induction j using Fin.addCases with
      | left j => simp only [Placement.active,Fin.castAdd_zero,Fin.cast_eq_self,placement,Equiv.coe_fn_mk,normalized,BlankWordPairRecycleBank.output,Tapes.append,
          Fin.addCases_right,Fin.addCases_left]
      | right j =>
        induction j using Fin.addCases with
        | left j => simp only [Placement.active,Fin.castAdd_zero,Fin.cast_eq_self,placement,Equiv.coe_fn_mk,normalized,BlankWordPairRecycleBank.output,Tapes.append,
            Fin.addCases_right,Fin.addCases_left]
        | right j =>
          induction j using Fin.addCases <;>
            simp only [Placement.active,Fin.castAdd_zero,Fin.cast_eq_self,placement,Equiv.coe_fn_mk,normalized,BlankWordPairRecycleBank.output,Tapes.append,
              Fin.addCases_right,Fin.addCases_left]

def recycle (hc : 0<c) :=
  Placement.placed (u:=0) (BlankWordPairRecycleBank.program (a:=2) (u:=c+(c+S)) hc) (placement c S)

theorem recycle_runs (hc : 0<c) (es : Fin c → Expr c) (data : Fin c → Fin n → Coefficient)
    (w : ℕ) (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) :
    HoareTime (recycle (S:=S) hc)
      (fun v => v=state hc es (fun _ _ => blank) (fun _ _ => blank) (fun _ => 0) (fun _ => 0) data n)
      (fun v => v=normalized (S:=S) (result hc es data)) (c*(7*(n*(2*(w+1)))+17)) := by
  have hr := RawLinearCombinationComplexArray.result_width hc es data w hw
  have h := Placement.hoare_at (u:=0) (BlankWordPairRecycleBank.runs hc
    (fun j => serialized (data j)) (fun j => serialized (result hc es data j))
    ((empty c).append ((empty c).append (empty S))) (n*(2*(w+1)))
    (fun j => serialized_length _ w (hw j)) (fun j => serialized_length _ w (hr j))
    (fun j => serialized_nonblank (data j)) (fun j => serialized_nonblank (result hc es data j)))
    (placement c S) _ (active_final (S:=S) hc es data)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  have he : Placement.extra (u:=0) (placement c S)
      (state hc es (fun _ _ => blank) (fun _ _ => blank) (fun _ => 0) (fun _ => 0) data n)=
      Placement.extra (u:=0) (placement c S) (normalized (S:=S) (result hc es data)) := by
    apply Placement.Tapes.ext'
    all_goals intro i; exact Fin.elim0 i
  rw [Placement.replace,he,← active_normalized hc es data]
  exact Placement.view _ _

def originalCount (bs : List Bool) := MarkedWordCleanup.one (RadixZeroFill.encodedBinary (q:=2) bs) 1

def bank (data : Fin c → Fin n → Coefficient) (bs : List Bool) :=
  CountedLoopHeaderClean.bank ((normalized (S:=S) data).append (originalCount bs))

def program (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ j,Size (es j)≤S) :=
  seq (RawLinearCombinationComplexArray.program hc es hs) (extend (extend (recycle (S:=S) hc) 1) 2)

/-- Complete physical scalar-array execution from normalized original streams
through replacement and every private cleanup; the original count is retained. -/
theorem runs (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ j,Size (es j)≤S)
    (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (bs : List Bool) (hn : Counter.value bs=n) :
    HoareTime (program hc es hs) (fun v => v=bank (S:=S) data bs)
      (fun v => v=bank (S:=S) (result hc es data) bs)
      (n*(RawLinearCombinationComplexArray.bodyCost es w+6)+11*bs.length+35+
        c*(7*(n*(2*(w+1)))+17)+1) := by
  have h0 := RawLinearCombinationComplexArray.runs hc es hs (fun _ _ => blank) (fun _ _ => blank)
    (fun _ => 0) (fun _ => 0) data w hw bs hn
  have hinit : state (S:=S) hc es (fun _ _ => blank) (fun _ _ => blank)
      (fun _ => 0) (fun _ => 0) data 0=normalized (S:=S) data := by
    simp only [state,normalized,position,prefixTape,CyclicRowCycle.rowPrefix,List.take_zero,List.flatten_nil,
      List.length_nil,Nat.cast_zero,add_zero]
    rfl
  simp only [counted,hinit] at h0
  have h1 := hoare_extend_eq (hoare_extend_eq (recycle_runs (S:=S) hc es data w hw) (originalCount bs))
    (SharedBank.empty 2 2)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.RawLinearCombinationComplexArrayReusable
