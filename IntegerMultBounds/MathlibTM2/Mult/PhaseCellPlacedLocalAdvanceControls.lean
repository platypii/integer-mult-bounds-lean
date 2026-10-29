module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredLocalAdvanceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPackedCellInputs
public import IntegerMultBounds.MathlibTM2.Host.Embed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def localAdvancePlacement (i : Fin 117) : Fin 168 :=
  if i = 94 then 153 else if i = 95 then 155 else if i = 106 then 154 else
  if i = 115 then 163 else ⟨i.val,by omega⟩

theorem localAdvancePlacement_injective : Function.Injective localAdvancePlacement := by
  intro i j he
  have hv := congrArg (fun k : Fin 168 => k.val) he
  simp only [localAdvancePlacement] at hv
  split_ifs at hv <;> simp_all only
  all_goals first | exact Fin.ext hv | omega

def placedLocalAdvanceControls : Pr P 168 Q A U :=
  embProg localAdvancePlacement Empty.elim (restoredLocalAdvanceControls (P := Empty))

theorem placedLocalAdvanceControls_exec (V a N w : ℕ)
    (hw : w < 2^V) (hcoords : a+N < 2^V) (hunits : (a+N)*w < 2^V)
    (offsets : List ℕ) (hne : offsets ≠ []) (hordered : offsets.Pairwise (· ≤ ·))
    (hfit : ∀ j ∈ offsets, j ≤ N)
    (cs suffix : List (Fin (A+4))) (hlen : cs.length = offsets.length)
    (v : HS 168 Q A U) (S : Stacks 168 A) (hV : (S.R 163).length = V)
    (h153 : S.R 153 = binSyms V w) (h155 : S.R 155 = binSyms V a) (h154 : S.R 154 = binSyms V 0)
    (hcount : S.R 116 = cs)
    (hpackets : S.R 109 = (offsets.map (a+·)).flatMap (binSyms V)++suffix)
    (hblank : ∀ k : Fin 168, k.val < 19 → S.R k = [])
    (h88 : S.R 88 = []) (h89 : S.R 89 = []) (h90 : S.R 90 = []) (h91 : S.R 91 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ offsets.length*(3*tblC V V+29*V+30)+8*N*w+78*V+91 ∧
      Exec body placedLocalAdvanceControls (mk v S) m
        (mk v' {S with R := Function.update S.R 91 (match offsets.map (·*w) with
          | [] => [] | j::js => gatherControls A (j::windowAdvances j js))}) := by
  have ho : (a::offsets.map (a+·)).Pairwise (· ≤ ·) := by
    apply List.pairwise_cons.mpr
    constructor
    · intro j hj; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hj; omega
    · rw [List.pairwise_map]
      exact hordered.imp (fun h => Nat.add_le_add_left h a)
  have hb : ∀ j ∈ offsets.map (a+·), j ≤ a+N := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hj
    exact Nat.add_le_add_left (hfit k hk) a
  have hsmall : ∀ k : Fin 117, k.val < 19 →
      (embStk localAdvancePlacement S).R k = [] := by
    intro k hk
    have h94 : k.val ≠ 94 := by omega
    have h95 : k.val ≠ 95 := by omega
    have h106 : k.val ≠ 106 := by omega
    have h115 : k.val ≠ 115 := by omega
    simpa [embStk,localAdvancePlacement,Fin.ext_iff,h94,h95,h106,h115] using hblank ⟨k.val,by omega⟩ hk
  have hsrc : ∀ i, (embStk localAdvancePlacement S).R (packedAdvanceSource i) =
      binSyms V (packedAdvanceValues a w (packedAdvanceSource i)) := by
    intro i
    simp only [packedAdvanceSource]
    split_ifs
    · simpa [embStk,localAdvancePlacement,packedAdvanceValues] using h155
    · simpa [embStk,localAdvancePlacement,packedAdvanceValues] using h153
    · simpa [embStk,localAdvancePlacement,packedAdvanceValues] using h154
  obtain ⟨vi,m,hui,hm,hei⟩ := restoredLocalAdvanceControls_exec (body := fun p : Empty => nomatch p)
    V a N w (by omega) hw (offsets.map (a+·)) ho (fun j hj => (hb j hj).trans_lt hcoords)
    (fun j hj => (Nat.mul_le_mul_right w (hb j hj)).trans_lt hunits) hb cs suffix
    (by simpa using hlen) (embDn localAdvancePlacement v) (embStk localAdvancePlacement S)
    hV hsrc hsmall hcount hpackets h88 h89 h90
  obtain ⟨v',hv,hu,he⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    localAdvancePlacement_injective (fun p => nomatch p) hei v rfl S rfl
  refine ⟨v',m,hu.trans hui,by simpa using hm,he.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updR localAdvancePlacement_injective,embOvr_stk]
  simp only [localAdvancePlacement,show (91 : Fin 117) ≠ 94 by decide,show (91 : Fin 117) ≠ 95 by decide,
    show (91 : Fin 117) ≠ 106 by decide,show (91 : Fin 117) ≠ 115 by decide,ite_false]
  simp only [embStk,localAdvancePlacement,Fin.reduceEq,ite_false,h91,List.append_nil]
  rw [packedGatherControls_eq w a offsets hne]
  simp only [Function.comp_def,localAdvancePlacement,Fin.reduceEq,ite_false,h91,List.append_nil]
  cases hm : offsets.map (·*w) <;> simp [hm,h91]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
