import IntegerMultBounds.Machine.CompactGlobalRowHeaders
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet

/-! Once-only complete-row padding on forty-five fixed tapes. Its only public
numeric inputs are K,d,D,payload; no divisor, row or record-width header is
assumed. The arithmetic header bank is preserved during the actual padding. -/
namespace IntegerMultBounds.Machine.CompactGlobalRowInitialData
noncomputable section
open CompactGlobalRowHeaders
open CompactGlobalRowPadding
open ActiveRepairRankHeadersCommands (State)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def payload (source dest : ℤ → Fin (a+4)) (p q : ℤ) : Tapes 2 a := ⟨![p,q],![source,dest]⟩
def bank (st : State) (source dest : ℤ → Fin (a+4)) (p q : ℤ) : Tapes 45 a :=
  (ActiveRepairRankHeadersCommands.bank st).append (payload source dest p q)

def placement : Fin (12+33) ≃ Fin 45 where
  toFun := ![43,44,17,11,16,15,28,29,30,31,32,33,0,1,2,3,4,5,6,7,8,9,10,12,13,14,18,19,20,21,22,23,24,25,26,27,34,35,36,37,38,39,40,41,42]
  invFun := ![12,13,14,15,16,17,18,19,20,21,22,3,23,24,25,5,4,2,26,27,28,29,30,31,32,33,34,35,6,7,8,9,10,11,36,37,38,39,40,41,42,43,44,0,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def prepare (c m : ℕ) := extend (CompactGlobalRowHeaders.program (a := a) c m) 2
def padProgram := Placement.placed (RowPaddingConstructedAlphabet.program (a := a)) placement

theorem prepares (c m d D K P : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hp : 0<P) (hD : rowAxes c m d≤D)
    (source dest : ℤ → Fin (a+4)) (p q : ℤ) :
    HoareTime (prepare (a := a) c m)
      (fun v => v=bank (initial K d D P) source dest p q)
      (fun v => v=bank (finished c m d D K P) source dest p q)
      (CompactGlobalRowHeaders.cost c m d D K P) :=
  hoare_extend_eq (CompactGlobalRowHeaders.runs c m d D K P hc hm hd hK hp hD) (payload source dest p q)

private theorem placed_exact {s u t k cost : ℕ} {M : Program s k a}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t a) (small small' : Tapes s a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) ?_ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

theorem active_bank (c m d D K P : ℕ) (source dest : ℤ → Fin (a+4)) (p q : ℤ) :
    Placement.active placement (bank (finished c m d D K P) source dest p q) =
      RowPaddingConstructedAlphabet.bank source dest p q (bits 1) (bits (originalRows c m d K))
        (bits (initialRows c m d K)) (bits (recordWidth c m d D K P)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _

theorem extra_slot_lt (i : Fin 33) : (placement (Fin.natAdd 12 i)).val<43 := by
  fin_cases i <;> decide

theorem extra_bank (st : State) (source dest source' dest' : ℤ → Fin (a+4)) (p q : ℤ) :
    Placement.extra placement (bank st source dest p q) =
      Placement.extra placement (bank st source' dest' p q) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals have he : placement (Fin.natAdd 12 i) =
      Fin.castAdd 2 (⟨(placement (Fin.natAdd 12 i)).val,extra_slot_lt i⟩ : Fin 43) := Fin.ext rfl
  all_goals rw [he]
  all_goals simp only [bank,Tapes.append,Fin.addCases_left]

theorem pads (c m d D K P : ℕ) (hc : 2≤c) (hK : 0<K) (hp : 0<P)
    (source dest : ℤ → Fin 4) (p q : ℤ)
    (x : Fin (1*originalRows c m d K*recordWidth c m d D K P) → Bool) :
    HoareTime (padProgram (a := a))
      (fun v => v=bank (finished c m d D K P)
        (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun i => bitSymbol (x i))))
        (RowPaddingConstructedAlphabet.mapTape dest) p q)
      (fun v => v=bank (finished c m d D K P)
        (RowPaddingConstructedAlphabet.erased
          (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun i => bitSymbol (x i))))
          p (1*originalRows c m d K*recordWidth c m d D K P))
        (putWord (RowPaddingConstructedAlphabet.mapTape dest) q
          (List.ofFn (RecursiveRowPadding.pad (initialRows c m d K) (bitSymbol false) (fun i => bitSymbol (x i))))) p q)
      (413*(initialRows c m d K*recordWidth c m d D K P)) := by
  have hr : 0<originalRows c m d K := pow_pos (by decide) _
  have hl : 0<recordWidth c m d D K P := Nat.mul_pos (pow_pos (by decide) _) hp
  have h := RowPaddingConstructedAlphabet.pad_bits_hoare (a := a) source dest p q
    (bits 1) (bits (originalRows c m d K)) (bits (initialRows c m d K))
    (bits (recordWidth c m d D K P)) 1 _ _ _ x
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (by decide) hr (initial_bounds c m d K (by omega) hK).1 hl
  simp only [Nat.mul_one] at h
  exact placed_exact placement _ _ _ _ (active_bank c m d D K P _ _ p q)
    (active_bank c m d D K P _ _ p q) (extra_bank _ _ _ _ _ p q) h

end
end IntegerMultBounds.Machine.CompactGlobalRowInitialData
