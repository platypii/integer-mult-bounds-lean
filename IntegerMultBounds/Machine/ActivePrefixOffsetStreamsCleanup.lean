import IntegerMultBounds.Machine.WordBankCleanup
import IntegerMultBounds.Machine.FiniteReturnStackAt
import IntegerMultBounds.Machine.SharedBank

/-! Four physical caller streams: erase completed T/Z backwards, erase X from
its restored origin, and rewind the retained output. Empty words are included. -/
namespace IntegerMultBounds.Machine.ActivePrefixOffsetStreamsCleanup
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

def word (xs : List Bool) : ℤ → Fin (a+4) := putWord (fun _ => blank) 0 (xs.map bitSymbol)
def eraseProgram (slot : Fin t) := Placement.placed (EraseBack.program (a := a)) (FiniteReturnStackAt.placement slot)
def returnProgram (slot : Fin t) := Placement.placed (ReturnOrigin.program (a := a)) (FiniteReturnStackAt.placement slot)

theorem erase_at (v : Tapes t a) (slot : Fin t) (xs : List Bool)
    (ht : v.tape slot=word xs) (hh : v.head slot=xs.length) :
    HoareTime (eraseProgram slot) (fun w => w=v)
      (fun w => w=setTape v slot (fun _ => blank) 0) (xs.length+2) := by
  have h := EraseBack.erase_hoare (a := a) (fun _ => blank) 0 (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl (by intros; rfl)
  simp only [List.length_map,zero_add] at h
  have hp := Placement.hoare_at h (FiniteReturnStackAt.placement slot) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hh]
    rfl)
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank slot v _ _

theorem return_at (v : Tapes t a) (slot : Fin t) (xs : List Bool)
    (ht : v.tape slot=word xs) (hh : v.head slot=xs.length) :
    HoareTime (returnProgram slot) (fun w => w=v)
      (fun w => w=setTape v slot (word xs) 0) (xs.length+2) := by
  have h := ReturnOrigin.return_hoare (a := a) (xs.map bitSymbol) (ReturnOrigin.bits_nonblank xs)
  simp only [List.length_map] at h
  have hp := Placement.hoare_at h (FiniteReturnStackAt.placement slot) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hh]
    rfl)
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank slot v _ _

def program (focus : Fin 4 → Fin t) (ht : 1≤t) :=
  seq (seq (seq (eraseProgram (a := a) (focus 0)) (eraseProgram (a := a) (focus 2)))
    (WordBankCleanup.clearProgram (focus 1) ht a)) (returnProgram (a := a) (focus 3))
def erasedT (v : Tapes t a) (focus : Fin 4 → Fin t) := setTape v (focus 0) (fun _ => blank) 0
def erasedZ (v : Tapes t a) (focus : Fin 4 → Fin t) := setTape (erasedT v focus) (focus 2) (fun _ => blank) 0
def erasedX (v : Tapes t a) (focus : Fin 4 → Fin t) := WordBankCleanup.write (erasedZ v focus) (focus 1) (fun _ => blank)
def result (v : Tapes t a) (focus : Fin 4 → Fin t) (out : List Bool) := setTape (erasedX v focus) (focus 3) (word out) 0

theorem runs (v : Tapes t a) (focus : Fin 4 → Fin t) (hf : Function.Injective focus) (ht : 1≤t)
    (T X Z out : List Bool)
    (hT : v.tape (focus 0)=word T) (hX : v.tape (focus 1)=word X)
    (hZ : v.tape (focus 2)=word Z) (hO : v.tape (focus 3)=word out)
    (pT : v.head (focus 0)=T.length) (pX : v.head (focus 1)=0)
    (pZ : v.head (focus 2)=Z.length) (pO : v.head (focus 3)=out.length) :
    HoareTime (program focus ht) (fun w => w=v) (fun w => w=result v focus out)
      (T.length+Z.length+2*X.length+out.length+12) := by
  have h0 := erase_at v (focus 0) T hT pT
  have h2 := erase_at (erasedT v focus) (focus 2) Z
    (by simpa only [erasedT,setTape,Function.update_of_ne (hf.ne (by decide : (2 : Fin 4)≠0))] using hZ)
    (by simpa only [erasedT,setTape,Function.update_of_ne (hf.ne (by decide : (2 : Fin 4)≠0))] using pZ)
  have hxhead : (erasedZ v focus).head (focus 1)=0 := by
    simpa only [erasedZ,erasedT,setTape,Function.update_of_ne (hf.ne (by decide : (1 : Fin 4)≠2)),
      Function.update_of_ne (hf.ne (by decide : (1 : Fin 4)≠0))] using pX
  have h1 := WordBankCleanup.clear_hoare (erasedZ v focus) (focus 1) ht (X.map bitSymbol)
    (ReturnOrigin.bits_nonblank X) (by
      rw [hxhead]
      simpa only [word,erasedZ,erasedT,setTape,Function.update_of_ne (hf.ne (by decide : (1 : Fin 4)≠2)),
        Function.update_of_ne (hf.ne (by decide : (1 : Fin 4)≠0))] using hX)
  have h3 := return_at (erasedX v focus) (focus 3) out
    (by simpa only [erasedX,WordBankCleanup.write,erasedZ,erasedT,setTape,
      Function.update_of_ne (hf.ne (by decide : (3 : Fin 4)≠1)),
      Function.update_of_ne (hf.ne (by decide : (3 : Fin 4)≠2)),
      Function.update_of_ne (hf.ne (by decide : (3 : Fin 4)≠0))] using hO)
    (by simpa only [erasedX,WordBankCleanup.write,erasedZ,erasedT,setTape,
      Function.update_of_ne (hf.ne (by decide : (3 : Fin 4)≠2)),
      Function.update_of_ne (hf.ne (by decide : (3 : Fin 4)≠0))] using pO)
  exact (((h0.seq h2).seq h1).seq h3).consequence (fun _ h => h) (fun _ h => h)
    (by simp only [List.length_map]; omega)

theorem result_streams (v : Tapes t a) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (out : List Bool) (hX : v.head (focus 1)=0) :
    SharedBank.payload (result v focus out) focus=
      (⟨![0,0,0,0],![fun _ => blank,fun _ => blank,fun _ => blank,word out]⟩ : Tapes 4 a) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [result,erasedX,erasedZ,erasedT,WordBankCleanup.write,
    setTape,hf.eq_iff,hX]

theorem result_frame (v : Tapes t a) (focus : Fin 4 → Fin t) (out : List Bool)
    (i : Fin t) (hi : ∀ j, i≠focus j) :
    (result v focus out).head i=v.head i ∧ (result v focus out).tape i=v.tape i := by
  simp only [result,erasedX,erasedZ,erasedT,WordBankCleanup.write,setTape,
    Function.update_of_ne (hi 0),Function.update_of_ne (hi 1),Function.update_of_ne (hi 2),
    Function.update_of_ne (hi 3)]
  exact ⟨trivial,trivial⟩

end
end IntegerMultBounds.Machine.ActivePrefixOffsetStreamsCleanup
