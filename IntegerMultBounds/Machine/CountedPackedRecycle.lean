import IntegerMultBounds.Machine.WordBankCleanup
import IntegerMultBounds.Machine.CountedPackedInverse

/-! Recycle the five packed intermediate words, copying the result back to
its original pair of payload tapes and physically erasing every intermediate. -/
namespace IntegerMultBounds.Machine.CountedPackedRecycle
noncomputable section
variable {a : ℕ}
open WordBankCleanup

def vSource (inverse : Bool) : Fin 9 := if inverse then 8 else 5
theorem source_ne (inverse : Bool) : vSource inverse ≠ 0 := by cases inverse <;> decide

def program (inverse : Bool) (a : ℕ) := seq (seq (seq (seq (seq (seq
  (replaceProgram (vSource inverse) 0 (source_ne inverse) (by decide) a)
  (replaceProgram (6 : Fin 9) 1 (by decide) (by decide) a))
  (clearProgram (3 : Fin 9) (by decide) a))
  (clearProgram (4 : Fin 9) (by decide) a))
  (clearProgram (5 : Fin 9) (by decide) a))
  (clearProgram (6 : Fin 9) (by decide) a))
  (clearProgram (8 : Fin 9) (by decide) a)

def result (v : Tapes 9 a) (X Y : List Bool) : Tapes 9 a :=
  let v := write (write v 0 (putWord (v.tape 0) (v.head 0) (X.map bitSymbol)))
    1 (putWord (v.tape 1) (v.head 1) (Y.map bitSymbol))
  write (write (write (write (write v 3 (fun _ => blank)) 4 (fun _ => blank))
    5 (fun _ => blank)) 6 (fun _ => blank)) 8 (fun _ => blank)

def cost (X Y s3 s4 s5 s6 s8 : List Bool) : ℕ :=
  3*X.length+3*Y.length+2*(s3.length+s4.length+s5.length+s6.length+s8.length)+33

theorem recycle_hoare (inverse : Bool) (v : Tapes 9 a) (oldV oldW s3 s4 s5 s6 s8 : List Bool)
    (f g : ℤ → Fin (a+4))
    (h0 : v.tape 0 = putWord f (v.head 0) (oldV.map bitSymbol))
    (h1 : v.tape 1 = putWord g (v.head 1) (oldW.map bitSymbol))
    (h3 : v.tape 3 = putWord (fun _ => blank) (v.head 3) (s3.map bitSymbol))
    (h4 : v.tape 4 = putWord (fun _ => blank) (v.head 4) (s4.map bitSymbol))
    (h5 : v.tape 5 = putWord (fun _ => blank) (v.head 5) (s5.map bitSymbol))
    (h6 : v.tape 6 = putWord (fun _ => blank) (v.head 6) (s6.map bitSymbol))
    (h8 : v.tape 8 = putWord (fun _ => blank) (v.head 8) (s8.map bitSymbol))
    (hlenV : (if inverse then s8 else s5).length = oldV.length)
    (hlenW : s6.length = oldW.length)
    (hf : f (v.head 0-1) = blank) (hg : g (v.head 1-1) = blank) :
    HoareTime (program inverse a) (fun w => w = v)
      (fun w => w = result v (if inverse then s8 else s5) s6)
      (cost (if inverse then s8 else s5) s6 s3 s4 s5 s6 s8) := by
  let X := if inverse then s8 else s5
  let A := write v 0 (putWord f (v.head 0) (X.map bitSymbol))
  let B := write A 1 (putWord g (v.head 1) (s6.map bitSymbol))
  have ha := replace_hoare v (vSource inverse) 0 (source_ne inverse) (by decide)
    (fun _ => blank) f (X.map bitSymbol) (oldV.map bitSymbol)
    (by simpa [X] using hlenV)
    (by cases inverse with
      | false => simpa [vSource,X] using h5
      | true => simpa [vSource,X] using h8)
    h0 (ReturnOrigin.bits_nonblank X) rfl rfl hf
  have hb := replace_hoare A (6 : Fin 9) 1 (by decide) (by decide)
    (fun _ => blank) g (s6.map bitSymbol) (oldW.map bitSymbol)
    (by simpa using hlenW)
    (by simpa [A,write] using h6) (by simpa [A,write] using h1)
    (ReturnOrigin.bits_nonblank s6) rfl rfl (by simpa [A,write] using hg)
  have he1 := clear_hoare B (3 : Fin 9) (by decide) (s3.map bitSymbol)
    (ReturnOrigin.bits_nonblank s3) (by simpa [A,B,write] using h3)
  let C1 := write B 3 (fun _ => blank)
  have he2 := clear_hoare C1 (4 : Fin 9) (by decide) (s4.map bitSymbol)
    (ReturnOrigin.bits_nonblank s4) (by simpa [A,B,C1,write] using h4)
  let C2 := write C1 4 (fun _ => blank)
  have he3 := clear_hoare C2 (5 : Fin 9) (by decide) (s5.map bitSymbol)
    (ReturnOrigin.bits_nonblank s5) (by simpa [A,B,C1,C2,write] using h5)
  let C3 := write C2 5 (fun _ => blank)
  have he4 := clear_hoare C3 (6 : Fin 9) (by decide) (s6.map bitSymbol)
    (ReturnOrigin.bits_nonblank s6) (by simpa [A,B,C1,C2,C3,write] using h6)
  let C4 := write C3 6 (fun _ => blank)
  have he5 := clear_hoare C4 (8 : Fin 9) (by decide) (s8.map bitSymbol)
    (ReturnOrigin.bits_nonblank s8) (by simpa [A,B,C1,C2,C3,C4,write] using h8)
  let C5 := write C4 8 (fun _ => blank)
  have hall := (((((ha.seq hb).seq he1).seq he2).seq he3).seq he4).seq he5
  refine hall.consequence (fun _ h => h) ?_ ?_
  · intro w hw
    rw [hw]
    change C5 = result v X s6
    unfold result
    rw [h0,h1,EqualWordReplace.overwrite f (v.head 0) (X.map bitSymbol)
      (oldV.map bitSymbol) (by simpa [X] using hlenV),
      EqualWordReplace.overwrite g (v.head 1) (s6.map bitSymbol)
        (oldW.map bitSymbol) (by simpa using hlenW)]
  · simp only [cost,List.length_map,X]
    omega

end
end IntegerMultBounds.Machine.CountedPackedRecycle
