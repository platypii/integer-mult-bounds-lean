import IntegerMultBounds.Machine.WordBankCleanup
import IntegerMultBounds.Machine.ActiveTargetRotation

/-! Physically return a repaired full-width array to its original caller tape,
erase the separate raw output, and restore both heads with a linear cost. -/
namespace IntegerMultBounds.Machine.ActiveRepairArrayRecycle
noncomputable section
open WordBankCleanup
variable {t a m : ℕ}

def program (src dst : Fin t) (hne : src≠dst) (ht : 2≤t) (a : ℕ) :=
  seq (replaceProgram src dst hne ht a) (clearProgram src (by omega) a)

def result (v : Tapes t a) (src dst : Fin t) (y : Fin m → Bool) :=
  write (write v dst (ActiveTargetRotation.word y)) src (fun _ => blank)

theorem word_eq (x : Fin m → Bool) :
    ActiveTargetRotation.word (a:=a) x=
      putWord (fun _ => blank) 0 ((List.ofFn x).map bitSymbol) := by
  rw [List.map_ofFn]
  rfl

theorem runs (v : Tapes t a) (src dst : Fin t) (hne : src≠dst) (ht : 2≤t)
    (x y : Fin m → Bool)
    (hs : v.tape src=ActiveTargetRotation.word y) (hd : v.tape dst=ActiveTargetRotation.word x)
    (hsh : v.head src=0) (hdh : v.head dst=0) :
    HoareTime (program src dst hne ht a) (fun w => w=v)
      (fun w => w=result v src dst y) (5*m+10) := by
  let xs := (List.ofFn y).map (bitSymbol (a:=a))
  let ys := (List.ofFn x).map (bitSymbol (a:=a))
  have hx : ∀ z∈xs,z≠blank := ReturnOrigin.bits_nonblank _
  have hlen : xs.length=ys.length := by simp [xs,ys]
  have hh := replace_hoare v src dst hne ht (fun _ => blank) (fun _ => blank)
    xs ys hlen (by rw [hs,word_eq,hsh]) (by rw [hd,word_eq,hdh]) hx rfl rfl rfl
  have hmid : write v dst (putWord (fun _ => blank) (v.head dst) xs)=
      write v dst (ActiveTargetRotation.word y) := by rw [hdh,word_eq]
  rw [hmid] at hh
  have hc := clear_hoare (write v dst (ActiveTargetRotation.word y)) src (by omega) xs hx (by
    simp only [write,Function.update_of_ne hne,hsh]
    rw [hs,word_eq])
  exact (hh.seq hc).consequence (fun _ h => h) (fun _ h => h)
    (by simp [xs]; omega)

theorem source_blank (v : Tapes t a) (src dst : Fin t) (y : Fin m → Bool) :
    (result v src dst y).tape src=fun _ => blank := by simp [result,write]

theorem destination (v : Tapes t a) (src dst : Fin t) (hne : src≠dst) (y : Fin m → Bool) :
    (result v src dst y).tape dst=ActiveTargetRotation.word y := by
  simp [result,write,Ne.symm hne]

theorem heads (v : Tapes t a) (src dst : Fin t) (y : Fin m → Bool) :
    (result v src dst y).head=v.head := rfl

theorem frame (v : Tapes t a) (src dst : Fin t) (y : Fin m → Bool)
    (i : Fin t) (hs : i≠src) (hd : i≠dst) :
    (result v src dst y).tape i=v.tape i := by simp [result,write,hs,hd]

end
end IntegerMultBounds.Machine.ActiveRepairArrayRecycle
