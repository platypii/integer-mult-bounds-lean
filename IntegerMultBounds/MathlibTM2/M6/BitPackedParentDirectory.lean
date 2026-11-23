module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedReturnFields
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Load the packed return directory from a parent archive with an arbitrary suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Node Mult.ShortConv
open Shared50ModularControl (prime)

private theorem directoryLength {A d : ℕ} (width : ℕ) (values : Fin d → ℕ) :
    (List.ofFn fun i => binSyms (A := A) width (values i)).flatten.length = d*width := by
  simp [List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const]

/-- Read exactly the parent coefficients, using the binary modulus as a width clock. -/
theorem loadParentDirectory {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 6 ↪ Fin T) :
    ∃ code : Pr P T Q prime U, ∀ w (parent : Fin 64 → ZMod (prime^(w+1))) tail u S,
      let M := prime^(w+1)
      let dir : List (Fin (prime+4)) := (List.ofFn fun j => binSyms M.size (parent j).val).flatten
      S.R (r 0) = binSyms M.size M → S.R (r 1) = dir ++ tail →
      (∀ i : Fin 6, 2 ≤ i.val → S.R (r i) = []) →
      ∃ z, z.user = u.user ∧ Exec body code (mk u S) (772*M.size+16)
        (mk z {S with R := Function.update S.R (r 2) dir}) := by
  refine ⟨(umul 64 (r 0) (r 3) (r 5)).seq ((copyPrefix (r 3) (r 1) (r 2) (r 4) (r 5)).seq (uclear (r 3))),?_⟩
  intro w parent tail u S M dir modulus archive free
  have len : dir.length = 64*M.size := directoryLength _ _
  obtain ⟨v,same,prepare⟩ := umul_exec body 64 (a := r 0) (b := r 3) (t := r 5)
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide)) u S (free 5 (by decide))
  rw [modulus,length_binSyms,free 3 (by decide),List.append_nil] at prepare
  let D := {S with R := Function.update S.R (r 3) (List.replicate (64*M.size) tick)}
  obtain ⟨y,user,read⟩ := copyPrefix_exec (body := body) (count := r 3) (src := r 1)
    (dst := r 2) (saved := r 4) (tmp := r 5) (by simp [List.nodup_cons,r.injective.eq_iff])
    v D dir tail (by simpa [D,r.injective.eq_iff] using archive) (by simp [D,len])
    (by simpa [D,r.injective.eq_iff] using free 4 (by decide)) (by simpa [D,r.injective.eq_iff] using free 5 (by decide))
  have empty : D.R (r 2) = [] := by simpa [D,r.injective.eq_iff] using free 2 (by decide)
  rw [empty,List.append_nil] at read
  let E := {D with R := Function.update D.R (r 2) dir}
  obtain ⟨z,last,clear⟩ := uclear_exec body (r 3) y E
  have clock : (E.R (r 3)).length = 64*M.size := by simp [E,D,r.injective.eq_iff]
  rw [clock] at clear
  refine ⟨z,last.trans (user.trans same),(prepare.seq (read.seq clear)).cast (by rw [len]; omega) ?_⟩
  congr 1
  refine Stacks.ext rfl rfl rfl ?_
  change Function.update (Function.update (Function.update S.R (r 3) _) (r 2) dir) (r 3) [] = _
  rw [Function.update_comm (r.injective.ne (by decide : (2 : Fin 6) ≠ 3)),Function.update_idem,
    ← free 3 (by decide),Function.update_eq_self]

open M8.RevMachine in
/-- Execute the descriptor-seeded stage directly from a parent archive prefix. -/
theorem runWithParentArchive {T N Q V : ℕ} {P A U : Type}
    (body : P → Pr P N Q prime U) (host : A → Pr A (T+273) Q prime U)
    (stage : Fin N ↪ Fin T) (label : P → A)
    (installed : ∀ p, host (label p) = embProg (stage.trans (Fin.castAddEmb 273)) label (body p))
    (bank : Fin SweepFile.tapes ↪ Fin N) (src dst : Fin (142081+2) ↪ Fin N)
    (liveOff : ∀ i j, bank i ≠ src j)
    (reg : Fin 8 ↪ Fin T) (saved : Fin T)
    (apart : ∀ i j, stage i ≠ reg j) (saveOff : ∀ i, saved ≠ reg i)
    (saveBank : ∀ i, stage (bank i) ≠ saved) (scratch : Fin 4 ↪ Fin T)
    (scratchOff : ∀ i j, scratch i ≠ reg j) (hdr : Fin 6 → Fin T) (regs : Fin 35 ↪ Fin T)
    (dirPorts : Fin 6 ↪ Fin T) (radixPort : dirPorts 0 = regs 2) (outputPort : dirPorts 2 = reg 4)
    (descriptorOff : ∀ i, hdr i ≠ reg 4) (regsOff : ∀ i, regs i ≠ reg 4)
    (piece : Pr P N Q prime U) :
    let low := Fin.castAddEmb 273 (n := T)
    let place := stage.trans low
    ∃ code : Pr A (T+273) Q prime U, ∀ (v : RecursiveInterchangeLayout.Descriptor) w
      (parent : Fin 64 → ZMod (prime^(w+1))) (seed : Stacks N prime) price effect,
      let M := prime^(w+1)
      let W := v.beforeH*(v.beforeRows*v.rows*v.between*v.afterD)
      v.Positive → seed.R ∘ bank = returnSeed w (128*M.size) W 1 parent →
      PackedPieceHandoff V effect body piece src dst seed price →
      ∀ x u S, ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk place S) →
      (∀ j, (∀ i, src i ≠ j) → S.L (place j) = seed.L j ∧
        ((∀ i, bank i ≠ j) → S.R (place j) = seed.R j)) →
      S.R (low (regs 2)) = binSyms M.size M → S.R (low (regs 28)) = binSyms 1 1 →
      (S.R (low (regs 33))).length = w →
      (∀ i, S.R (low (hdr i)) = (Routines.hdr v i).map bitSymbol) →
      (∀ j : Fin 273, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      (∃ tail, S.R (low (dirPorts 1)) = (List.ofFn fun j => binSyms M.size (parent j).val).flatten ++ tail) →
      (∀ i : Fin 6, 2 ≤ i.val → S.R (low (dirPorts i)) = []) →
      (∀ i, S.R (low (reg (fieldSlot i))) = []) → (∀ i, S.R (low (scratch i)) = []) →
      (∀ i, S.R (place (bank i)) = []) → S.R (low (reg 1)) = [] → S.R (low (reg 2)) = [] →
      S.R (low (reg 7)) = [] → S.R (low saved) = [] →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ t ≤ 152403531*(M^128*W)+price ∧
        z.user = u.user ∧ ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk place F) ∧ effect x y := by
  intro low place
  obtain ⟨load,prepare⟩ := loadParentDirectory host (dirPorts.trans low)
  obtain ⟨call,run⟩ := runWithDescriptorReturnFields body host stage label installed bank src dst liveOff
    reg saved apart saveOff saveBank scratch scratchOff hdr regs piece
  refine ⟨load.seq call,?_⟩
  intro v w parent seed price effect M W pos seedBank pieceRun x u S words privateTapes base unit clock descriptor fresh archive free slots aux blank hh hu ht hs
  obtain ⟨tail,archive⟩ := archive
  obtain ⟨y,user,setup⟩ := prepare w parent tail u S (by simpa only [Function.Embedding.trans_apply,radixPort] using base) archive free
  let dir : List (Fin (prime+4)) := (List.ofFn fun j => binSyms M.size (parent j).val).flatten
  let D := {S with R := Function.update S.R (low (reg 4)) dir}
  rw [show (dirPorts.trans low) 2 = low (reg 4) from congrArg low outputPort] at setup
  have keep (j : Fin T) (off : j ≠ reg 4) : D.R (low j) = S.R (low j) :=
    Function.update_of_ne (low.injective.ne off) ..
  have stageR j := keep (stage j) (apart j 4)
  have project : embStk place D = embStk place S := by
    unfold embStk
    congr 1
    exact funext stageR
  have unused (j : Fin 273) : j.natAdd T ≠ low (reg 4) := by
    intro eq
    have h := congrArg Fin.val eq
    change T+j.val = (reg 4).val at h
    omega
  obtain ⟨z,F,b,out,exec,paid,same,result,action⟩ := run v w parent seed price effect pos seedBank pieceRun x y D
    (project ▸ words) (fun j away => ⟨(privateTapes j away).1,fun h => (stageR j).trans ((privateTapes j away).2 h)⟩)
    ((keep _ (regsOff 2)).trans base) ((keep _ (regsOff 28)).trans unit)
    ((congrArg List.length (keep _ (regsOff 33))).trans clock)
    (fun i => (keep _ (descriptorOff i)).trans (descriptor i))
    (fun j => ⟨(fresh j).1,(Function.update_of_ne (unused j) ..).trans (fresh j).2⟩) (Function.update_self ..)
    (fun i => (keep _ (reg.injective.ne (by fin_cases i <;> decide))).trans (slots i))
    (fun i => (keep _ (scratchOff i 4)).trans (aux i)) (fun i => (stageR _).trans (blank i))
    ((keep _ (reg.injective.ne (by decide))).trans hh) ((keep _ (reg.injective.ne (by decide))).trans hu)
    ((keep _ (reg.injective.ne (by decide))).trans ht) ((keep _ (saveOff 4)).trans hs)
  refine ⟨z,F,_,out,setup.seq exec,?_,same.trans user,result,action⟩
  have wp : 0 < W := Nat.mul_pos pos.2.2.1 (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pos.1 pos.2.1) pos.2.2.2.1) pos.2.2.2.2)
  have volume : M ≤ M^128*W := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans (Nat.le_mul_of_pos_right _ wp)
  have digits : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have mp : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  change b ≤ 152402743*(M^128*W)+price at paid
  change 772*M.size+16+b ≤ _
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
