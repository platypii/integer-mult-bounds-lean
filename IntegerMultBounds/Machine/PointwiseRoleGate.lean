import IntegerMultBounds.Machine.PointwiseBinaryNormalized
import IntegerMultBounds.Machine.InjectivePlacement

/-! A fixed source/destination pointwise gate placed into a role bank. Every
role retains its head, all spectators remain exact, and a single descriptor
and work clock are shared across all gates. -/
namespace IntegerMultBounds.Machine.PointwiseRoleGate
variable {t a n : ℕ}
noncomputable section

structure Gate (t : ℕ) where
  src : Fin t
  dst : Fin t
  distinct : src ≠ dst

def Gate.slots (g : Gate t) : Fin 4 → Fin (t+2) :=
  ![Fin.castAdd 2 g.src,Fin.castAdd 2 g.dst,Fin.natAdd t 0,Fin.natAdd t 1]

theorem Gate.slots_injective (g : Gate t) : Function.Injective g.slots := by
  intro i j h
  have hsd : g.src.val ≠ g.dst.val := fun h => g.distinct (Fin.ext h)
  have hs := g.src.isLt
  have hd := g.dst.isLt
  fin_cases i <;> fin_cases j <;> simp_all [Gate.slots,Fin.ext_iff] <;> omega

def Gate.placement (g : Gate t) : Fin (4+((t+2)-4)) ≃ Fin (t+2) :=
  InjectivePlacement.placement g.slots g.slots_injective
    (by have hs := g.src.isLt; have hd := g.dst.isLt
        have hne : g.src.val ≠ g.dst.val := fun h => g.distinct (Fin.ext h)
        omega)

@[simp] theorem Gate.placement_active (g : Gate t) (i : Fin 4) :
    g.placement (Fin.castAdd ((t+2)-4) i) = g.slots i :=
  InjectivePlacement.active_slot _ _ _ _

def program (g : Gate t) (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) :=
  Placement.placed (PointwiseBinaryNormalized.program op) g.placement

def bank (background : Fin t → ℤ → Fin (a+4)) (origins : Fin t → ℤ)
    (data : Fin t → Fin n → Fin (a+4)) (bs : List Bool) : Tapes (t+2) a :=
  (⟨origins,fun j => putWord (background j) (origins j) (List.ofFn (data j))⟩ : Tapes t a).append
    (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1)

def applyGate (g : Gate t) (op : Fin (a+4) → Fin (a+4) → Fin (a+4))
    (data : Fin t → Fin n → Fin (a+4)) : Fin t → Fin n → Fin (a+4) :=
  Function.update data g.dst (fun i => op (data g.src i) (data g.dst i))

theorem active_bank (g : Gate t) (background : Fin t → ℤ → Fin (a+4)) (origins : Fin t → ℤ)
    (data : Fin t → Fin n → Fin (a+4)) (bs : List Bool) :
    Placement.active g.placement (bank background origins data bs) =
      PointwiseBinaryNormalized.bank
        (PointwiseBinaryNormalized.pair (background g.src) (background g.dst)
          (origins g.src) (origins g.dst) (data g.src) (data g.dst)) bs := by
  unfold Placement.active
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [Gate.placement_active,Gate.slots,bank,
      PointwiseBinaryNormalized.pair,StackPop.bank,
      CountedLoopReuseAlphabet.controls,Tapes.append,Fin.addCases]

private theorem extra_ne_dst (g : Gate t) (i : Fin ((t+2)-4)) :
    g.placement (Fin.natAdd 4 i) ≠ Fin.castAdd 2 g.dst := by
  have he : g.placement (Fin.castAdd ((t+2)-4) (1 : Fin 4)) = Fin.castAdd 2 g.dst := by
    simp [Gate.slots]
  intro h
  have hv := congrArg Fin.val (g.placement.injective (h.trans he.symm))
  simp only [Fin.val_natAdd,Fin.val_castAdd,Fin.val_one] at hv
  omega

private theorem bank_frame (g : Gate t) (op : Fin (a+4) → Fin (a+4) → Fin (a+4))
    (background : Fin t → ℤ → Fin (a+4)) (origins : Fin t → ℤ)
    (data : Fin t → Fin n → Fin (a+4)) (bs : List Bool) :
    Placement.extra g.placement (bank background origins (applyGate g op data) bs) =
      Placement.extra g.placement (bank background origins data bs) := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    have hn := extra_ne_dst g i
    generalize he : g.placement (Fin.natAdd 4 i) = k at hn ⊢
    change (bank background origins (applyGate g op data) bs).tape k =
      (bank background origins data bs).tape k
    induction k using Fin.addCases with
    | left k =>
      have hk : k ≠ g.dst := by intro h; subst k; exact hn rfl
      simp [bank,Tapes.append,applyGate,hk]
    | right k => simp [bank,Tapes.append]

/-- One actual gate on arbitrary fixed role slots. Only the destination word
changes; all heads, every spectator word, and both count controls are exact. -/
theorem gate_hoare (g : Gate t) (op : Fin (a+4) → Fin (a+4) → Fin (a+4))
    (background : Fin t → ℤ → Fin (a+4)) (origins : Fin t → ℤ)
    (data : Fin t → Fin n → Fin (a+4)) (bs : List Bool) (hn : Counter.value bs = n) :
    HoareTime (program g op) (fun w => w = bank background origins data bs)
      (fun w => w = bank background origins (applyGate g op data) bs) (14*n+14*bs.length+33) := by
  have hh := Placement.hoare_at (PointwiseBinaryNormalized.array_hoare op
    (background g.src) (background g.dst) (origins g.src) (origins g.dst)
    (data g.src) (data g.dst) bs hn) g.placement (bank background origins data bs)
    (active_bank g background origins data bs)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  have ha := active_bank g background origins (applyGate g op data) bs
  simp only [applyGate,Function.update_of_ne g.distinct,Function.update_self] at ha
  rw [Placement.replace,← ha,← bank_frame g op background origins data bs]
  exact Placement.view _ _

end
end IntegerMultBounds.Machine.PointwiseRoleGate
