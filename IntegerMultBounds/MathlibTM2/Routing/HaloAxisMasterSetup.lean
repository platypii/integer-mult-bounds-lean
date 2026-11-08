module

public import IntegerMultBounds.MathlibTM2.Routing.UnaryHeaderList
public import IntegerMultBounds.MathlibTM2.Routing.HaloPassHeaderSetup

/-! Read the ordinary axis dimensions and movement exponents from the same
metadata stream used by count production. Only width and zero are shared inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloAxisMasterSetup
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main HaloPassContext
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

def control : Fin 8 → Fin 117 := ![115,116,72,73,75,76,57,58]
def owned : List (Fin 117) := [44,45,55,65,47,54,43]
def entries (p : Parameters) : List (Fin 117 × ℕ) :=
  [(44,p.N),(45,p.B),(55,p.L),(65,p.H),(47,p.w),(54,p.k),(43,p.r)]

def packet (A : ℕ) (p : Parameters) := UnaryHeaderList.packet (A := A) p.V (entries p)
def run : Pr J 117 Q A U := UnaryHeaderList.load control owned
def cost (p : Parameters) := UnaryHeaderList.cost p.V (entries p)

def result (p : Parameters) (S : Stacks 117 A) (tail : List (Fin (A+4))) : Stacks 117 A :=
  {S with R := Function.update (UnaryHeaderList.install (entries p) S.R) 72 tail}

theorem result_holds (p : Parameters) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hV : (S.R 115).length = p.V) (hz : S.R 116 = []) : HaloPassHeaderSetup.Masters p (result p S tail) := by
  constructor <;> simp [result,UnaryHeaderList.install,entries,hV,hz]

theorem result_other (p : Parameters) (S : Stacks 117 A) (tail : List (Fin (A+4))) (j : Fin 117)
    (hj : j ∉ (72 : Fin 117)::owned) : (result p S tail).R j = S.R j := by
  simp only [List.mem_cons,not_or] at hj
  dsimp only [result]
  rw [Function.update_of_ne hj.1,UnaryHeaderList.install_off]
  simpa only [entries,List.map_cons,List.map_nil,owned] using hj.2

theorem run_native : mnNativePushBound 3 (run (J := J) (Q := Q) (A := A) (U := U)) :=
  UnaryHeaderList.load_native _ _

theorem run_exec (p : Parameters) (hfit : ∀ e ∈ entries p, e.2 < 2^p.V)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = p.V) (hz : S.R 116 = [])
    (hq : S.R 72 = packet A p++tail) (hb : ∀ j ∈ owned++[(73 : Fin 117),75,76,57,58], S.R j = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost p ∧
      Exec body run (mk v S) n (mk vf (result p S tail)) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*cost p)
        depth run (mk v S) n (mk vf (result p S tail))) := by
  have hports : (entries p).map Prod.fst = owned := by rfl
  have hsep : ∀ dst ∈ owned, ∀ j, dst ≠ control j := by decide +kernel
  obtain ⟨vf,n,hu,hn,he⟩ := UnaryHeaderList.load_exec (body := body) control (by decide +kernel) p.V (entries p)
    (by rw [hports]; decide) (by rw [hports]; exact hsep) hfit tail v S
    (by simpa [control] using hV) (by simpa [control] using hz) (by simpa [control,packet] using hq)
    (fun j hj => hb j (List.mem_append_left _ (hports ▸ hj))) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [control] <;> exact hb _ (by simp))
  have he' : Exec body run (mk v S) n (mk vf (result p S tail)) := by simpa [run,hports,control,result] using he
  refine ⟨vf,n,hu,hn,he',?_⟩
  intro depth
  exact mn_native_exec_within he' 3 run_native depth _ (by dsimp [cost]; omega)

end IntegerMultBounds.MathlibTM2.Routing.HaloAxisMasterSetup
