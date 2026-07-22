import Pom.Linearization.Guard
import Pom.Linearization.Seq

namespace Pom

open Linearization

variable {t st} [Linearizable t st]
  [∀ β, OmegaCompletePartialOrder (t β)] [∀ β, OrderBot (t β)]
variable {act test : Type}
  [DCPO act] [ScottCompact act] [Sem act st (t st)]
  [DCPO test] [ScottCompact test] [Sem test st (t Bool)]

def skip : Pom (Label act test) := Pom.singleton Label.fork

noncomputable def if_stmt (b : test) (p q : Pom (Label act test)) : Pom (Label act test) :=
  guard (Label.test_ne_bot b) p q

-- The characteristic function of a while loop
noncomputable def while_body (b : test) (p κ : Pom (Label act test)) : Pom (Label act test) :=
  if_stmt b (seq p κ) skip

lemma while_body_monotone (b : test) (p : Pom (Label act test)) : Monotone (while_body b p) := by
  intro _ _ hle; unfold while_body
  refine guard_monotone _ (le_refl _) ?_ (le_refl _)
  exact seq_monotone (le_refl _) hle

open OmegaCompletePartialOrder

lemma while_body_continuous (b : test) (p : Pom (Label act test)) : ωScottContinuous (while_body b p) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨while_body_monotone b p, ?_⟩
  intro c; unfold while_body;
  conv in skip => exact (Chain.ωSup_const _).symm
  conv => lhs; exact guard_continuous _ _ _
  simp only [DFunLike.coe, Chain.map, OrderHom.comp, Chain.const, Function.comp]
  sorry

def lfp {X : Type} [OmegaCompletePartialOrder X] [OrderBot X] (f : X → X) (hf : Monotone f) : X :=
  ωSup <| fixedPoints.iterateChain ⟨f, hf⟩ ⊥ bot_le

noncomputable def while_loop (b : test) (p : Pom (Label act test)) : Pom (Label act test) :=
  lfp _ (while_body_monotone b p)

theorem lin_if_stmt (b : test) (p q : Pom (Label act test)) :
    (lin (if_stmt b p q) : st → t st) =
    fun σ ↦ Sem.sem b σ >>= fun r ↦ bif r then lin p σ else lin q σ :=
  lin_guard _ _ _

theorem lin_skip : @lin t st act test _ _ _ _ _ _ _ skip = Pure.pure := by sorry

def while_sem (b : test) (f κ : st → t st) : st → t st :=
  fun σ ↦ Sem.sem b σ >>= fun r ↦ bif r then f σ >>= κ else pure σ

lemma while_sem_monotone (b : test) (f : st → t st) : Monotone (while_sem b f) := by
  intro κ₁ κ₂ hle σ; refine ContinuousMonad.bind_mono (le_refl _) ?_
  rintro (_ | _)
  · exact le_refl _
  · refine ContinuousMonad.bind_mono (le_refl _) hle

lemma lin_while_body (b : test) (p : Pom (Label act test)) (n : ℕ) :
    (((while_body b p)^[n] ⊥).lin : st → t st) = (while_sem b p.lin)^[n] ⊥ := by
  induction n with
  | zero => sorry -- lin ⊥ = ⊥
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    rw [Function.iterate_succ', Function.comp_apply]
    conv => lhs; exact lin_if_stmt _ _ _
    ext σ; refine congrArg₂ Bind.bind rfl ?_
    ext r; cases r
    · exact congrFun lin_skip _
    · exact (congrFun (lin_seq _ _) σ).trans <| congrArg₂ Bind.bind rfl ih

theorem lin_while (b : test) (p : Pom (Label act test)) :
    (lin (while_loop b p) : st → t st) = lfp _ (while_sem_monotone b (lin p)) := by
  unfold while_loop
  conv => lhs; exact lin_continuous.map_ωSup _
  simp only [Chain.map, OrderHom.comp, OrderHom.coe_mk, Chain.coe_toOrderHom]
  refine congrArg ωSup ?_
  ext n σ
  unfold fixedPoints.iterateChain; simp only [DFunLike.coe, Function.comp_apply]
  exact congrFun (lin_while_body _ _ _) _

end Pom
