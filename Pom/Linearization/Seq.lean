import DomainTheory.OmegaCompletePartialOrder.Instances

import Pom.Linearization
import Pom.Lpo.Linearization.Seq
import Pom.Operations.Seq

open Linearization

namespace Pomfin

lemma lin_seq {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [PartialOrder act] [Sem act s (t s)]
    [PartialOrder test] [Sem test s (t Bool)]
    (p q : Pomfin (Label act test)) :
    (lin t s _ _ (seq p q) : s → t s) = fun σ ↦ lin _ _ _ _ p σ >>= lin _ _ _ _ q := by
  obtain ⟨α, β, f, rfl, rfl, heq⟩ := exists_rep_seq p q
  rw [heq, lin_mk, Lpofin.lin_seq]; ext σ
  refine congrArg₂ _ ?_ ?_ <;> symm
  · exact congrFun (lin_mk _) σ
  · exact lin_mk _

end Pomfin

namespace Pom

open OmegaCompletePartialOrder

theorem lin_seq {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [ScottCompact act] [Sem act s (t s)]
    [DCPO test] [ScottCompact test] [Sem test s (t Bool)]
    (p q : Pom (Label act test)) :
    (lin (seq p q) : s → t s) = fun σ ↦ lin p σ >>= lin q := by
  ext σ; unfold seq
  conv => lhs; exact congrFun ((lin_continuous (act := act) (test := test)).map_ωSup _) _
  simp only [ωSup_apply, Chain.coe_map, OrderHom.coe_mk, Function.comp_apply]
  simp only [DFunLike.coe, lin_eq_fin, Pomfin.lin_seq]
  let c₁ : Chain (t s) := {
    toFun n := Pomfin.lin t s act test (p.trunc n) σ
    monotone' _ _ hle := (Pomfin.lin_monotone t s act test <| trunc_mono (le_refl p) hle) σ
  }
  let c₂ : Chain (s → t s) := {
    toFun n := Pomfin.lin t s act test (q.trunc n)
    monotone' _ _ hle := Pomfin.lin_monotone t s act test <| trunc_mono (le_refl q) hle
  }
  conv => lhs; exact (ContinuousMonad.bind_continuous (c₁ := c₁) (c₂ := c₂)).symm
  rfl

end Pom
