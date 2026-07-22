import Pom.Linearization
import Pom.Operations.Guard

open Linearization

namespace Lpofin

noncomputable def guard {l : Type} [Bot l] {x : Node} {ℓ : l} {α β : Lpofin l}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes)
    (hroot : ℓ ≠ ⊥) : Lpofin l :=
  ⟨Lpo.guard hx hx' hd hroot,
    Set.finite_insert.mpr (Set.finite_union.mpr ⟨α.property, β.property⟩)⟩

lemma lin_guard {t : Type → Type} {X act test : Type}
    [Linearizable t X]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [Sem act X (t X)]
    [DCPO test] [Sem test X (t Bool)]
    {α β : Lpofin (Label act test)} {b : test}
    {x : Node} {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes}
    {hd : Disjoint α.nodes β.nodes} :
    (lin (Lpofin.guard hx hx' hd (Label.test_ne_bot b)) : X → t X) =
    fun σ ↦ Sem.sem b σ >>= fun r ↦ bif r then α.lin σ else β.lin σ := by sorry

lemma guard_trunc {l : Type} [Preorder l] [OrderBot l] {x : Node} {ℓ : l} {α β : Lpo l}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes} {hd : Disjoint α.nodes β.nodes}
    {hroot : ℓ ≠ ⊥}
    (n : ℕ) :
    (Lpo.guard hx hx' hd hroot).trunc (n + 1) =
    Lpofin.guard
      (fun h ↦ hx <| (α.trunc_le n).nodes h)
      (fun h ↦ hx' <| (β.trunc_le n).nodes h)
      (hd.mono (α.trunc_le n).nodes (β.trunc_le n).nodes)
      hroot := Subtype.ext <| Lpo.par_trunc n

end Lpofin

section DomainTheory

-- A few lemmas to add to the domain theory library

namespace OmegaCompletePartialOrder
namespace Chain

def shift {X : Type} [Preorder X] (c : Chain X) : Chain X := {
  toFun n := c (n + 1)
  monotone' _ _ hle := c.monotone' <| add_le_add hle (le_refl _)
}

lemma ωSup_shift {X : Type} [OmegaCompletePartialOrder X] (c : Chain X) :
    ωSup c = ωSup c.shift := by
  refine le_antisymm ?_ ?_
  · refine ωSup_le _ _ ?_; intro i
    refine le_trans ?_ (le_ωSup _ i)
    exact c.monotone' <| Nat.le_succ _
  · refine ωSup_le _ _ ?_; intro i
    exact le_ωSup _ (i + 1)

def const {X : Type} [Preorder X] (x : X) : Chain X := {
  toFun _ := x
  monotone' _ _ _ := le_refl _
}

lemma ωSup_const {X : Type} [OmegaCompletePartialOrder X] (x : X) :
    ωSup (const x) = x := by
  refine le_antisymm ?_ ?_
  · refine ωSup_le _ _ ?_; intro n; exact le_refl _
  · exact le_ωSup (const x) 0

end Chain
end OmegaCompletePartialOrder

open OmegaCompletePartialOrder

lemma ωSup_apply {X Y : Type} [OmegaCompletePartialOrder Y] (c : Chain (X → Y)) (x : X) :
    ωSup c x = ωSup {
      toFun n := c n x
      monotone' _ _ hle := c.monotone' hle x
    } := rfl

end DomainTheory

namespace Pom
open OmegaCompletePartialOrder

lemma lin_guard {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [ScottCompact act] [Sem act s (t s)]
    [DCPO test] [ScottCompact test] [Sem test s (t Bool)]
    (p q : Pom (Label act test)) (b : test) :
    (lin (guard (Label.test_ne_bot b) p q) : s → t s) =
    fun σ ↦ Sem.sem b σ >>= fun r ↦ bif r then lin p σ else lin q σ := by
  obtain ⟨α, β, x, hx, hx', hd, rfl, rfl, hmem⟩ := exists_rep_guard (Label.test_ne_bot b) p q
  rw [guard_mk hx hx' hd, lin_mk]
  rw [Chain.ωSup_shift]; simp only [Chain.shift, DFunLike.coe]
  conv => lhs; arg 1; arg 1; arg 1; ext n; arg 1; exact Lpofin.guard_trunc _
  conv => lhs; arg 1; arg 1; arg 1; ext n; exact Lpofin.lin_guard
  ext σ; rw [ωSup_apply]; simp only [DFunLike.coe]
  let c : Chain (Bool → t s) := {
    toFun n r := bif r then (α.trunc n).lin σ else (β.trunc n).lin σ
    monotone' _ _ hle r := by
      cases r <;> simp only [cond_true, cond_false] <;>
        exact Lpofin.lin_mono (Lpo.trunc_mono (le_refl _) hle) _
  }
  conv =>
    lhs; exact (ContinuousMonad.bind_continuous (c₁ := Chain.const (Sem.sem b σ)) (c₂ := c)).symm
  refine congrArg₂ _ (Chain.ωSup_const _) ?_
  ext r; rw [ωSup_apply]; simp only [c, DFunLike.coe]
  cases r <;> (simp only [cond_true, cond_false]; symm; exact congrFun (lin_mk _) _)

end Pom
