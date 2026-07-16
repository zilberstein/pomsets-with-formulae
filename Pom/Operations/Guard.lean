import Pom.Lpo.Operations.Guard
import Pom.Lpo.Operations.Par.FinApprox
import Pom.Operations.Par
import Pom.Order.Extension
import Pom.Order.FinApprox

namespace Pom

variable {l : Type} [Bot l]

lemma exists_guard {ℓ : l} (h : ℓ ≠ ⊥) (α β : Lpo l) :
    ∃ (γ : Lpo l) (i : ParLpoIsomorphism α β),
      γ = Lpo.guard i.hx i.hx' i.hdisj h := by
  have ⟨i⟩ := exists_isomorphic_lpos α β
  exact ⟨_, i, rfl⟩

noncomputable def guard {ℓ : l} (h : ℓ ≠ ⊥) : Pom l → Pom l → Pom l :=
  Quotient.map₂ (fun α β ↦ (exists_guard h α β).choose) <| by
    intro α₁ α₂ hα β₁ β₂ hβ
    have h₁ := (exists_guard h α₁ β₁).choose_spec
    have h₂ := (exists_guard h α₂ β₂).choose_spec
    rw [h₁.choose_spec, h₂.choose_spec]
    refine Lpo.guard_isomorphic ?_ ?_
    · exact Setoid.trans (Setoid.symm h₁.choose.hα) <| Setoid.trans hα h₂.choose.hα
    · exact Setoid.trans (Setoid.symm h₁.choose.hβ) <| Setoid.trans hβ h₂.choose.hβ

lemma mem_guard {p q : Pom l} {α β : Lpo l}
    {x : Node} {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes} {hd : Disjoint α.nodes β.nodes}
    {ℓ : l} (h : ℓ ≠ ⊥)
    (h₁ : α ∈ p) (h₂ : β ∈ q) :
    Lpo.guard hx hx' hd h ∈ guard h p q := by
  rcases h₁ with rfl; rcases h₂ with rfl
  conv => lhs; exact Quotient.map₂_mk _ _ _ _
  have h := (exists_guard h α β).choose_spec
  rw [h.choose_spec]
  refine Quotient.eq_iff_equiv.mpr (Lpo.guard_isomorphic ?_ ?_)
  · symm; exact h.choose.hα
  · symm; exact h.choose.hβ

lemma exists_rep_guard {ℓ : l} (h : ℓ ≠ ⊥) (p q : Pom l) :
    ∃ (α β : Lpo l) (x : Node) (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes)
      (hd : Disjoint α.nodes β.nodes),
      α ∈ p ∧ β ∈ q ∧ Lpo.guard hx hx' hd h ∈ guard h p q := by
  obtain ⟨α, rfl⟩ := p.exists_rep
  obtain ⟨β, rfl⟩ := q.exists_rep
  have ⟨i, heq⟩ := (exists_guard h α β).choose_spec
  refine ⟨i.α', i.β', i.root, i.hx, i.hx', i.hdisj, ?_, ?_, ?_⟩
  · exact Quotient.eq_iff_equiv.mpr i.hα
  · exact Quotient.eq_iff_equiv.mpr i.hβ
  · rw [← heq]; exact Quotient.map₂_mk _ _ _ _

lemma guard_monotone {l : Type} [PartialOrder l] [OrderBot l] {ℓ ℓ' : l} (hℓ : ℓ ≠ ⊥)
    {p p' q q' : Pom l} (hle : ℓ ≤ ℓ') (hle₁ : p ≤ p') (hle₂ : q ≤ q') :
    guard hℓ p q ≤ guard (ne_bot_of_le_ne_bot hℓ hle) p' q' := by
  obtain ⟨α', β', x, hx, hx', hd, rfl, rfl, hmem⟩ := exists_rep_guard _ p' q'
  have ⟨α, hα, hle₁⟩ := ge_lpo hle₁
  have ⟨β, hβ, hle₂⟩ := ge_lpo hle₂
  refine ⟨Lpo.guard (α := α) (β := β) (x := x) ?_ ?_ ?_ hℓ, ?_, _, hmem, ?_⟩
  · intro hc; apply hx; exact hle₁.nodes hc
  · intro hc; apply hx'; exact hle₂.nodes hc
  · exact hd.mono hle₁.nodes hle₂.nodes
  · refine mem_guard hℓ hα hβ
  · exact Lpo.guard_monotone hle hle₁ hle₂

open OmegaCompletePartialOrder

lemma guard_eq_ext {l : Type} [DCPO l] [OrderBot l] [ScottCompact l]
    {ℓ : l} (h : ℓ ≠ ⊥) :
    guard h = ext₂ (fun p q ↦ guard h p.to_pom q.to_pom) (guard_monotone h (le_refl _)) := by
  ext p q
  unfold ext₂; refine le_antisymm ?_ ?_
  · refine pom_ge_iff_ge_fin fun n ↦ ?_
    cases n with
    | zero => exact le_of_eq_of_le (trunc_0 _) bot_le
    | succ n =>
      obtain ⟨α, β, x, hx, hx', hd, rfl, rfl, hmem⟩ := exists_rep_guard h p q
      rw [hmem]
      unfold trunc Pomfin.to_pom
      conv => lhs; arg 3; exact Quotient.lift_mk _ _ _
      conv => lhs; exact Quotient.map_mk _ _ _
      refine le_of_eq_of_le ?_ (le_ωSup _ n)
      conv => lhs; arg 2; exact Lpo.par_trunc n
      simp only [DFunLike.coe]
      symm; refine mem_guard h ?_ ?_ <;> {
        conv => lhs; arg 3; exact Quotient.lift_mk _ _ _
        exact Quotient.map_mk _ _ _
      }
  · refine ωSup_le _ _ fun n ↦ guard_monotone h (le_refl _) ?_ ?_ <;>
    exact Pom.trunc_le _ n

lemma guard_continuous {l : Type} [DCPO l] [OrderBot l] [ScottCompact l]
    {ℓ : l} (h : ℓ ≠ ⊥) (c₁ c₂ : Chain (Pom l)) :
    guard h (ωSup c₁) (ωSup c₂) = ωSup {
      toFun n := guard h (c₁ n) (c₂ n)
      monotone' _ _ hle := guard_monotone h (le_refl _) (c₁.monotone' hle) (c₂.monotone' hle)
    } :=
  continuous_of_eq_ext₂ (guard_monotone h (le_refl _)) (guard_eq_ext h) c₁ c₂

end Pom
