import Pom.Order
import Pom.Lpo.Operations.Par
import Pom.Lpo.Operations.Par.Isomorphism
import Pom.Lpo.Operations.Par.Order

namespace Pom

variable {l : Type} [Bot l]

structure ParLpoIsomorphism (α β : Lpo l) where
  root : Node
  α' : Lpo l
  β' : Lpo l
  hα : α ≈ α'
  hβ : β ≈ β'
  hx : root ∉ α'.nodes
  hx' : root ∉ β'.nodes
  hdisj : Disjoint α'.nodes β'.nodes

lemma exists_isomorphic_lpos (α β : Lpo l) : Nonempty (ParLpoIsomorphism α β) := by
  have ⟨f, hf⟩ := Countable.exists_injective_nat (Option (α.nodes ⊕ β.nodes))
  have e := Equiv.ofInjective (f : _ → Node) hf
  refine ⟨{
    root := (e none).val
    α' := α.permute <| Equiv.ofInjective (Subtype.val ∘ e ∘ some ∘ Sum.inl) ?_
    β' := β.permute <| Equiv.ofInjective (Subtype.val ∘ e ∘ some ∘ Sum.inr) ?_
    hα := ⟨_, rfl⟩
    hβ := ⟨_, rfl⟩
    hx := ?_, hx' := ?_, hdisj := ?_
  }⟩
  · exact Subtype.val_injective.comp <| e.injective.comp <| (Option.some_injective _).comp <|
      Sum.inl_injective
  · exact Subtype.val_injective.comp <| e.injective.comp <| (Option.some_injective _).comp <|
      Sum.inr_injective
  · intro hc; have ⟨z, heq⟩ := Set.mem_range.mp hc
    have := e.injective (Subtype.val_injective heq); contradiction
  · intro hc; have ⟨z, heq⟩ := Set.mem_range.mp hc
    have := e.injective (Subtype.val_injective heq); contradiction
  · refine Set.disjoint_left.mpr ?_; intro z hz hz'
    have ⟨x, heq⟩ := Set.mem_range.mp hz
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hz'
    have := e.injective (Subtype.val_injective heq) |> Option.some_injective _
    contradiction

variable {fork : l} (hfork : fork ≠ ⊥)

lemma exists_par (α β : Lpo l) :
    ∃ (γ : Lpo l) (i : ParLpoIsomorphism α β),
      γ = Lpo.par i.hx i.hx' i.hdisj hfork := by
  have ⟨i⟩ := exists_isomorphic_lpos α β
  exact ⟨_, i, rfl⟩

noncomputable def par : Pom l → Pom l → Pom l :=
  Quotient.map₂ (fun α β ↦ (exists_par hfork α β).choose) <| by
    intro α₁ α₂ hα β₁ β₂ hβ
    have h₁ := (exists_par hfork α₁ β₁).choose_spec
    have h₂ := (exists_par hfork α₂ β₂).choose_spec
    rw [h₁.choose_spec, h₂.choose_spec]
    refine Lpo.par_isomorphic ?_ ?_
    · exact Setoid.trans (Setoid.symm h₁.choose.hα) <| Setoid.trans hα h₂.choose.hα
    · exact Setoid.trans (Setoid.symm h₁.choose.hβ) <| Setoid.trans hβ h₂.choose.hβ

lemma mem_par {p q : Pom l} {α β : Lpo l}
    {x : Node} {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes} {hd : Disjoint α.nodes β.nodes}
    (h₁ : α ∈ p) (h₂ : β ∈ q) :
    Lpo.par hx hx' hd hfork ∈ par hfork p q := by
  rcases h₁ with rfl; rcases h₂ with rfl
  conv => lhs; exact Quotient.map₂_mk _ _ _ _
  have h := (exists_par hfork α β).choose_spec
  rw [h.choose_spec]
  refine Quotient.eq_iff_equiv.mpr (Lpo.par_isomorphic ?_ ?_)
  · symm; exact h.choose.hα
  · symm; exact h.choose.hβ

lemma exists_rep_par (p q : Pom l) :
    ∃ (α β : Lpo l) (x : Node) (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes)
      (hd : Disjoint α.nodes β.nodes),
      α ∈ p ∧ β ∈ q ∧ Lpo.par hx hx' hd hfork ∈ par hfork p q := by
  obtain ⟨α, rfl⟩ := p.exists_rep
  obtain ⟨β, rfl⟩ := q.exists_rep
  have ⟨i, heq⟩ := (exists_par hfork α β).choose_spec
  refine ⟨i.α', i.β', i.root, i.hx, i.hx', i.hdisj, ?_, ?_, ?_⟩
  · exact Quotient.eq_iff_equiv.mpr i.hα
  · exact Quotient.eq_iff_equiv.mpr i.hβ
  · rw [← heq]; exact Quotient.map₂_mk _ _ _ _

lemma par_monotone {l : Type} [PartialOrder l] [OrderBot l] {fork : l} (hfork : fork ≠ ⊥)
    {p p' q q' : Pom l} (hle₁ : p ≤ p') (hle₂ : q ≤ q') :
    par hfork p q ≤ par hfork p' q' := by
  obtain ⟨α', β', x, hx, hx', hd, rfl, rfl, hmem⟩ := exists_rep_par hfork p' q'
  have ⟨α, hα, hle₁⟩ := ge_lpo hle₁
  have ⟨β, hβ, hle₂⟩ := ge_lpo hle₂
  refine ⟨Lpo.par (α := α) (β := β) (x := x) ?_ ?_ ?_ hfork, ?_, _, hmem, ?_⟩
  · intro hc; apply hx; exact hle₁.nodes hc
  · intro hc; apply hx'; exact hle₂.nodes hc
  · exact hd.mono hle₁.nodes hle₂.nodes
  · refine mem_par hfork hα hβ
  · exact Lpo.par_monotone (le_refl _) hle₁ hle₂

end Pom
