import Pom.Basic
import Pom.Lpo.Operations.Par
import Pom.Lpo.Operations.Par.Isomorphism

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
  let e₁ := Equiv.ofInjective (Subtype.val ∘ e ∘ some ∘ Sum.inl)
  let e₂ := Equiv.ofInjective (Subtype.val ∘ e ∘ some ∘ Sum.inr)
  refine ⟨{
    root := (e none).val
    α' := α.permute (e₁ ?_)
    β' := β.permute (e₂ ?_)
    hα := ⟨_, rfl⟩
    hβ := ⟨_, rfl⟩
    hx := ?_
    hx' := ?_
    hdisj := ?_
  }⟩
  · exact Subtype.val_injective.comp <| e.injective.comp <| (Option.some_injective _).comp <|
      Sum.inl_injective
  · exact Subtype.val_injective.comp <| e.injective.comp <| (Option.some_injective _).comp <|
      Sum.inr_injective
  · unfold e₁; intro hc
    have ⟨z, heq⟩ := Set.mem_range.mp hc
    have := e.injective (Subtype.val_injective heq); contradiction
  · unfold e₂; intro hc
    have ⟨z, heq⟩ := Set.mem_range.mp hc
    have := e.injective (Subtype.val_injective heq); contradiction
  · refine Set.disjoint_left.mpr ?_; intro z hz hz'
    have ⟨x, heq⟩ := Set.mem_range.mp hz
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hz'
    have := e.injective (Subtype.val_injective heq) |> Option.some_injective _
    contradiction

variable {fork : l} (hfork : fork ≠ ⊥)

noncomputable def par_fun (α β : Lpo l) : Lpo l :=
  let s := (exists_isomorphic_lpos α β).some
  Lpo.par s.hx s.hx' s.hdisj hfork

lemma par_fun_isomorphic {α α' β β' : Lpo l} (hα : α ≈ α') (hβ : β ≈ β') :
    par_fun hfork α β ≈ par_fun hfork α' β' := by
  have h := exists_isomorphic_lpos α β
  have h' := exists_isomorphic_lpos α' β'
  unfold par_fun; refine Lpo.par_isomorphic ?_ ?_
  · exact Setoid.trans (Setoid.symm h.some.hα) <| Setoid.trans hα h'.some.hα
  · exact Setoid.trans (Setoid.symm h.some.hβ) <| Setoid.trans hβ h'.some.hβ

noncomputable def par : Pom l → Pom l → Pom l :=
  Quotient.map₂ (par_fun hfork) (fun _ _ hα _ _ hβ ↦ par_fun_isomorphic hfork hα hβ)

end Pom
