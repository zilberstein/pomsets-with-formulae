import Pom.Linearization

open Linearization

namespace Label

def eval {t : Type → Type} {s act test : Type}
    [Linearizable t s] [Bot (t s)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (ℓ : Label act test) : s → t s :=
  match ℓ with
    | Label.bot => ⊥
    | Label.fork => pure
    | Label.act a => Sem.sem a
    | Label.test b => fun σ ↦ (Sem.sem b σ : t Bool) *> pure σ

end Label

namespace Lpofin

lemma singleton_next {l : Type} [Bot l] (x : Node) (ℓ : l) :
    next (singleton x ℓ) (singleton x ℓ).nodes_finset = {x} := by
  classical
  ext y; constructor
  · intro h; have ⟨hy, _, _⟩ := Finset.mem_filter.mp h
    obtain rfl := (Set.Finite.mem_toFinset _).mp hy
    exact Finset.mem_singleton_self _
  · intro hy; obtain rfl := Finset.mem_singleton.mp hy
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩ <;>
      try (apply (Set.Finite.mem_toFinset _).mpr; exact Set.mem_singleton _)
    · rintro _ ⟨⟩

lemma singleton_erase {l : Type} [Bot l] (x : Node) (ℓ : l) :
    (singleton x ℓ).nodes_finset.erase x = ∅ := by
  apply Finset.eq_empty_of_forall_notMem; intro y hy
  have ⟨hne, hy⟩ := Finset.mem_erase.mp hy
  obtain rfl := (Set.Finite.mem_toFinset _).mp hy
  contradiction

lemma singleton_filter {l : Type} [Bot l] (x : Node) (ℓ : l) (r : Bool) :
    (singleton x ℓ).filter_by_outcome (singleton x ℓ).nodes_finset x r = ∅ := by
  apply Finset.eq_empty_of_forall_notMem; intro y hy
  classical
  have ⟨he, _⟩ := Finset.mem_filter.mp hy
  rw [singleton_erase] at he; contradiction

lemma lin_rec_eq_empty {t : Type → Type} {s act test : Type}
    [Linearizable t s] [Bot (t s)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (α : Lpofin (Label act test)) {u : Finset Node}
    (h : u = ∅) :
    (α.lin_rec u : s → t s) = pure := by
  ext σ; unfold lin_rec; refine if_pos h

theorem lin_singleton {t : Type → Type} {s act test : Type}
    [Linearizable t s] [Bot (t s)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (x : Node) (ℓ : Label act test) :
    (lin (singleton x ℓ) : s → t s) = ℓ.eval := by
  ext σ; unfold lin lin_rec
  -- First iteration, node x gets evaluated
  refine (if_neg ?_).trans ?_
  · refine Finset.ne_empty_of_mem (a := x) ?_
    exact (Set.Finite.mem_toFinset _).mpr (Set.mem_singleton _)
  · conv => lhs; exact Nondet.finset_singleton x (singleton_next x ℓ)
    simp only [lin_node, Label.eval]
    have hℓ : (singleton x ℓ).lab x = ℓ := if_pos rfl; rw [hℓ]
    cases ℓ with
    | bot => rfl
    | fork =>
      exact congrFun (lin_rec_eq_empty _ (singleton_erase _ _)) _
    | act a =>
      refine Eq.trans ?_ (bind_pure _)
      refine congrArg₂ Bind.bind rfl (lin_rec_eq_empty _ ?_)
      exact singleton_erase _ _
    | test b =>
      simp only
      rw [seqRight_eq_bind]; refine congrArg₂ Bind.bind rfl ?_
      ext r; refine congrFun (lin_rec_eq_empty _ ?_) _
      exact singleton_filter _ _ _

end Lpofin


namespace Pom

theorem lin_singleton {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [Sem act s (t s)]
    [DCPO test] [Sem test s (t Bool)]
    (ℓ : Label act test) :
    (lin (singleton ℓ) : s → t s) = ℓ.eval := by
  rw [Pomfin.singleton_eq, lin_eq_fin]
  conv => lhs; exact Pomfin.lin_mk _
  exact Lpofin.lin_singleton default ℓ

lemma lin_bot {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [Sem act s (t s)]
    [DCPO test] [Sem test s (t Bool)] :
    @lin t s act test _ _ _ _ _ _ _ (singleton ⊥) = ⊥ := lin_singleton _

lemma lin_fork {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [Sem act s (t s)]
    [DCPO test] [Sem test s (t Bool)] :
    @lin t s act test _ _ _ _ _ _ _ (singleton Label.fork) = pure := lin_singleton _

lemma lin_act {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [Sem act s (t s)]
    [DCPO test] [Sem test s (t Bool)]
    (a : act) :
    @lin t s act test _ _ _ _ _ _ _ (singleton (Label.act a)) = Sem.sem a := lin_singleton _

end Pom
