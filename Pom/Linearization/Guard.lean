import DomainTheory.OmegaCompletePartialOrder.Instances

import Pom.Linearization
import Pom.Operations.Guard

open Linearization

namespace Lpofin

noncomputable def guard {l : Type} [Bot l] {x : Node} {ℓ : l} {α β : Lpofin l}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes)
    (hroot : ℓ ≠ ⊥) : Lpofin l :=
  ⟨Lpo.guard hx hx' hd hroot,
    Set.finite_insert.mpr (Set.finite_union.mpr ⟨α.property, β.property⟩)⟩

open Classical in
lemma next_guard_eq_singleton {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    next (Lpofin.guard hx hx' hd (Label.test_ne_bot b))
      (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).nodes_finset = {x} := by
  ext y
  simp only [next, Finset.mem_filter, Lpofin.nodes_finset,
    Set.Finite.mem_toFinset, Lpo.nodes, Finset.mem_singleton]
  constructor
  · rintro ⟨hy, _, hmin⟩
    rcases hy with rfl | hy
    · rfl
    · exfalso
      exact hmin x (Or.inl ⟨rfl, hy⟩) (Set.mem_insert x _)
  · rintro rfl
    refine ⟨Or.inl rfl, Set.mem_insert y _, ?_⟩
    intro z hz
    rcases hz with ⟨rfl, hy⟩ | hp | hq
    · exact (hy.elim hx hx').elim
    · exact (hx ((p.val.property.rel_dom hp).2)).elim
    · exact (hx' ((q.val.property.rel_dom hq).2)).elim

lemma filter_guard_root_true {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.filter_by_outcome a.nodes_finset x true = p.nodes_finset := by
  classical
  dsimp only
  ext y
  simp only [filter_by_outcome, Finset.mem_filter, Finset.mem_erase,
    Lpofin.nodes_finset, Set.Finite.mem_toFinset, Lpofin.form, Lpo.form,
    Form.and, Form.sat, cond_true]
  constructor
  · rintro ⟨⟨_, hy⟩, v, hv, hvx⟩
    rcases hv with rfl | ⟨hyp, _, _⟩ | ⟨hyq, _, hnx⟩
    · contradiction
    · exact hyp
    · exact (hnx hvx).elim
  · intro hyp
    obtain ⟨v, hv⟩ := (p.val.property.form_dom y).mpr hyp
    refine ⟨⟨?_, ?_⟩, Set.insert x v, ?_, Set.mem_insert x _⟩
    · exact fun h ↦ hx (h ▸ hyp)
    · exact Set.mem_insert_of_mem x (Or.inl hyp)
    · right; left
      refine ⟨hyp, ?_, Set.mem_insert x _⟩
      exact (((p.val.property.form y) hyp).1 _ _ <| by
        refine Set.disjoint_left.mpr ?_
        intro z hz hrel
        have hz' : z = x := by
          rcases Set.mem_symmDiff.mp hz with ⟨hz, hn⟩ | ⟨hz, hn⟩
          · rcases Set.mem_insert_iff.mp hz with hzx | hzv
            · exact hzx
            · exact (hn hzv).elim
          · exact (hn (Set.mem_insert_of_mem x hz)).elim
        subst z
        exact hx (p.val.property.rel_dom hrel).1).mpr hv

lemma filter_guard_root_false {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.filter_by_outcome a.nodes_finset x false = q.nodes_finset := by
  classical
  dsimp only
  ext y
  simp only [filter_by_outcome, Finset.mem_filter, Finset.mem_erase,
    Lpofin.nodes_finset, Set.Finite.mem_toFinset, Lpofin.form, Lpo.form,
    Form.and, Form.sat, cond_false]
  constructor
  · rintro ⟨⟨_, hy⟩, v, hv, hnx⟩
    rcases hv with rfl | ⟨hyp, _, hvx⟩ | ⟨hyq, _, _⟩
    · contradiction
    · exact (hnx hvx).elim
    · exact hyq
  · intro hyq
    obtain ⟨v, hv⟩ := (q.val.property.form_dom y).mpr hyq
    refine ⟨⟨?_, ?_⟩, v \ {x}, ?_, ?_⟩
    · exact fun h ↦ hx' (h ▸ hyq)
    · exact Set.mem_insert_of_mem x (Or.inr hyq)
    · right; right
      refine ⟨hyq, ?_, ?_⟩
      · exact (((q.val.property.form y) hyq).1 _ _ <| by
          refine Set.disjoint_left.mpr ?_
          intro z hz hrel
          have hz' : z = x := by
            simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_singleton_iff] at hz
            aesop
          subst z
          exact hx' (q.val.property.rel_dom hrel).1).mpr hv
      · intro h
        exact ((Set.mem_sdiff x).mp h).2 (Set.mem_singleton x)
    · intro h
      exact ((Set.mem_sdiff x).mp h).2 (Set.mem_singleton x)

lemma guard_left_next {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (hu : ↑u ⊆ p.nodes) :
    let a : Lpofin (Label act test) := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.next u = p.next u := by
  classical
  ext y
  simp only [next, Finset.mem_filter, Lpofin.nodes_finset, Set.Finite.mem_toFinset,
    Lpo.nodes, Lpofin.rel, Lpo.rel]
  constructor
  · rintro ⟨hy, hyu, hmin⟩
    exact ⟨hu hyu, hyu, fun z hz hzu ↦ hmin z (Or.inr (Or.inl hz)) hzu⟩
  · rintro ⟨hyp, hyu, hmin⟩
    refine ⟨Set.mem_insert_of_mem x (Or.inl hyp), hyu, ?_⟩
    intro z hz hzu
    rcases hz with ⟨rfl, _⟩ | hp | hq
    · exact hx (hu hzu)
    · exact hmin z hp hzu
    · exact (Set.disjoint_left.mp hd (hu hzu) (q.val.property.rel_dom hq).1).elim

lemma guard_left_lab {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (hy : y ∈ p.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.lab y = p.lab y := by
  dsimp only [Lpofin.lab, Lpo.lab, Lpofin.guard, Lpo.guard, Lpo.par_gen, Lpo.par_base]
  rw [if_neg]
  · exact if_pos hy
  · exact Ne.symm (fun h ↦ hx (h ▸ hy))

lemma guard_left_filter {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (hu : ↑u ⊆ p.nodes)
    (hy : y ∈ u) (r : Bool) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.filter_by_outcome u y r = p.filter_by_outcome u y r := by
  classical
  ext z
  simp only [filter_by_outcome, Finset.mem_filter, Finset.mem_erase,
    Lpofin.form, Lpo.form]
  constructor
  · rintro ⟨hze, v, hv, hb⟩
    rcases hv with rfl | ⟨hzp, hpv, _⟩ | ⟨hzq, _, _⟩
    · exact (hx (hu hze.2)).elim
    · exact ⟨hze, v, hpv, hb⟩
    · exact (Set.disjoint_right.mp hd hzq (hu hze.2)).elim
  · rintro ⟨hze, v, hpv, hb⟩
    have hxy : x ≠ y := fun h ↦ hx (h ▸ hu hy)
    refine ⟨hze, Set.insert x v, ?_, ?_⟩
    · right; left
      refine ⟨hu hze.2, ?_, Set.mem_insert x _⟩
      exact (((p.val.property.form z) (hu hze.2)).1 _ _ <| by
        refine Set.disjoint_left.mpr ?_
        intro w hw hrel
        have hwx : w = x := by
          rcases Set.mem_symmDiff.mp hw with ⟨hw, hn⟩ | ⟨hw, hn⟩
          · rcases Set.mem_insert_iff.mp hw with h | h
            · exact h
            · exact (hn h).elim
          · exact (hn (Set.mem_insert_of_mem x hw)).elim
        subst w
        exact hx (p.val.property.rel_dom hrel).1).mpr hpv
    · match r with
      | true =>
        exact Set.mem_insert_of_mem x hb
      | false =>
        intro h
        rcases Set.mem_insert_iff.mp h with heq | hv
        · exact hxy heq.symm
        · exact hb hv

open Classical in
lemma nondet_finset_congr {α ι : Type} [Nondet α] {X Y : Finset ι}
    (h : X = Y) (f : ↑X → α) (g : ↑Y → α)
    (hfg : ∀ x : ↑X, f x = g ⟨x, h ▸ x.property⟩) :
    Nondet.nondet f = Nondet.nondet g := by
  subst Y
  congr
  funext x
  exact hfg x

lemma lin_rec_guard_left_aux {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (hu : ↑u ⊆ p.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    (Lpofin.lin_rec (t := t) a u : s → t s) = Lpofin.lin_rec (t := t) p u := by
  classical
  induction u using Finset.strongInduction with
  | H u ih =>
    ext σ
    unfold lin_rec
    by_cases he : u = ∅
    · simp only [he, ↓reduceIte]
    · simp only [he, ↓reduceIte]
      apply @nondet_finset_congr (t s) Node _ _ _
        (guard_left_next p q b hx hx' hd u hu)
      intro ⟨y, hy⟩
      have hyu : y ∈ u := (Finset.mem_filter.mp hy).2.1
      have hyp : y ∈ p.nodes := hu hyu
      simp only [lin_node]
      rw [guard_left_lab p q b hx hx' hd hyp]
      match hl : p.lab y with
      | Label.bot => rfl
      | Label.fork =>
        simp only
        exact congrFun (ih (u.erase y) (Finset.erase_ssubset hyu)
          (fun _ h ↦ hu (Finset.mem_of_mem_erase h))) σ
      | Label.act ac =>
        simp only
        congr 1
        funext τ
        exact congrFun (ih (u.erase y) (Finset.erase_ssubset hyu)
          (fun _ h ↦ hu (Finset.mem_of_mem_erase h))) τ
      | Label.test bb =>
        simp only
        congr 1
        funext r
        rw [guard_left_filter p q b hx hx' hd u hu hyu r]
        exact congrFun (ih (p.filter_by_outcome u y r)
          (Finset.ssubset_of_subset_of_ssubset filter_by_outcome_sub_erase
            (Finset.erase_ssubset hyu))
          (fun z hz ↦ hu (filter_by_outcome_sub_erase hz |> Finset.mem_of_mem_erase))) σ

lemma guard_right_next {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (hu : ↑u ⊆ q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.next u = q.next u := by
  classical
  ext y
  simp only [next, Finset.mem_filter, Lpofin.nodes_finset, Set.Finite.mem_toFinset,
    Lpo.nodes, Lpofin.rel, Lpo.rel]
  constructor
  · rintro ⟨hy, hyu, hmin⟩
    exact ⟨hu hyu, hyu, fun z hz hzu ↦ hmin z (Or.inr (Or.inr hz)) hzu⟩
  · rintro ⟨hyq, hyu, hmin⟩
    refine ⟨Set.mem_insert_of_mem x (Or.inr hyq), hyu, ?_⟩
    intro z hz hzu
    rcases hz with ⟨rfl, _⟩ | hp | hq
    · exact hx' (hu hzu)
    · exact (Set.disjoint_left.mp hd (p.val.property.rel_dom hp).1 (hu hzu)).elim
    · exact hmin z hq hzu

lemma guard_right_lab {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (hy : y ∈ q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.lab y = q.lab y := by
  dsimp only [Lpofin.lab, Lpo.lab, Lpofin.guard, Lpo.guard, Lpo.par_gen, Lpo.par_base]
  rw [if_neg]
  · exact if_neg (Set.disjoint_right.mp hd hy)
  · exact Ne.symm (fun h ↦ hx' (h ▸ hy))

lemma guard_right_filter {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (hu : ↑u ⊆ q.nodes)
    (hy : y ∈ u) (r : Bool) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.filter_by_outcome u y r = q.filter_by_outcome u y r := by
  classical
  ext z
  simp only [filter_by_outcome, Finset.mem_filter, Finset.mem_erase,
    Lpofin.form, Lpo.form]
  constructor
  · rintro ⟨hze, v, hv, hb⟩
    rcases hv with rfl | ⟨hzp, _, _⟩ | ⟨hzq, hqv, _⟩
    · exact (hx' (hu hze.2)).elim
    · exact (Set.disjoint_left.mp hd hzp (hu hze.2)).elim
    · exact ⟨hze, v, hqv, hb⟩
  · rintro ⟨hze, v, hqv, hb⟩
    have hxy : x ≠ y := fun h ↦ hx' (h ▸ hu hy)
    refine ⟨hze, v \ {x}, ?_, ?_⟩
    · right; right
      refine ⟨hu hze.2, ?_, ?_⟩
      · exact (((q.val.property.form z) (hu hze.2)).1 _ _ <| by
          refine Set.disjoint_left.mpr ?_
          intro w hw hrel
          have hwx : w = x := by
            simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_singleton_iff] at hw
            aesop
          subst w
          exact hx' (q.val.property.rel_dom hrel).1).mpr hqv
      · intro h
        exact ((Set.mem_sdiff x).mp h).2 (Set.mem_singleton x)
    · match r with
      | true =>
        exact (Set.mem_sdiff y).mpr ⟨hb, hxy.symm⟩
      | false =>
        intro h
        exact hb ((Set.mem_sdiff y).mp h).1

lemma lin_rec_guard_right_aux {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (hu : ↑u ⊆ q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    (Lpofin.lin_rec (t := t) a u : s → t s) = Lpofin.lin_rec (t := t) q u := by
  classical
  induction u using Finset.strongInduction with
  | H u ih =>
    ext σ
    unfold lin_rec
    by_cases he : u = ∅
    · simp only [he, ↓reduceIte]
    · simp only [he, ↓reduceIte]
      apply @nondet_finset_congr (t s) Node _ _ _
        (guard_right_next p q b hx hx' hd u hu)
      intro ⟨y, hy⟩
      have hyu : y ∈ u := (Finset.mem_filter.mp hy).2.1
      have hyq : y ∈ q.nodes := hu hyu
      simp only [lin_node]
      rw [guard_right_lab p q b hx hx' hd hyq]
      match hl : q.lab y with
      | Label.bot => rfl
      | Label.fork =>
        simp only
        exact congrFun (ih (u.erase y) (Finset.erase_ssubset hyu)
          (fun _ h ↦ hu (Finset.mem_of_mem_erase h))) σ
      | Label.act ac =>
        simp only
        congr 1
        funext τ
        exact congrFun (ih (u.erase y) (Finset.erase_ssubset hyu)
          (fun _ h ↦ hu (Finset.mem_of_mem_erase h))) τ
      | Label.test bb =>
        simp only
        congr 1
        funext r
        rw [guard_right_filter p q b hx hx' hd u hu hyu r]
        exact congrFun (ih (q.filter_by_outcome u y r)
          (Finset.ssubset_of_subset_of_ssubset filter_by_outcome_sub_erase
            (Finset.erase_ssubset hyu))
          (fun z hz ↦ hu (filter_by_outcome_sub_erase hz |> Finset.mem_of_mem_erase))) σ

lemma lin_rec_guard_left {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (p q : Lpofin (Label act test)) (b : test) (σ : s)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    Lpofin.lin_rec (t := t) a p.nodes_finset σ = Lpofin.lin (t := t) p σ := by
  exact congrFun (lin_rec_guard_left_aux p q b hx hx' hd p.nodes_finset
    (fun _ h ↦ p.property.mem_toFinset.mp h)) σ

lemma lin_rec_guard_right {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (p q : Lpofin (Label act test)) (b : test) (σ : s)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    Lpofin.lin_rec (t := t) a q.nodes_finset σ = Lpofin.lin (t := t) q σ := by
  exact congrFun (lin_rec_guard_right_aux p q b hx hx' hd q.nodes_finset
    (fun _ h ↦ q.property.mem_toFinset.mp h)) σ

lemma lin_guard_branch_true {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (p q : Lpofin (Label act test)) (b : test) (σ : s)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    Lpofin.lin_rec (t := t) a (a.filter_by_outcome a.nodes_finset x true) σ =
      Lpofin.lin (t := t) p σ := by
  dsimp only
  have hf := filter_guard_root_true p q b hx hx' hd
  dsimp only at hf
  rw [hf]
  exact lin_rec_guard_left p q b σ hx hx' hd

lemma lin_guard_branch_false {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (p q : Lpofin (Label act test)) (b : test) (σ : s)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    Lpofin.lin_rec (t := t) a (a.filter_by_outcome a.nodes_finset x false) σ =
      Lpofin.lin (t := t) q σ := by
  dsimp only
  have hf := filter_guard_root_false p q b hx hx' hd
  dsimp only at hf
  rw [hf]
  exact lin_rec_guard_right p q b σ hx hx' hd

lemma lin_guard_branch {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (p q : Lpofin (Label act test)) (b : test) (σ : s) (r : Bool)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    Lpofin.lin_rec (t := t) a (a.filter_by_outcome a.nodes_finset x r) σ =
      bif r then Lpofin.lin (t := t) p σ else Lpofin.lin (t := t) q σ := by
  cases r
  · exact lin_guard_branch_false p q b σ hx hx' hd
  · exact lin_guard_branch_true p q b σ hx hx' hd

lemma lin_guard {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    {p q : Lpofin (Label act test)} {b : test}
    {x : Node} {hx : x ∉ p.nodes} {hx' : x ∉ q.nodes}
    {hd : Disjoint p.nodes q.nodes} :
    (lin (Lpofin.guard hx hx' hd (Label.test_ne_bot b)) : s → t s) =
    fun σ ↦ Sem.sem b σ >>= fun r ↦ bif r then lin p σ else lin q σ := by
  classical
  ext σ
  let a : Lpofin (Label act test) :=
    ⟨Lpo.guard hx hx' hd (Label.test_ne_bot b), by
      exact Set.finite_insert.mpr (Set.finite_union.mpr ⟨p.property, q.property⟩)⟩
  let vp : t s := Lpofin.lin p σ
  let vq : t s := Lpofin.lin q σ
  change Lpofin.lin a σ = Sem.sem b σ >>= fun r ↦ bif r then vp else vq
  unfold Lpofin.lin Lpofin.lin_rec
  have hnext : next a a.nodes_finset = {x} := next_guard_eq_singleton p q b hx hx' hd
  have hu : Unique ↑(next a a.nodes_finset) := by
    rw [hnext]; infer_instance
  refine (if_neg ?_).trans <| (@Nondet.nondet_singleton (t s) _ _ hu _).trans ?_
  · exact Finset.ne_empty_of_mem (a.property.mem_toFinset.mpr (Set.mem_insert x _))
  · have := @Unique.eq_default _ hu ⟨x, by rw [hnext]; exact Finset.mem_singleton_self _⟩
    rw [← this]; simp only [lin_node]
    have halab : a.lab x = Label.test b := by
      simp [a, Lpofin.lab, Lpo.lab, Lpo.guard, Lpo.par_gen, Lpo.par_base]
    rw [halab]
    change (Sem.sem b σ >>= fun r ↦ Lpofin.lin_rec (t := t) a
      (a.filter_by_outcome a.nodes_finset x r) σ) = _
    congr 1
    funext r
    exact lin_guard_branch p q b σ r hx hx' hd

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
