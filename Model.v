(* The staged-set model of the type theory of Theorem 1.1, in Rocq 9.1 with the
   standard library's core only.

   Part 0: preliminaries (universe-polymorphic records and equality, the axioms of
   the metatheory). Part I: the specification, a category with families [CwF] with
   one sort of types and the structure [TModel] of the rules on it, stated with the
   operations of the CwF only. Part II: staged sets over a well-order of stages.
   Part III: the CwF of staged sets, the model [stagedModel], and the failure of
   excluded middle and of propositional extensionality. Part IV: the model
   [natModel] for the stages nat. Part V: the universe classifies the types.

   Reading guide. The result is [natModel : TModel stagedCwF] in Part IV, and Rocq
   checks every proof. To check Theorem 1.1, it suffices to read the axioms of
   Part 0 and the specification in Part I, which states the rules of the paper on
   an arbitrary CwF. Parts II and III construct the model of the paper. Their
   comments give the definitions of the paper, in the notation of the paper:

     |X|, ν(x)          [carrier X], [birth X x]    a staged set X, with ν : |X| → L
     L∞ = L ∪ {∞}       [TV], with ∞ = [None]       truth values
     ⌞p⌟                [decode p]                  one element born at p, none if p = ∞
     ν(X)               [nuS X]                     min {ν(x) | x ∈ |X|}, ∞ if X = ∅
     𝚷(X, Y), 𝚺(X, Y)   [SPi X Y], [SigS A B γ]     staged product and staged sum
     Γ.A, A[σ], t[σ]    [Γ ▹ A], [A[σ]], [t[σ]ₜ]     for [ext Γ A], [sub A σ], [subTm t σ]
     σ : Δ → Γ, σ ∘ δ   [σ : Δ ⟶ Γ], [σ ∘ δ]         for [Hom Δ Γ], [comp σ δ]

   Universes: everything is universe-polymorphic and the records are cumulative;
   the universe of the model is a universe of Rocq. The stdlib's [sig], [sigT] and equality lemmas are not
   used: they are template-polymorphic or monomorphic and would bound every level
   by a global universe. *)

Set Universe Polymorphism.
Set Primitive Projections.

(** * Part 0. Preliminaries *)

(** Subsets [{x : A | P x}] and dependent pairs [(x, y)], [x : A], [y : B x]. *)
#[universes(polymorphic, cumulative)]
Record Sub@{i} (A : Type@{i}) (P : A -> Prop) : Type@{i} := mkSub { val : A; prf : P val }.
Arguments mkSub {A P} val prf. Arguments val {A P} _. Arguments prf {A P} _.
#[universes(polymorphic, cumulative)]
Record Sig@{i} (A : Type@{i}) (B : A -> Type@{i}) : Type@{i} := mkSig { fst : A; snd : B fst }.
Arguments mkSig {A B} fst snd. Arguments fst {A B} _. Arguments snd {A B} _.

(** Equality, by pattern matching only: transport [tr P e : P x → P y] along
    [e : x = y], congruence [ap], inverse [inv] and composition [cat]. *)
Definition tr@{u v} {A : Type@{u}} (P : A -> Type@{v}) {x y : A} (e : x = y) (p : P x) : P y :=
  match e with eq_refl => p end.
Definition ap@{u v} {A : Type@{u}} {B : Type@{v}} (f : A -> B) {x y : A} (e : x = y) : f x = f y :=
  match e with eq_refl => eq_refl end.
Definition inv@{u} {A : Type@{u}} {x y : A} (e : x = y) : y = x := match e with eq_refl => eq_refl end.
Definition cat@{u} {A : Type@{u}} {x y z : A} (e : x = y) (e' : y = z) : x = z :=
  match e' with eq_refl => e end.

(** [rw H] rewrites the left side of [H] into its right side, and [rwl H] the
    right side into the left, by [tr]. *)
Ltac rw H :=
  lazymatch type of H with
  | @eq ?T ?a ?b =>
      lazymatch goal with |- context [a] => idtac | _ => fail "rw: no occurrence" end;
      pattern a; lazymatch goal with |- ?P a => refine (tr P (inv H) _) end; cbv beta
  end.
Ltac rwl H :=
  lazymatch type of H with
  | @eq ?T ?a ?b =>
      lazymatch goal with |- context [b] => idtac | _ => fail "rwl: no occurrence" end;
      pattern b; lazymatch goal with |- ?P b => refine (tr P H _) end; cbv beta
  end.

(** The axioms of the metatheory: excluded middle, propositional extensionality,
    function extensionality, and global choice as constructive indefinite description. *)
Axiom em : forall P : Prop, P \/ ~ P.
Axiom propext : forall P Q : Prop, (P <-> Q) -> P = Q.
Axiom funext@{u v} : forall {A : Type@{u}} {B : A -> Type@{v}} (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.
Axiom choice@{u} : forall {A : Type@{u}} (P : A -> Prop), (exists x, P x) -> Sub@{u} A P.

(** Proof irrelevance, from propositional extensionality, with the consequences for
    subsets and transports. *)
Lemma proof_irrel {P : Prop} (p q : P) : p = q.
Proof.
  assert (H : P = True) by (apply propext; split; [intros _; exact I | intros _; exact p]).
  revert p q. rw H. intros [] []. reflexivity.
Qed.
Lemma sub_eq@{i} {A : Type@{i}} {P : A -> Prop} (s t : Sub@{i} A P) : val s = val t -> s = t.
Proof. destruct s as [v p], t as [w q]; cbn. intros e. destruct e, (proof_irrel p q). reflexivity. Qed.
Lemma tr_irrel@{u v} {A : Type@{u}} (P : A -> Type@{v}) {x : A} (e : x = x) (p : P x) : tr P e p = p.
Proof. rw (proof_irrel e eq_refl). reflexivity. Qed.

(** Generic transport lemmas, used to build the equations of types in the specification.
    [treq P x y], for [x : P a] and [y : P b], says that [x] and [y] are equal along an
    equation [a = b]. *)
Definition treq {A : Type} (P : A -> Type) {a b : A} (x : P a) (y : P b) : Prop :=
  exists e : a = b, tr P e x = y.
Lemma treq_tr {A : Type} (P : A -> Type) {a b : A} (e : a = b) (x : P a) : treq P x (tr P e x).
Proof. exists e. reflexivity. Qed.
Lemma treq_sym {A : Type} (P : A -> Type) {a b : A} {x : P a} {y : P b} : treq P x y -> treq P y x.
Proof. intros [e h]. destruct e, h. exists eq_refl. reflexivity. Qed.
Lemma treq_trans {A : Type} (P : A -> Type) {a b c : A} {x : P a} {y : P b} {z : P c} :
  treq P x y -> treq P y z -> treq P x z.
Proof. intros [e h] [e' h']. destruct e, h, e', h'. exists eq_refl. reflexivity. Qed.
Lemma treq_tr_eq {A : Type} (P : A -> Type) {a b : A} (e : a = b) (x : P a) (y : P b) :
  treq P x y -> tr P e x = y.
Proof. intros [e' h]. rw (proof_irrel e e'). exact h. Qed.
Lemma treq_ap {A B : Type} (P : A -> Type) (Q : B -> Type) (f : A -> B) (g : forall a, P a -> Q (f a))
    {a b : A} {x : P a} {y : P b} : treq P x y -> treq Q (g a x) (g b y).
Proof. intros [e h]. destruct e, h. exists eq_refl. reflexivity. Qed.
Lemma ap_dep {A R : Type} (P : A -> Type) (g : forall a, P a -> R) {a b : A} {x : P a} {y : P b} :
  treq P x y -> g a x = g b y.
Proof. intros [e h]. destruct e, h. reflexivity. Qed.
Lemma ap_dep2 {A R : Type} (P : A -> Type) (g : forall a, P a -> P a -> R) {a b : A} (e : a = b)
    {x1 x2 : P a} {y1 y2 : P b} : tr P e x1 = y1 -> tr P e x2 = y2 -> g a x1 x2 = g b y1 y2.
Proof. destruct e. intros h1 h2. destruct h1, h2. reflexivity. Qed.
Lemma tr_ap {A B : Type} (P : B -> Type) (f : A -> B) {a b : A} (e : a = b) (x : P (f a)) :
  tr (fun a => P (f a)) e x = tr P (ap f e) x.
Proof. destruct e. reflexivity. Qed.
Lemma tr_apD {A : Type} (P : A -> Type) (f : forall a, P a) {a b : A} (e : a = b) : tr P e (f a) = f b.
Proof. destruct e. reflexivity. Qed.
Lemma tr_app2 {A R : Type} (P Q : A -> Type) (g : forall a, P a -> Q a -> R) {a b : A} (e : a = b)
    (x : P a) (y : Q a) : g b (tr P e x) (tr Q e y) = g a x y.
Proof. destruct e. reflexivity. Qed.

(** Transparent projections of a conjunction. *)
Definition and1 {P Q : Prop} (h : P /\ Q) : P := match h with conj p _ => p end.
Definition and2 {P Q : Prop} (h : P /\ Q) : Q := match h with conj _ q => q end.

(** A Boolean decision [decb P] of a proposition, by excluded middle and choice. *)
Definition ft_absurd (e : false = true) : False :=
  match e in _ = b return (if b then False else True) with eq_refl => I end.
Definition decbS (P : Prop) : Sub bool (fun b => b = true <-> P) :=
  choice (fun b : bool => b = true <-> P)
    (match em P with
     | or_introl h => ex_intro _ true (conj (fun _ => h) (fun _ => eq_refl))
     | or_intror h => ex_intro _ false (conj (fun e => match ft_absurd e with end)
                                             (fun p => match h p with end))
     end).
Definition decb (P : Prop) : bool := val (decbS P).
Lemma decb_spec (P : Prop) : decb P = true <-> P.
Proof. exact (prf (decbS P)). Qed.
Lemma decb_true (P : Prop) : P -> decb P = true.
Proof. apply decb_spec. Qed.
Lemma decb_false (P : Prop) : ~ P -> decb P = false.
Proof. intros h. destruct (decb P) eqn:E; [exfalso; apply h, decb_spec, E | reflexivity]. Qed.

(** * Part I. The specification *)

(** In the comments of this part, [Γ.A] is [ext Γ A], [A[σ]] is [sub A σ] and
    [t[σ]] is [subTm t σ], [p] is [pp A], [q] is [qq A], [⟨σ, t⟩] is [pair σ t],
    [σ⁺] is [wk σ A], and [B[t]] is [sub B (sec t)], the substitution along
    [⟨id, t⟩]. Transports along equations between types are left implicit, as in
    the paper. *)

(** ** The category with families *)

Record CwF := {
  (** Contexts and context morphisms form a category. *)
  Ctx : Type;
  Hom : Ctx -> Ctx -> Type;
  idH : forall Γ, Hom Γ Γ;
  comp : forall {Θ Δ Γ}, Hom Δ Γ -> Hom Θ Δ -> Hom Θ Γ;
  (** [id ∘ σ = σ] *)
  id_comp : forall {Δ Γ} (σ : Hom Δ Γ), comp (idH Γ) σ = σ;
  (** [σ ∘ id = σ] *)
  comp_id : forall {Δ Γ} (σ : Hom Δ Γ), comp σ (idH Δ) = σ;
  (** [(σ ∘ δ) ∘ ε = σ ∘ (δ ∘ ε)] *)
  comp_assoc : forall {Ξ Θ Δ Γ} (σ : Hom Δ Γ) (δ : Hom Θ Δ) (ε : Hom Ξ Θ),
    comp (comp σ δ) ε = comp σ (comp δ ε);
  (** The empty context [⋄] is terminal. *)
  empty : Ctx;
  toEmpty : forall Γ, Hom Γ empty;
  toEmpty_unique : forall {Γ} (σ : Hom Γ empty), σ = toEmpty Γ;
  (** Types [Γ ⊢ A] and terms [Γ ⊢ t : A]. *)
  Ty : Ctx -> Type;
  Tm : forall Γ, Ty Γ -> Type;
  (** Substitution [A[σ]] and [t[σ] : A[σ]]. *)
  sub : forall {Δ Γ}, Ty Γ -> Hom Δ Γ -> Ty Δ;
  subTm : forall {Δ Γ} {A : Ty Γ}, Tm Γ A -> forall σ : Hom Δ Γ, Tm Δ (sub A σ);
  (** [A[id] = A] *)
  ty_sub_id : forall {Γ} (A : Ty Γ), sub A (idH Γ) = A;
  (** [A[σ ∘ δ] = A[σ][δ]] *)
  ty_sub_comp : forall {Θ Δ Γ} (A : Ty Γ) (σ : Hom Δ Γ) (δ : Hom Θ Δ),
    sub A (comp σ δ) = sub (sub A σ) δ;
  (** [t[id] = t] *)
  tm_sub_id : forall {Γ} {A : Ty Γ} (t : Tm Γ A), tr (Tm Γ) (ty_sub_id A) (subTm t (idH Γ)) = t;
  (** [t[σ ∘ δ] = t[σ][δ]] *)
  tm_sub_comp : forall {Θ Δ Γ} {A : Ty Γ} (t : Tm Γ A) (σ : Hom Δ Γ) (δ : Hom Θ Δ),
    tr (Tm Θ) (ty_sub_comp A σ δ) (subTm t (comp σ δ)) = subTm (subTm t σ) δ;
  (** Context extension [Γ.A], with [p : Γ.A → Γ] and [q : A[p]] over [Γ.A]. *)
  ext : forall Γ, Ty Γ -> Ctx;
  pp : forall {Γ} (A : Ty Γ), Hom (ext Γ A) Γ;
  qq : forall {Γ} (A : Ty Γ), Tm (ext Γ A) (sub A (pp A));
  (** [⟨σ, t⟩ : Δ → Γ.A], for [σ : Δ → Γ] and [t : A[σ]] over [Δ]. *)
  pair : forall {Δ Γ} {A : Ty Γ} (σ : Hom Δ Γ), Tm Δ (sub A σ) -> Hom Δ (ext Γ A);
  (** [p ∘ ⟨σ, t⟩ = σ] *)
  pair_proj : forall {Δ Γ} {A : Ty Γ} (σ : Hom Δ Γ) (t : Tm Δ (sub A σ)),
    comp (pp A) (pair σ t) = σ;
  (** [q[⟨σ, t⟩] = t] *)
  pair_var : forall {Δ Γ} {A : Ty Γ} (σ : Hom Δ Γ) (t : Tm Δ (sub A σ)),
    tr (Tm Δ) (cat (inv (ty_sub_comp A (pp A) (pair σ t))) (ap (fun s => sub A s) (pair_proj σ t)))
      (subTm (qq A) (pair σ t)) = t;
  (** [⟨p ∘ τ, q[τ]⟩ = τ] *)
  pair_eta : forall {Δ Γ} {A : Ty Γ} (τ : Hom Δ (ext Γ A)),
    pair (comp (pp A) τ) (tr (Tm Δ) (inv (ty_sub_comp A (pp A) τ)) (subTm (qq A) τ)) = τ
}.

Arguments Hom {c} _ _. Arguments idH {c} _. Arguments comp {c Θ Δ Γ} _ _.
Arguments id_comp {c Δ Γ} _. Arguments comp_id {c Δ Γ} _. Arguments comp_assoc {c Ξ Θ Δ Γ} _ _ _.
Arguments toEmpty {c} _. Arguments toEmpty_unique {c Γ} _.
Arguments Ty {c} _. Arguments Tm {c} _ _. Arguments sub {c Δ Γ} _ _.
Arguments subTm {c Δ Γ A} _ _. Arguments ty_sub_id {c Γ} _. Arguments ty_sub_comp {c Θ Δ Γ} _ _ _.
Arguments tm_sub_id {c Γ A} _. Arguments tm_sub_comp {c Θ Δ Γ A} _ _ _.
Arguments ext {c} _ _. Arguments pp {c Γ} _. Arguments qq {c Γ} _.
Arguments pair {c Δ Γ A} _ _. Arguments pair_proj {c Δ Γ A} _ _. Arguments pair_var {c Δ Γ A} _ _.
Arguments pair_eta {c Δ Γ A} _.

(** Notation for the operations of a CwF, following the paper: [Δ ⟶ Γ] for [Hom Δ Γ],
    [σ ∘ δ] for [comp σ δ], [Γ ▹ A] for the context extension [Γ.A], [A[σ]] for the
    substitution [sub A σ] of a type, [t[σ]ₜ] for the substitution [subTm t σ] of a term, and
    [⟨σ, t⟩] for [pair σ t]. *)
Notation "Δ ⟶ Γ" := (Hom Δ Γ) (at level 90, no associativity).
Notation "σ ∘ δ" := (comp σ δ) (at level 40, left associativity).
Notation "Γ ▹ A" := (ext Γ A) (at level 50, left associativity).
Notation "A [ σ ]" := (sub A σ) (at level 3, left associativity, format "A [ σ ]").
Notation "t [ σ ]ₜ" := (subTm t σ) (at level 3, left associativity, format "t [ σ ]ₜ").
Notation "⟨ σ , t ⟩" := (pair σ t) (format "⟨ σ ,  t ⟩").

Section Spec.
Context {C : CwF}.

(** Transports of terms along equations of types, and of types and terms over a
    context extension along an equation of the extending types. *)
Definition trTm {Γ : Ctx C} {A B : Ty Γ} (e : A = B) (t : Tm Γ A) : Tm Γ B := tr (Tm Γ) e t.
Definition trTy {Γ : Ctx C} {X Y : Ty Γ} (e : X = Y) (F : Ty (Γ ▹ X)) : Ty (Γ ▹ Y) :=
  tr (fun Z => Ty (Γ ▹ Z)) e F.
Definition trD {Γ : Ctx C} {X Y : Ty Γ} (e : X = Y) {F : Ty (Γ ▹ X)} (t : Tm (Γ ▹ X) F) :
    Tm (Γ ▹ Y) (trTy e F) :=
  match e as e0 in _ = Y0 return Tm (Γ ▹ Y0) (trTy e0 F) with eq_refl => t end.

(** The weakening [σ⁺ : Δ.A[σ] → Γ.A], the section [⟨id, t⟩], and
    [(γ, a, b) ↦ (γ, b)]. *)
Definition wk {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (A : Ty Γ) : Δ ▹ A[σ] ⟶ Γ ▹ A :=
  ⟨σ ∘ pp (A[σ]), trTm (inv (ty_sub_comp A σ (pp (A[σ])))) (qq (A[σ]))⟩.
Definition sec {Γ : Ctx C} {A : Ty Γ} (t : Tm Γ A) : Γ ⟶ Γ ▹ A :=
  ⟨idH Γ, trTm (inv (ty_sub_id A)) t⟩.
Definition snd2 {Γ : Ctx C} (A : Ty Γ) : Γ ▹ A ▹ A[pp A] ⟶ Γ ▹ A :=
  ⟨pp A ∘ pp (A[pp A]), trTm (inv (ty_sub_comp A (pp A) (pp _))) (qq (A[pp A]))⟩.

(** Weakening commutes with substitution: [B[p][σ⁺] = B[σ][p]]. *)
Definition e_pwk {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (A B : Ty Γ) :
    B[pp A][wk σ A] = B[σ][pp (A[σ])] :=
  cat (cat (inv (ty_sub_comp B (pp A) (wk σ A))) (ap (fun s => B[s]) (pair_proj _ _)))
    (ty_sub_comp B σ (pp (A[σ]))).
Definition e_snd2 {Γ : Ctx C} (A B : Ty Γ) :
    B[pp A][snd2 A] = B[pp A][pp (A[pp A])] :=
  cat (cat (inv (ty_sub_comp B (pp A) (snd2 A))) (ap (fun s => B[s]) (pair_proj _ _)))
    (ty_sub_comp B (pp A) (pp (A[pp A]))).

(** Derived equations of the CwF. A field below that states a law along an equation of
    types defines that equation by [let e : … := … in], from the fields of the CwF and the
    earlier fields of the record, using the following lemmas. A comment above each [let]
    states the equation in the notation of the paper. Each is a substitution law that holds
    in every CwF with the given formers, and Rocq checks it where the [let] defines it. *)

(** [q[τ[σ]] ≃ q[τ][σ]], [q[⟨σ, t⟩] ≃ t], and [x ≃ y] implies [x[σ] ≃ y[σ]]. *)
Lemma tsc_treq {Θ Δ Γ : Ctx C} {A : Ty Γ} (t : Tm Γ A) (σ : Δ ⟶ Γ) (δ : Θ ⟶ Δ) :
  treq (Tm Θ) (t[σ ∘ δ]ₜ) (t[σ]ₜ[δ]ₜ).
Proof. exists (ty_sub_comp A σ δ). exact (tm_sub_comp t σ δ). Qed.
Lemma pv_treq {Δ Γ : Ctx C} {A : Ty Γ} (σ : Δ ⟶ Γ) (t : Tm Δ (A[σ])) :
  treq (Tm Δ) ((qq A)[⟨σ, t⟩]ₜ) t.
Proof. eexists. exact (pair_var σ t). Qed.
Lemma sub_treq {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) {X Y : Ty Γ} {x : Tm Γ X} {y : Tm Γ Y} :
  treq (Tm Γ) x y -> treq (Tm Δ) (x[σ]ₜ) (y[σ]ₜ).
Proof. exact (treq_ap (Tm Γ) (Tm Δ) (fun Z => Z[σ]) (fun Z z => z[σ]ₜ)). Qed.
Lemma subTm_hom {Δ Γ : Ctx C} {A : Ty Γ} (t : Tm Γ A) {f g : Δ ⟶ Γ} (e : f = g) :
  treq (Tm Δ) (t[f]ₜ) (t[g]ₜ).
Proof. destruct e. exists eq_refl. reflexivity. Qed.

(** Morphisms into [Γ.A] with equal components are equal: [p ∘ τ₁ = p ∘ τ₂] and
    [q[τ₁] ≃ q[τ₂]] imply [τ₁ = τ₂]. *)
Lemma hom_ext {Δ Γ : Ctx C} {A : Ty Γ} (τ1 τ2 : Δ ⟶ Γ ▹ A) (e : pp A ∘ τ1 = pp A ∘ τ2) :
  treq (Tm Δ) ((qq A)[τ1]ₜ) ((qq A)[τ2]ₜ) -> τ1 = τ2.
Proof.
  intros h. refine (cat (inv (pair_eta τ1)) (cat _ (pair_eta τ2))).
  apply (ap_dep (fun f => Tm Δ (A[f])) (fun f u => ⟨f, u⟩)). exists e.
  refine (cat (tr_ap (Tm Δ) (fun f => A[f]) e _) (treq_tr_eq _ _ _ _ _)).
  eapply treq_trans; [apply treq_sym, treq_tr|]. eapply treq_trans; [exact h|]. apply treq_tr.
Qed.

(** [⟨id, t⟩ ∘ σ = σ⁺ ∘ ⟨id, t[σ]⟩], and hence [C[t][σ] = C[σ⁺][t[σ]]]. *)
Lemma comp_sec {Δ Γ : Ctx C} {A : Ty Γ} (t : Tm Γ A) (σ : Δ ⟶ Γ) :
  sec t ∘ σ = wk σ A ∘ sec (t[σ]ₜ).
Proof.
  refine (hom_ext _ _ (cat (cat (inv (comp_assoc (pp A) (sec t) σ))
    (cat (ap (fun f => f ∘ σ) (pair_proj (idH Γ) (trTm (inv (ty_sub_id A)) t))) (id_comp σ)))
    (inv (cat (inv (comp_assoc (pp A) (wk σ A) (sec (t[σ]ₜ))))
      (cat (ap (fun f => f ∘ sec (t[σ]ₜ)) (pair_proj _ _))
        (cat (comp_assoc σ (pp (A[σ])) (sec (t[σ]ₜ)))
          (cat (ap (fun f => σ ∘ f) (pair_proj (idH Δ) (trTm (inv (ty_sub_id (A[σ]))) (t[σ]ₜ))))
            (comp_id σ))))))) _).
  eapply treq_trans; [apply tsc_treq|]. eapply treq_trans; [apply sub_treq, pv_treq|].
  eapply treq_trans; [apply sub_treq, treq_sym, treq_tr|].
  eapply treq_trans; [|apply treq_sym, tsc_treq].
  eapply treq_trans; [|apply sub_treq, treq_sym, pv_treq].
  eapply treq_trans; [|apply sub_treq, treq_tr].
  eapply treq_trans; [|apply treq_sym, pv_treq]. apply treq_tr.
Qed.
Definition e_sec {Δ Γ : Ctx C} {A : Ty Γ} (B : Ty (Γ ▹ A)) (t : Tm Γ A) (σ : Δ ⟶ Γ) :
    B[sec t][σ] = B[wk σ A][sec (t[σ]ₜ)] :=
  cat (inv (ty_sub_comp B (sec t) σ))
    (cat (ap (fun f => B[f]) (comp_sec t σ)) (ty_sub_comp B (wk σ A) (sec (t[σ]ₜ)))).

(** ** Π, Σ and the finite types *)

Record PiF := {
  (** [Π(A, B)], for [B] over [Γ.A]. *)
  Pi : forall {Γ} (A : Ty Γ), Ty (Γ ▹ A) -> Ty Γ;
  (** [Π(A, B)[σ] = Π(A[σ], B[σ⁺])] *)
  pi_sub : forall {Δ Γ} (A : Ty Γ) (B : Ty (Γ ▹ A)) (σ : Δ ⟶ Γ),
    (Pi A B)[σ] = Pi (A[σ]) (B[wk σ A]);
  (** [λ : Tm(Γ.A, B) → Tm(Γ, Π(A, B))] and [app] in the other direction. *)
  lam : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)}, Tm (Γ ▹ A) B -> Tm Γ (Pi A B);
  app : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)}, Tm Γ (Pi A B) -> Tm (Γ ▹ A) B;
  (** [app (λ t) = t] *)
  pi_beta : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)} (t : Tm (Γ ▹ A) B), app (lam t) = t;
  (** [λ (app s) = s] *)
  pi_eta : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)} (s : Tm Γ (Pi A B)), lam (app s) = s;
  (** [(λ t)[σ] = λ (t[σ⁺])] *)
  lam_sub : forall {Δ Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)} (t : Tm (Γ ▹ A) B) (σ : Δ ⟶ Γ),
    trTm (pi_sub A B σ) ((lam t)[σ]ₜ) = lam (t[wk σ A]ₜ)
}.

Record SigmaF := {
  (** [Σ(A, B)], for [B] over [Γ.A]. *)
  Sigma : forall {Γ} (A : Ty Γ), Ty (Γ ▹ A) -> Ty Γ;
  (** [Σ(A, B)[σ] = Σ(A[σ], B[σ⁺])] *)
  sigma_sub : forall {Δ Γ} (A : Ty Γ) (B : Ty (Γ ▹ A)) (σ : Δ ⟶ Γ),
    (Sigma A B)[σ] = Sigma (A[σ]) (B[wk σ A]);
  (** [⟨t, u⟩ : Σ(A, B)] for [t : A] and [u : B[t]], and the projections [π₁], [π₂]. *)
  spair : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)} (t : Tm Γ A),
    Tm Γ (B[sec t]) -> Tm Γ (Sigma A B);
  sfst : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)}, Tm Γ (Sigma A B) -> Tm Γ A;
  ssnd : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)} (s : Tm Γ (Sigma A B)),
    Tm Γ (B[sec (sfst s)]);
  (** [π₁ ⟨t, u⟩ = t] *)
  sigma_fst : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)} (t : Tm Γ A) (u : Tm Γ (B[sec t])),
    sfst (spair t u) = t;
  (** [π₂ ⟨t, u⟩ = u] *)
  sigma_snd : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)} (t : Tm Γ A) (u : Tm Γ (B[sec t])),
    trTm (ap (fun x => B[sec x]) (sigma_fst t u)) (ssnd (spair t u)) = u;
  (** [⟨π₁ s, π₂ s⟩ = s] *)
  sigma_eta : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)} (s : Tm Γ (Sigma A B)),
    spair (sfst s) (ssnd s) = s;
  (** [⟨t, u⟩[σ] = ⟨t[σ], u[σ]⟩] *)
  spair_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) {A : Ty Γ} {B : Ty (Γ ▹ A)} (t : Tm Γ A)
    (u : Tm Γ (B[sec t])),
    (* [e : B[t][σ] = B[σ⁺][t[σ]]], the equation of the types of [u[σ]] *)
    let e : B[sec t][σ] = B[wk σ A][sec (t[σ]ₜ)] := e_sec B t σ in
    trTm (sigma_sub A B σ) ((spair t u)[σ]ₜ) = spair (t[σ]ₜ) (trTm e (u[σ]ₜ));
  (** [(π₁ s)[σ] = π₁ (s[σ])] *)
  sfst_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) {A : Ty Γ} {B : Ty (Γ ▹ A)} (s : Tm Γ (Sigma A B)),
    (sfst s)[σ]ₜ = sfst (trTm (sigma_sub A B σ) (s[σ]ₜ));
  (** [(π₂ s)[σ] = π₂ (s[σ])] *)
  ssnd_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) {A : Ty Γ} {B : Ty (Γ ▹ A)} (s : Tm Γ (Sigma A B)),
    (* [e : B[π₁ s][σ] = B[σ⁺][π₁ (s[σ])]] *)
    let e : B[sec (sfst s)][σ]
            = B[wk σ A][sec (sfst (trTm (sigma_sub A B σ) (s[σ]ₜ)))] :=
      cat (e_sec B (sfst s) σ) (ap (fun x => B[wk σ A][sec x]) (sfst_sub σ s)) in
    trTm e ((ssnd s)[σ]ₜ) = ssnd (trTm (sigma_sub A B σ) (s[σ]ₜ))
}.

Record FinF := {
  (** The empty type [0]. *)
  zero : forall Γ, Ty Γ;
  (** [0[σ] = 0] *)
  zero_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), (zero Γ)[σ] = zero Δ;
  (** [elim C t : C[t]], for [C] over [Γ.0] and [t : 0]. *)
  zero_elim : forall {Γ} (Cm : Ty (Γ ▹ zero Γ)) (t : Tm Γ (zero Γ)), Tm Γ (Cm[sec t]);
  (** [(elim C t)[σ] = elim (C[σ⁺]) (t[σ])] *)
  zero_elim_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (Cm : Ty (Γ ▹ zero Γ)) (t : Tm Γ (zero Γ)),
    (* [e : C[t][σ] = C[σ⁺][t[σ]]], along [0[σ] = 0] *)
    let e : Cm[sec t][σ]
            = (trTy (zero_sub σ) (Cm[wk σ (zero Γ)]))[sec (trTm (zero_sub σ) (t[σ]ₜ))] :=
      cat (e_sec Cm t σ)
        (inv (tr_app2 (fun Z => Ty (Δ ▹ Z)) (Tm Δ) (fun Z (X : Ty (Δ ▹ Z)) (u : Tm Δ Z) => X[sec u])
          (zero_sub σ) (Cm[wk σ (zero Γ)]) (t[σ]ₜ))) in
    trTm e ((zero_elim Cm t)[σ]ₜ)
    = zero_elim (trTy (zero_sub σ) (Cm[wk σ (zero Γ)])) (trTm (zero_sub σ) (t[σ]ₜ));
  (** The unit type [1], with [⋆ : 1]. *)
  one : forall Γ, Ty Γ;
  (** [1[σ] = 1] *)
  one_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), (one Γ)[σ] = one Δ;
  star : forall Γ, Tm Γ (one Γ);
  (** [⋆[σ] = ⋆] *)
  star_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), trTm (one_sub σ) ((star Γ)[σ]ₜ) = star Δ;
  (** [t = ⋆] for every [t : 1] *)
  one_eta : forall {Γ} (t : Tm Γ (one Γ)), t = star Γ;
  (** The type [2], with [tt, ff : 2]. *)
  two : forall Γ, Ty Γ;
  (** [2[σ] = 2] *)
  two_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), (two Γ)[σ] = two Δ;
  ttT : forall Γ, Tm Γ (two Γ);
  ffT : forall Γ, Tm Γ (two Γ);
  (** [tt[σ] = tt] *)
  tt_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), trTm (two_sub σ) ((ttT Γ)[σ]ₜ) = ttT Δ;
  (** [ff[σ] = ff] *)
  ff_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), trTm (two_sub σ) ((ffT Γ)[σ]ₜ) = ffT Δ;
  (** [if C c_tt c_ff b : C[b]], for [C] over [Γ.2], [c_tt : C[tt]] and [c_ff : C[ff]]. *)
  two_elim : forall {Γ} (Cm : Ty (Γ ▹ two Γ)),
    Tm Γ (Cm[sec (ttT Γ)]) -> Tm Γ (Cm[sec (ffT Γ)]) ->
    forall b : Tm Γ (two Γ), Tm Γ (Cm[sec b]);
  (** [if C c_tt c_ff tt = c_tt] *)
  two_elim_tt : forall {Γ} (Cm : Ty (Γ ▹ two Γ)) (ct : Tm Γ (Cm[sec (ttT Γ)]))
    (cf : Tm Γ (Cm[sec (ffT Γ)])), two_elim Cm ct cf (ttT Γ) = ct;
  (** [if C c_tt c_ff ff = c_ff] *)
  two_elim_ff : forall {Γ} (Cm : Ty (Γ ▹ two Γ)) (ct : Tm Γ (Cm[sec (ttT Γ)]))
    (cf : Tm Γ (Cm[sec (ffT Γ)])), two_elim Cm ct cf (ffT Γ) = cf;
  (** [(if C c_tt c_ff b)[σ] = if (C[σ⁺]) (c_tt[σ]) (c_ff[σ]) (b[σ])] *)
  two_elim_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (Cm : Ty (Γ ▹ two Γ))
    (ct : Tm Γ (Cm[sec (ttT Γ)])) (cf : Tm Γ (Cm[sec (ffT Γ)])) (b : Tm Γ (two Γ)),
    (* [e1 : C[tt][σ] = C[σ⁺][tt]], [e2 : C[ff][σ] = C[σ⁺][ff]] and [e3 : C[b][σ] = C[σ⁺][b[σ]]],
       along [2[σ] = 2] *)
    let e1 : Cm[sec (ttT Γ)][σ] = (trTy (two_sub σ) (Cm[wk σ (two Γ)]))[sec (ttT Δ)] :=
      cat (e_sec Cm (ttT Γ) σ)
        (cat (inv (tr_app2 (fun Z => Ty (Δ ▹ Z)) (Tm Δ) (fun Z (X : Ty (Δ ▹ Z)) (u : Tm Δ Z) => X[sec u])
               (two_sub σ) (Cm[wk σ (two Γ)]) ((ttT Γ)[σ]ₜ)))
          (ap (fun x => (trTy (two_sub σ) (Cm[wk σ (two Γ)]))[sec x]) (tt_sub σ))) in
    let e2 : Cm[sec (ffT Γ)][σ] = (trTy (two_sub σ) (Cm[wk σ (two Γ)]))[sec (ffT Δ)] :=
      cat (e_sec Cm (ffT Γ) σ)
        (cat (inv (tr_app2 (fun Z => Ty (Δ ▹ Z)) (Tm Δ) (fun Z (X : Ty (Δ ▹ Z)) (u : Tm Δ Z) => X[sec u])
               (two_sub σ) (Cm[wk σ (two Γ)]) ((ffT Γ)[σ]ₜ)))
          (ap (fun x => (trTy (two_sub σ) (Cm[wk σ (two Γ)]))[sec x]) (ff_sub σ))) in
    let e3 : Cm[sec b][σ]
             = (trTy (two_sub σ) (Cm[wk σ (two Γ)]))[sec (trTm (two_sub σ) (b[σ]ₜ))] :=
      cat (e_sec Cm b σ)
        (inv (tr_app2 (fun Z => Ty (Δ ▹ Z)) (Tm Δ) (fun Z (X : Ty (Δ ▹ Z)) (u : Tm Δ Z) => X[sec u])
          (two_sub σ) (Cm[wk σ (two Γ)]) (b[σ]ₜ))) in
    trTm e3 ((two_elim Cm ct cf b)[σ]ₜ)
    = two_elim (trTy (two_sub σ) (Cm[wk σ (two Γ)])) (trTm e1 (ct[σ]ₜ))
        (trTm e2 (cf[σ]ₜ)) (trTm (two_sub σ) (b[σ]ₜ))
}.

(** The eliminator of [1], derived from the η-law. *)
Definition one_elim (F : FinF) {Γ} (Cm : Ty (Γ ▹ one F Γ)) (c : Tm Γ (Cm[sec (star F Γ)]))
    (t : Tm Γ (one F Γ)) : Tm Γ (Cm[sec t]) :=
  tr (fun x => Tm Γ (Cm[sec x])) (inv (one_eta F t)) c.

Lemma one_elim_star (F : FinF) {Γ} (Cm : Ty (Γ ▹ one F Γ)) (c : Tm Γ (Cm[sec (star F Γ)])) :
  one_elim F Cm c (star F Γ) = c.
Proof. unfold one_elim. rw (proof_irrel (inv (one_eta F (star F Γ))) eq_refl). reflexivity. Qed.

(** ** W-types *)

Section W.
Context (P : PiF) {Γ : Ctx C} (A : Ty Γ) (B : Ty (Γ ▹ A)) (Wt : Ty Γ).

(** [Γ, a : A ⊢ Π(b : B a). W], the context [Γ, a, f] of [sup], and its type. *)
Definition wF : Ty (Γ ▹ A) := Pi P B (Wt[pp A][pp B]).
Definition wCtx2 : Ctx C := Γ ▹ A ▹ wF.
Definition wSupTy : Ty wCtx2 := Wt[pp A][pp wF].

(** [(γ, a, f) ↦ (γ, sup a f)]. *)
Definition wSupMap (sup : Tm wCtx2 wSupTy) : wCtx2 ⟶ Γ ▹ Wt :=
  ⟨pp A ∘ pp wF, trTm (inv (ty_sub_comp Wt (pp A) (pp wF))) sup⟩.

(** [(γ, a, f, b) ↦ (γ, f b)]. *)
Definition wRho : wCtx2 ▹ B[pp wF] ⟶ Γ ▹ Wt :=
  ⟨pp A ∘ pp B ∘ wk (pp wF) B, trTm (inv (cat (ty_sub_comp Wt (pp A ∘ pp B) (wk (pp wF) B))
                    (ap (fun X => X[wk (pp wF) B]) (ty_sub_comp Wt (pp A) (pp B)))))
      (app P (trTm (pi_sub P B (Wt[pp A][pp B]) (pp wF)) (qq wF)))⟩.

(** [Γ, a, f ⊢ Π(b : B a). C (f b)] and [Γ, a, f, g ⊢ C (sup a f)]. *)
Definition wIH (Cm : Ty (Γ ▹ Wt)) : Ty wCtx2 := Pi P (B[pp wF]) (Cm[wRho]).
Definition wMinorTy (Cm : Ty (Γ ▹ Wt)) (sup : Tm wCtx2 wSupTy) : Ty (wCtx2 ▹ wIH Cm) :=
  Cm[wSupMap sup ∘ pp (wIH Cm)].
(** [Π(a : A). Π(f : Π(b : B a). W). Π(g : Π(b : B a). C (f b)). C (sup a f)]. *)
Definition wMinorPi (Cm : Ty (Γ ▹ Wt)) (sup : Tm wCtx2 wSupTy) : Ty Γ :=
  Pi P A (Pi P wF (Pi P (wIH Cm) (wMinorTy Cm sup))).

(** [C[S ∘ p][⟨id, g⟩] = C[S]] for the step type, where [S = (γ, a, f) ↦ (γ, sup a f)]. *)
Definition e_minor (Cm : Ty (Γ ▹ Wt)) (sup : Tm wCtx2 wSupTy) (g : Tm wCtx2 (wIH Cm)) :
    (wMinorTy Cm sup)[sec g] = Cm[wSupMap sup] :=
  cat (inv (ty_sub_comp Cm (wSupMap sup ∘ pp (wIH Cm)) (sec g)))
    (ap (fun f => Cm[f]) (cat (comp_assoc (wSupMap sup) (pp (wIH Cm)) (sec g))
      (cat (ap (fun f => wSupMap sup ∘ f) (pair_proj (idH _) _)) (comp_id (wSupMap sup))))).

End W.

(** For [W[σ] = W']: [(Π(b : B a). W)[σ⁺] = Π(b : B[σ⁺] a). W'] and [W[p][p][σ⁺⁺] = W'[p][p]]. *)
Definition e_wF (P : PiF) {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) {W : Ty Γ}
    {W' : Ty Δ} (ew : W[σ] = W') : (wF P A B W)[wk σ A] = wF P (A[σ]) (B[wk σ A]) W' :=
  cat (pi_sub P B (W[pp A][pp B]) (wk σ A))
    (ap (fun Y => Pi P (B[wk σ A]) Y)
      (cat (e_pwk (wk σ A) B (W[pp A]))
        (ap (fun Y => Y[pp (B[wk σ A])]) (cat (e_pwk σ A W) (ap (fun Y => Y[pp (A[σ])]) ew))))).
Definition e_wSupTy (P : PiF) {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) {W : Ty Γ}
    {W' : Ty Δ} (ew : W[σ] = W') :
    trTy (e_wF P σ A B ew) ((wSupTy P A B W)[wk (wk σ A) (wF P A B W)])
    = wSupTy P (A[σ]) (B[wk σ A]) W' :=
  cat (ap (trTy (e_wF P σ A B ew))
        (cat (e_pwk (wk σ A) (wF P A B W) (W[pp A]))
          (ap (fun Y => Y[pp ((wF P A B W)[wk σ A])])
            (cat (e_pwk σ A W) (ap (fun Y => Y[pp (A[σ])]) ew)))))
    (tr_apD (fun Z => Ty (Δ ▹ A[σ] ▹ Z)) (fun Z => (W'[pp (A[σ])])[pp Z])
      (e_wF P σ A B ew)).

(** Weakening along an equation [e : X[τ] = X']: [τ⁺ₑ = ⟨τ ∘ p, q⟩ : Δ.X' → Γ.X], with
    [Y[τ⁺]] transported along [e] equal to [Y[τ⁺ₑ]], and likewise for terms. *)
Definition wkE {Δ Γ : Ctx C} (τ : Δ ⟶ Γ) (X : Ty Γ) {X' : Ty Δ} (e : X[τ] = X') :
    Δ ▹ X' ⟶ Γ ▹ X :=
  ⟨τ ∘ pp X', trTm (cat (ap (fun Y => Y[pp X']) (inv e)) (inv (ty_sub_comp X τ (pp X')))) (qq X')⟩.
Lemma wkE_refl {Δ Γ : Ctx C} (τ : Δ ⟶ Γ) (X : Ty Γ) : wkE τ X (eq_refl (X[τ])) = wk τ X.
Proof.
  unfold wkE, wk, trTm. apply (ap (fun x => ⟨τ ∘ pp (X[τ]), x⟩)).
  apply (ap (fun e => tr (Tm _) e (qq (X[τ])))). apply proof_irrel.
Qed.
Lemma trTy_wk {Δ Γ : Ctx C} (τ : Δ ⟶ Γ) (X : Ty Γ) {X' : Ty Δ} (e : X[τ] = X') (Y : Ty (Γ ▹ X)) :
  trTy e (Y[wk τ X]) = Y[wkE τ X e].
Proof. destruct e. rw (wkE_refl τ X). reflexivity. Qed.
Lemma tm_wk {Δ Γ : Ctx C} (τ : Δ ⟶ Γ) (X : Ty Γ) {X' : Ty Δ} (e : X[τ] = X') {Y : Ty (Γ ▹ X)}
    (t : Tm (Γ ▹ X) Y) : treq (Tm (Δ ▹ X')) (t[wkE τ X e]ₜ) (trD e (t[wk τ X]ₜ)).
Proof. destruct e. rw (wkE_refl τ X). exists eq_refl. reflexivity. Qed.
Lemma wkE_q {Δ Γ : Ctx C} (τ : Δ ⟶ Γ) (X : Ty Γ) {X' : Ty Δ} (e : X[τ] = X') :
  treq (Tm (Δ ▹ X')) ((qq X)[wkE τ X e]ₜ) (qq X').
Proof. eapply treq_trans; [apply pv_treq | apply treq_sym, treq_tr]. Qed.

(** Naturality of application, from [lam_sub], β and η: [(app s)[δ⁺] = app (s[δ])], and its
    form along an equation [X[δ] = X']. *)
Lemma app_sub (P : PiF) {Δ Γ : Ctx C} (δ : Δ ⟶ Γ) {X : Ty Γ} {Y : Ty (Γ ▹ X)} (s : Tm Γ (Pi P X Y)) :
  (app P s)[wk δ X]ₜ = app P (trTm (pi_sub P X Y δ) (s[δ]ₜ)).
Proof.
  exact (inv (cat (ap (fun s0 => app P (trTm (pi_sub P X Y δ) (s0[δ]ₜ))) (inv (pi_eta P s)))
    (cat (ap (app P) (lam_sub P (app P s) δ)) (pi_beta P _)))).
Qed.
Definition e_piE (P : PiF) {Δ Γ : Ctx C} (δ : Δ ⟶ Γ) (X : Ty Γ) (Y : Ty (Γ ▹ X)) {X' : Ty Δ}
    (e : X[δ] = X') : (Pi P X Y)[δ] = Pi P X' (trTy e (Y[wk δ X])) :=
  cat (pi_sub P X Y δ)
    (ap_dep (fun Z => Ty (Δ ▹ Z)) (fun Z W => Pi P Z W) (treq_tr (fun Z => Ty (Δ ▹ Z)) e (Y[wk δ X]))).
Lemma app_subE (P : PiF) {Δ Γ : Ctx C} (δ : Δ ⟶ Γ) {X : Ty Γ} {Y : Ty (Γ ▹ X)} {X' : Ty Δ}
    (e : X[δ] = X') (s : Tm Γ (Pi P X Y)) :
  treq (Tm (Δ ▹ X')) ((app P s)[wkE δ X e]ₜ) (app P (trTm (e_piE P δ X Y e) (s[δ]ₜ))).
Proof.
  destruct e. rw (wkE_refl δ X). rw (app_sub P δ s). exists eq_refl.
  exact (ap (fun e => app P (tr (Tm Δ) e (s[δ]ₜ))) (proof_irrel _ _)).
Qed.

(** For [W[σ] = W'] and [sup[σ⁺⁺] = sup'] along the equations of [e_wF] and [e_wSupTy]:
    [(Π(a : A). Π(f : Π(b : B a). W). Π(g : Π(b : B a). C(f b)). C(sup a f))[σ] = the same with
    [A[σ]], [B[σ⁺]], [W'], [C[σ⁺]] and [sup']. *)
Lemma e_wMinorPi (P : PiF) {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)) {W : Ty Γ}
    {W' : Ty Δ} (ew : W[σ] = W') (Cm : Ty (Γ ▹ W)) (sup : Tm (wCtx2 P A B W) (wSupTy P A B W))
    (sup' : Tm (wCtx2 P (A[σ]) (B[wk σ A]) W') (wSupTy P (A[σ]) (B[wk σ A]) W'))
    (hsup : trTm (e_wSupTy P σ A B ew) (trD (e_wF P σ A B ew) (sup[wk (wk σ A) (wF P A B W)]ₜ))
            = sup') :
  (wMinorPi P A B W Cm sup)[σ]
  = wMinorPi P (A[σ]) (B[wk σ A]) W' (trTy ew (Cm[wk σ W])) sup'.
Proof.
  destruct ew.
  pose (A' := A[σ]). pose (τ := wk σ A). pose (B' := B[τ]). pose (W' := W[σ]).
  pose (F := wF P A B W). pose (F' := wF P A' B' W').
  pose (eF := e_wF P σ A B (eq_refl W') : F[τ] = F').
  pose (θ := wkE τ F eF).
  pose (S := wSupMap P A B W sup). pose (S' := wSupMap P A' B' W' sup').
  pose (ρ := wRho P A B W). pose (ρ' := wRho P A' B' W').
  pose (BF := B[pp F]). pose (B'F' := B'[pp F']).
  pose (eB := cat (inv (ty_sub_comp B (pp F) θ)) (cat (ap (fun f => B[f]) (pair_proj _ _))
                (ty_sub_comp B τ (pp F'))) : BF[θ] = B'F').
  pose (θB := wkE θ BF eB).
  (* [p ∘ p ∘ p ∘ ρ ∘ θB = σ ∘ p ∘ p ∘ p], both sides brought to [σ ∘ (p ∘ (p ∘ p))]. *)
  pose (NF := σ ∘ (pp A' ∘ (pp F' ∘ pp B'F'))).
  assert (NL : pp A ∘ (pp B ∘ (wk (pp F) B ∘ θB)) = NF).
  { refine (cat (ap (comp (pp A)) (inv (comp_assoc (pp B) (wk (pp F) B) θB))) _).
    refine (cat (ap (fun f => pp A ∘ (f ∘ θB)) (pair_proj _ _)) _).
    refine (cat (ap (comp (pp A)) (comp_assoc (pp F) (pp BF) θB)) _).
    refine (cat (ap (fun f => pp A ∘ (pp F ∘ f)) (pair_proj _ _)) _).
    refine (cat (ap (comp (pp A)) (inv (comp_assoc (pp F) θ (pp B'F')))) _).
    refine (cat (ap (fun f => pp A ∘ (f ∘ pp B'F')) (pair_proj _ _)) _).
    refine (cat (ap (comp (pp A)) (comp_assoc τ (pp F') (pp B'F'))) _).
    refine (cat (inv (comp_assoc (pp A) τ (pp F' ∘ pp B'F'))) _).
    refine (cat (ap (fun f => f ∘ (pp F' ∘ pp B'F')) (pair_proj _ _)) _).
    exact (comp_assoc σ (pp A') (pp F' ∘ pp B'F')). }
  assert (NR : σ ∘ (pp A' ∘ (pp B' ∘ wk (pp F') B')) = NF).
  { exact (ap (fun f => σ ∘ (pp A' ∘ f)) (pair_proj _ _)). }
  (* [ρ ∘ θB = σ⁺ ∘ ρ'] *)
  assert (M3 : ρ ∘ θB = wk σ W ∘ ρ').
  { apply hom_ext.
    - refine (cat (inv (comp_assoc (pp W) ρ θB)) _).
      refine (cat (ap (fun f => f ∘ θB) (pair_proj _ _)) _).
      refine (cat (comp_assoc (pp A ∘ pp B) (wk (pp F) B) θB) _).
      refine (cat (comp_assoc (pp A) (pp B) (wk (pp F) B ∘ θB)) _).
      refine (cat NL _). refine (inv _).
      refine (cat (inv (comp_assoc (pp W) (wk σ W) ρ')) _).
      refine (cat (ap (fun f => f ∘ ρ') (pair_proj _ _)) _).
      refine (cat (comp_assoc σ (pp W') ρ') _).
      refine (cat (ap (comp σ) (pair_proj _ _)) _).
      refine (cat (ap (comp σ) (comp_assoc (pp A') (pp B') (wk (pp F') B'))) _).
      exact NR.
    - pose (sF := trTm (pi_sub P B (W[pp A][pp B]) (pp F)) (qq F)).
      pose (sF' := trTm (pi_sub P B' (W'[pp A'][pp B']) (pp F')) (qq F')).
      pose (u1 := trTm (e_piE P θ BF (W[pp A][pp B][wk (pp F) B]) eB) (sF[θ]ₜ)).
      assert (eY : trTy eB (W[pp A][pp B][wk (pp F) B][wk θ BF])
                   = W'[pp A'][pp B'][wk (pp F') B']).
      { refine (cat (trTy_wk θ BF eB _) _).
        refine (cat (inv (ty_sub_comp _ (wk (pp F) B) θB)) _).
        refine (cat (inv (ty_sub_comp (W[pp A]) (pp B) (wk (pp F) B ∘ θB))) _).
        refine (cat (inv (ty_sub_comp W (pp A) (pp B ∘ (wk (pp F) B ∘ θB)))) _).
        refine (cat (ap (fun f => W[f]) (cat NL (inv NR))) _).
        refine (cat (ty_sub_comp W σ _) _).
        refine (cat (ty_sub_comp W' (pp A') _) _).
        exact (ty_sub_comp (W'[pp A']) (pp B') (wk (pp F') B')). }
      assert (hu : treq (Tm (Δ ▹ A' ▹ F')) u1 sF').
      { eapply treq_trans; [apply treq_sym, treq_tr|].
        eapply treq_trans; [apply sub_treq, treq_sym, treq_tr|].
        eapply treq_trans; [apply wkE_q | apply treq_tr]. }
      assert (ha : treq (Tm (Δ ▹ A' ▹ F' ▹ B'F')) (app P u1) (app P sF')).
      { refine (treq_ap (fun Y => Tm (Δ ▹ A' ▹ F') (Pi P B'F' Y)) (fun Y => Tm _ Y) (fun Y => Y)
                  (fun Y u => app P u) _).
        exists eY. refine (cat (tr_ap (Tm _) (fun Y => Pi P B'F' Y) eY u1) _).
        exact (treq_tr_eq _ _ _ _ hu). }
      eapply treq_trans; [apply tsc_treq|].
      eapply treq_trans; [apply sub_treq, pv_treq|].
      eapply treq_trans; [apply sub_treq, treq_sym, treq_tr|].
      eapply treq_trans; [apply app_subE|].
      eapply treq_trans; [exact ha|].
      eapply treq_trans; [|apply treq_sym, tsc_treq].
      eapply treq_trans; [|apply sub_treq, treq_sym, pv_treq].
      eapply treq_trans; [|apply sub_treq, treq_tr].
      eapply treq_trans; [|apply treq_sym, pv_treq].
      apply treq_tr. }
  (* [S ∘ θ = σ⁺ ∘ S'], by [sup_sub] *)
  assert (M2 : S ∘ θ = wk σ W ∘ S').
  { apply hom_ext.
    - refine (cat (inv (comp_assoc (pp W) S θ)) _).
      refine (cat (ap (fun f => f ∘ θ) (pair_proj _ _)) _).
      refine (cat (comp_assoc (pp A) (pp F) θ) _).
      refine (cat (ap (comp (pp A)) (pair_proj _ _)) _).
      refine (cat (inv (comp_assoc (pp A) τ (pp F'))) _).
      refine (cat (ap (fun f => f ∘ pp F') (pair_proj _ _)) _).
      refine (cat (comp_assoc σ (pp A') (pp F')) _). refine (inv _).
      refine (cat (inv (comp_assoc (pp W) (wk σ W) S')) _).
      refine (cat (ap (fun f => f ∘ S') (pair_proj _ _)) _).
      refine (cat (comp_assoc σ (pp W') S') _).
      exact (ap (comp σ) (pair_proj _ _)).
    - eapply treq_trans; [apply tsc_treq|].
      eapply treq_trans; [apply sub_treq, pv_treq|].
      eapply treq_trans; [apply sub_treq, treq_sym, treq_tr|].
      eapply treq_trans; [apply tm_wk|].
      eapply treq_trans; [exact (ex_intro _ _ hsup)|].
      eapply treq_trans; [|apply treq_sym, tsc_treq].
      eapply treq_trans; [|apply sub_treq, treq_sym, pv_treq].
      eapply treq_trans; [|apply sub_treq, treq_tr].
      eapply treq_trans; [|apply treq_sym, pv_treq].
      apply treq_tr. }
  pose (IH := wIH P A B W Cm). pose (IH' := wIH P A' B' W' (Cm[wk σ W])).
  assert (eIH : IH[θ] = IH').
  { refine (cat (pi_sub P BF (Cm[ρ]) θ) _).
    refine (ap_dep (fun Z => Ty (Δ ▹ A' ▹ F' ▹ Z)) (fun Z Y => Pi P Z Y) _).
    exists eB. refine (cat (trTy_wk θ BF eB (Cm[ρ])) _).
    exact (cat (inv (ty_sub_comp Cm ρ θB)) (cat (ap (fun f => Cm[f]) M3) (ty_sub_comp Cm (wk σ W) ρ'))). }
  pose (θI := wkE θ IH eIH).
  assert (M1 : S ∘ pp IH ∘ θI = wk σ W ∘ (S' ∘ pp IH')).
  { refine (cat (comp_assoc S (pp IH) θI) _).
    refine (cat (ap (comp S) (pair_proj _ _)) _).
    refine (cat (inv (comp_assoc S θ (pp IH'))) _).
    refine (cat (ap (fun f => f ∘ pp IH') M2) _).
    exact (comp_assoc (wk σ W) S' (pp IH')). }
  refine (cat (pi_sub P A _ σ) (ap (fun Y => Pi P A' Y) _)).
  refine (cat (pi_sub P F _ τ) _).
  refine (ap_dep (fun Z => Ty (Δ ▹ A' ▹ Z)) (fun Z Y => Pi P Z Y) _).
  exists eF. refine (cat (trTy_wk τ F eF _) _).
  refine (cat (pi_sub P IH _ θ) _).
  refine (ap_dep (fun Z => Ty (Δ ▹ A' ▹ F' ▹ Z)) (fun Z Y => Pi P Z Y) _).
  exists eIH. refine (cat (trTy_wk θ IH eIH _) _).
  exact (cat (inv (ty_sub_comp Cm (S ∘ pp IH) θI))
    (cat (ap (fun f => Cm[f]) M1) (ty_sub_comp Cm (wk σ W) (S' ∘ pp IH')))).
Qed.

Record WF {P : PiF} := {
  (** [W(A, B)], for [B] over [Γ.A]. *)
  wty : forall {Γ} (A : Ty Γ), Ty (Γ ▹ A) -> Ty Γ;
  (** [W(A, B)[σ] = W(A[σ], B[σ⁺])] *)
  wty_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)),
    (wty A B)[σ] = wty (A[σ]) (B[wk σ A]);
  (** [sup a f : W(A, B)], stated as a term over the context [Γ, a : A, f : Π(b : B a). W(A, B)]. *)
  sup : forall {Γ} (A : Ty Γ) (B : Ty (Γ ▹ A)), Tm (wCtx2 P A B (wty A B)) (wSupTy P A B (wty A B));
  (** [sup[σ⁺⁺] = sup], along the weakening of [σ] to that context. *)
  sup_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (A : Ty Γ) (B : Ty (Γ ▹ A)),
    (* [e : (Π(b : B a). W)[σ⁺] = Π(b : B[σ⁺] a). W'] and [e' : W[p][p][σ⁺⁺] = W'[p][p]], for
       [W = W(A, B)] and [W' = W(A[σ], B[σ⁺]) = W[σ]] *)
    let e : (wF P A B (wty A B))[wk σ A]
            = wF P (A[σ]) (B[wk σ A]) (wty (A[σ]) (B[wk σ A])) :=
      e_wF P σ A B (wty_sub σ A B) in
    let e' : trTy e ((wSupTy P A B (wty A B))[wk (wk σ A) (wF P A B (wty A B))])
             = wSupTy P (A[σ]) (B[wk σ A]) (wty (A[σ]) (B[wk σ A])) :=
      e_wSupTy P σ A B (wty_sub σ A B) in
    trTm e' (trD e ((sup A B)[wk (wk σ A) (wF P A B (wty A B))]ₜ)) = sup (A[σ]) (B[wk σ A]);
  (** [rec C m : C] over [Γ.W(A, B)], for a step term [m : Π(a : A). Π(f : Π(b : B a). W(A, B)). Π(g : Π(b : B a). C(f b)). C(sup a f)]. *)
  wrec : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)} (Cm : Ty (Γ ▹ wty A B)),
    Tm Γ (wMinorPi P A B (wty A B) Cm (sup A B)) -> Tm (Γ ▹ wty A B) Cm;
  (** [rec C m (sup a f) = m a f (λ b. rec C m (f b))], stated as an equation of substitutions. *)
  wrec_sup : forall {Γ} {A : Ty Γ} {B : Ty (Γ ▹ A)} (Cm : Ty (Γ ▹ wty A B))
    (m : Tm Γ (wMinorPi P A B (wty A B) Cm (sup A B))),
    (* [e : C[S ∘ p][⟨id, λb. rec C m (f b)⟩] = C[S]], for [S = (γ, a, f) ↦ (γ, sup a f)] *)
    let e : (wMinorTy P A B (wty A B) Cm (sup A B))[sec (lam P ((wrec Cm m)[wRho P A B (wty A B)]ₜ))]
            = Cm[wSupMap P A B (wty A B) (sup A B)] :=
      e_minor P A B (wty A B) Cm (sup A B) _ in
    trTm e ((app P (app P (app P m)))[sec (lam P ((wrec Cm m)[wRho P A B (wty A B)]ₜ))]ₜ)
    = (wrec Cm m)[wSupMap P A B (wty A B) (sup A B)]ₜ;
  (** [(rec C m)[σ⁺] = rec (C[σ⁺]) (m[σ])] *)
  wrec_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) {A : Ty Γ} {B : Ty (Γ ▹ A)} (Cm : Ty (Γ ▹ wty A B))
    (m : Tm Γ (wMinorPi P A B (wty A B) Cm (sup A B))),
    (* [e : (Π a f g. C(sup a f))[σ] = Π a f g. C[σ⁺](sup a f)], the second over [A[σ]] and [B[σ⁺]]:
       the types of [m[σ]] and of the step terms over [Δ] *)
    let e : (wMinorPi P A B (wty A B) Cm (sup A B))[σ]
            = wMinorPi P (A[σ]) (B[wk σ A]) (wty (A[σ]) (B[wk σ A]))
                (trTy (wty_sub σ A B) (Cm[wk σ (wty A B)])) (sup (A[σ]) (B[wk σ A])) :=
      e_wMinorPi P σ A B (wty_sub σ A B) Cm (sup A B) (sup (A[σ]) (B[wk σ A])) (sup_sub σ A B) in
    trD (wty_sub σ A B) ((wrec Cm m)[wk σ (wty A B)]ₜ)
    = wrec (trTy (wty_sub σ A B) (Cm[wk σ (wty A B)])) (trTm e (m[σ]ₜ))
}.

(** ** Propositions and identity propositions *)

Record PropF := {
  (** The universe [Prop]. *)
  prop : forall Γ, Ty Γ;
  (** [Prop[σ] = Prop] *)
  prop_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), (prop Γ)[σ] = prop Δ;
  (** [El φ], the type of proofs of [φ : Prop]. *)
  prfT : forall {Γ}, Tm Γ (prop Γ) -> Ty Γ;
  (** [(El φ)[σ] = El (φ[σ])] *)
  prf_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (φ : Tm Γ (prop Γ)),
    (prfT φ)[σ] = prfT (trTm (prop_sub σ) (φ[σ]ₜ));
  (** Proof irrelevance: [h = h'] for [h, h' : El φ]. *)
  prf_irrel : forall {Γ} {φ : Tm Γ (prop Γ)} (h h' : Tm Γ (prfT φ)), h = h';
  (** Impredicative quantification [∀(x : A). φ : Prop], for every type [A] and [φ : Prop] over [Γ.A]. *)
  all : forall {Γ} (A : Ty Γ), Tm (Γ ▹ A) (prop (Γ ▹ A)) -> Tm Γ (prop Γ);
  (** [(∀(x : A). φ)[σ] = ∀(x : A[σ]). φ[σ⁺]] *)
  all_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (A : Ty Γ) (φ : Tm (Γ ▹ A) (prop (Γ ▹ A))),
    trTm (prop_sub σ) ((all A φ)[σ]ₜ)
    = all (A[σ]) (trTm (prop_sub (wk σ A)) (φ[wk σ A]ₜ));
  (** Introduction: a proof of [φ] over [Γ.A] gives a proof of [∀(x : A). φ] over [Γ]. *)
  allIntro : forall {Γ} (A : Ty Γ) (φ : Tm (Γ ▹ A) (prop (Γ ▹ A))),
    Tm (Γ ▹ A) (prfT φ) -> Tm Γ (prfT (all A φ));
  (** Elimination: a proof of [∀(x : A). φ] over [Γ] gives a proof of [φ] over [Γ.A]. *)
  allElim : forall {Γ} (A : Ty Γ) (φ : Tm (Γ ▹ A) (prop (Γ ▹ A))),
    Tm Γ (prfT (all A φ)) -> Tm (Γ ▹ A) (prfT φ)
}.

Section Logic.
Context (Pr : PropF).

(** The substitution laws of [allIntro] and [allElim] follow from proof irrelevance,
    as do the β- and η-laws. *)
Lemma allIntro_sub {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (A : Ty Γ) (φ : Tm (Γ ▹ A) (prop Pr (Γ ▹ A)))
    (b : Tm (Γ ▹ A) (prfT Pr φ)) :
  tr (Tm Δ) (cat (prf_sub Pr σ (all Pr A φ)) (ap (prfT Pr) (all_sub Pr σ A φ))) ((allIntro Pr A φ b)[σ]ₜ)
  = allIntro Pr (A[σ]) _ (tr (Tm _) (prf_sub Pr (wk σ A) φ) (b[wk σ A]ₜ)).
Proof. apply prf_irrel. Qed.
Lemma allElim_sub {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (A : Ty Γ) (φ : Tm (Γ ▹ A) (prop Pr (Γ ▹ A)))
    (s : Tm Γ (prfT Pr (all Pr A φ))) :
  tr (Tm _) (prf_sub Pr (wk σ A) φ) ((allElim Pr A φ s)[wk σ A]ₜ)
  = allElim Pr (A[σ]) _
      (tr (Tm Δ) (cat (prf_sub Pr σ (all Pr A φ)) (ap (prfT Pr) (all_sub Pr σ A φ))) (s[σ]ₜ)).
Proof. apply prf_irrel. Qed.

(** [φ[σ]] for [φ : Prop], and the variable [R] of type [Prop] over [Γ, R : Prop]. *)
Definition subP {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (φ : Tm Γ (prop Pr Γ)) : Tm Δ (prop Pr Δ) :=
  trTm (prop_sub Pr σ) (φ[σ]ₜ).
Definition varP (Γ : Ctx C) : Tm (Γ ▹ prop Pr Γ) (prop Pr _) :=
  trTm (prop_sub Pr (pp _)) (qq (prop Pr Γ)).

(** The impredicative encodings of the connectives:
      [φ ⇒ ψ := ∀(_ : El φ). ψ],      [⊥ := ∀R:Prop. R],      [¬φ := φ ⇒ ⊥],
      [φ ∧ ψ := ∀R:Prop. (φ ⇒ ψ ⇒ R) ⇒ R],   [φ ∨ ψ := ∀R:Prop. (φ ⇒ R) ⇒ (ψ ⇒ R) ⇒ R],
      [φ ⇔ ψ := (φ ⇒ ψ) ∧ (ψ ⇒ φ)]. *)
Definition impT {Γ : Ctx C} (φ ψ : Tm Γ (prop Pr Γ)) : Tm Γ (prop Pr Γ) :=
  all Pr (prfT Pr φ) (subP (pp _) ψ).
Definition botT (Γ : Ctx C) : Tm Γ (prop Pr Γ) := all Pr (prop Pr Γ) (varP Γ).
Definition negT {Γ : Ctx C} (φ : Tm Γ (prop Pr Γ)) : Tm Γ (prop Pr Γ) := impT φ (botT Γ).
Definition andT {Γ : Ctx C} (φ ψ : Tm Γ (prop Pr Γ)) : Tm Γ (prop Pr Γ) :=
  all Pr (prop Pr Γ) (impT (impT (subP (pp _) φ) (impT (subP (pp _) ψ) (varP Γ))) (varP Γ)).
Definition orT {Γ : Ctx C} (φ ψ : Tm Γ (prop Pr Γ)) : Tm Γ (prop Pr Γ) :=
  all Pr (prop Pr Γ)
    (impT (impT (subP (pp _) φ) (varP Γ)) (impT (impT (subP (pp _) ψ) (varP Γ)) (varP Γ))).
Definition iffT {Γ : Ctx C} (φ ψ : Tm Γ (prop Pr Γ)) : Tm Γ (prop Pr Γ) := andT (impT φ ψ) (impT ψ φ).
(** Excluded middle, [∀P:Prop. P ∨ ¬P]. *)
Definition EMT (Γ : Ctx C) : Tm Γ (prop Pr Γ) :=
  all Pr (prop Pr Γ) (orT (varP Γ) (negT (varP Γ))).

(** A relation [R] over [Γ, a : A, b : A], substituted along [σ]. *)
Definition subR {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (A : Ty Γ)
    (R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)) :
    Tm (Δ ▹ A[σ] ▹ A[σ][pp (A[σ])]) (prop Pr _) :=
  tr (fun Z => Tm (Δ ▹ A[σ] ▹ Z) (prop Pr (Δ ▹ A[σ] ▹ Z))) (e_pwk σ A A)
    (subP (wk (wk σ A) (A[pp A])) R).

End Logic.

Record IdF {Pr : PropF} := {
  (** The identity proposition [Id(t, u) : Prop]. *)
  idP : forall {Γ} (A : Ty Γ), Tm Γ A -> Tm Γ A -> Tm Γ (prop Pr Γ);
  (** [Id(t, u)[σ] = Id(t[σ], u[σ])] *)
  idP_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (A : Ty Γ) (t u : Tm Γ A),
    subP Pr σ (idP A t u) = idP (A[σ]) (t[σ]ₜ) (u[σ]ₜ);
  (** [refl t : El (Id(t, t))] *)
  refl : forall {Γ} {A : Ty Γ} (t : Tm Γ A), Tm Γ (prfT Pr (idP A t t));
  (** Equality reflection: a term of [El (Id(t, u))] gives [t = u]. *)
  reflection : forall {Γ} {A : Ty Γ} {t u : Tm Γ A}, Tm Γ (prfT Pr (idP A t u)) -> t = u
}.

(** Naturality of [refl], from proof irrelevance. *)
Lemma refl_sub {Pr : PropF} (Id : IdF (Pr := Pr)) {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) {A : Ty Γ} (t : Tm Γ A) :
  tr (fun χ => Tm Δ (prfT Pr χ)) (idP_sub Id σ A t t)
     (trTm (prf_sub Pr σ (idP Id A t t)) ((refl Id t)[σ]ₜ))
  = refl Id (t[σ]ₜ).
Proof. apply prf_irrel. Qed.

Section Logic2.
Context {Pr : PropF} (Id : IdF (Pr := Pr)).

(** Propositional extensionality, [∀P Q:Prop. (P ⇔ Q) ⇒ Id(P, Q)]. *)
Definition propextT (Γ : Ctx C) : Tm Γ (prop Pr Γ) :=
  all Pr (prop Pr Γ) (all Pr (prop Pr _)
    (impT Pr (iffT Pr (subP Pr (pp _) (varP Pr Γ)) (varP Pr _))
      (idP Id (prop Pr _) (subP Pr (pp _) (varP Pr Γ)) (varP Pr _)))).

(** [∀ a b : A. R a b ⇒ Id(f a, f b)], for [f : B] over [Γ.A]: the hypothesis of
    [lift], and for [f := mk] the statement of soundness. *)
Definition respIn {Γ : Ctx C} (A : Ty Γ) (R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _))
    (B : Ty Γ) (f : Tm (Γ ▹ A) (B[pp A])) : Tm Γ (prop Pr Γ) :=
  all Pr A (all Pr (A[pp A]) (impT Pr R
    (idP Id (B[pp A][pp _]) (f[pp _]ₜ) (trTm (e_snd2 A B) (f[snd2 A]ₜ))))).

End Logic2.

(** ** Quotients *)

Record QuotF {Pr : PropF} {Id : IdF (Pr := Pr)} := {
  (** [A/R], for [R : Prop] over [Γ, a : A, b : A]. *)
  quot : forall {Γ} (A : Ty Γ), Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _) -> Ty Γ;
  (** [(A/R)[σ] = A[σ]/R[σ]] *)
  quot_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (A : Ty Γ) (R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)),
    (quot A R)[σ] = quot (A[σ]) (subR Pr σ A R);
  (** [mk : (A/R)[p]] over [Γ.A]. *)
  qmk : forall {Γ} {A : Ty Γ} {R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)},
    Tm (Γ ▹ A) ((quot A R)[pp A]);
  (** [mk[σ⁺] = mk] *)
  qmk_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (A : Ty Γ) (R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)),
    (* [e : (A/R)[p][σ⁺] = (A[σ]/R[σ])[p]] *)
    let e : ((quot A R)[pp A])[wk σ A] = (quot (A[σ]) (subR Pr σ A R))[pp (A[σ])] :=
      cat (e_pwk σ A (quot A R)) (ap (fun X => X[pp (A[σ])]) (quot_sub σ A R)) in
    trTm e ((qmk (A := A) (R := R))[wk σ A]ₜ) = qmk (A := A[σ]) (R := subR Pr σ A R);
  (** [lift B f h : B[p]] over [Γ.A/R], for [f : B[p]] over [Γ.A] and [h : ∀ a b. R a b ⇒ Id(f a, f b)]. *)
  qlift : forall {Γ} {A : Ty Γ} {R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)}
    (B : Ty Γ) (f : Tm (Γ ▹ A) (B[pp A])),
    Tm Γ (prfT Pr (respIn Id A R B f)) -> Tm (Γ ▹ quot A R) (B[pp _]);
  (** [(lift B f h)[⟨p, mk⟩] = f] *)
  qlift_mk : forall {Γ} {A : Ty Γ} {R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)}
    (B : Ty Γ) (f : Tm (Γ ▹ A) (B[pp A])) (h : Tm Γ (prfT Pr (respIn Id A R B f))),
    (* [e : B[p][⟨p, mk⟩] = B[p]] *)
    let e : B[pp (quot A R)][⟨pp A, qmk⟩] = B[pp A] :=
      cat (inv (ty_sub_comp B (pp (quot A R)) (⟨pp A, qmk⟩))) (ap (fun f => B[f]) (pair_proj (pp A) qmk)) in
    trTm e ((qlift B f h)[⟨pp A, qmk⟩]ₜ) = f;
  (** [(lift B f h)[σ⁺] = lift (B[σ]) (f[σ⁺]) h'] *)
  qlift_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) {A : Ty Γ} {R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)}
    (B : Ty Γ) (f : Tm (Γ ▹ A) (B[pp A])) (h : Tm Γ (prfT Pr (respIn Id A R B f)))
    (h' : Tm Δ (prfT Pr (respIn Id (A[σ]) (subR Pr σ A R) (B[σ])
                          (trTm (e_pwk σ A B) (f[wk σ A]ₜ))))),
    (* [e : B[p][σ⁺] = B[σ][p]], over [Δ.(A[σ]/R[σ])] *)
    let e : trTy (quot_sub σ A R) (B[pp (quot A R)][wk σ (quot A R)])
            = B[σ][pp (quot (A[σ]) (subR Pr σ A R))] :=
      cat (ap (trTy (quot_sub σ A R)) (e_pwk σ (quot A R) B))
        (tr_apD (fun Z => Ty (Δ ▹ Z)) (fun Z => B[σ][pp Z]) (quot_sub σ A R)) in
    trTm e (trD (quot_sub σ A R) ((qlift B f h)[wk σ (quot A R)]ₜ))
    = qlift (R := subR Pr σ A R) (B[σ]) (trTm (e_pwk σ A B) (f[wk σ A]ₜ)) h';
  (** Induction, stated as a map from terms of [El (χ[⟨p, mk⟩])] over [Γ.A] to terms of [El χ] over [Γ.A/R]. *)
  qind : forall {Γ} {A : Ty Γ} {R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)}
    (χ : Tm (Γ ▹ quot A R) (prop Pr _)),
    Tm (Γ ▹ A) (prfT Pr (subP Pr (⟨pp A, qmk⟩) χ)) -> Tm (Γ ▹ quot A R) (prfT Pr χ);
  (** Soundness: [∀ a b. R a b ⇒ Id(mk a, mk b)]. *)
  qsound : forall {Γ} {A : Ty Γ} {R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)},
    Tm Γ (prfT Pr (respIn Id A R (quot A R) qmk))
}.

(** Derived equations for propositions: [φ[σ][τ] = φ[σ ∘ τ]], [∀] along [wkE], the
    substitution laws of [⇒] and of [subR], and the substitution law of [respIn]. *)
Lemma subP_comp (Pr : PropF) {Θ Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (φ : Tm Γ (prop Pr Γ)) :
  subP Pr τ (subP Pr σ φ) = subP Pr (σ ∘ τ) φ.
Proof.
  refine (treq_tr_eq (Tm Θ) eq_refl _ _ _).
  eapply treq_trans; [apply treq_sym, treq_tr|]. eapply treq_trans; [apply sub_treq, treq_sym, treq_tr|].
  eapply treq_trans; [apply treq_sym, tsc_treq | apply treq_tr].
Qed.
Lemma all_wkE (Pr : PropF) {Δ Γ : Ctx C} (τ : Δ ⟶ Γ) (X : Ty Γ) {X' : Ty Δ} (e : X[τ] = X')
    (φ : Tm (Γ ▹ X) (prop Pr _)) :
  all Pr (X[τ]) (subP Pr (wk τ X) φ) = all Pr X' (subP Pr (wkE τ X e) φ).
Proof. destruct e. rw (wkE_refl τ X). reflexivity. Qed.
Lemma subP_wkE (Pr : PropF) {Δ Γ : Ctx C} (τ : Δ ⟶ Γ) (X : Ty Γ) {X' : Ty Δ} (e : X[τ] = X')
    (φ : Tm (Γ ▹ X) (prop Pr _)) :
  tr (fun Z => Tm (Δ ▹ Z) (prop Pr (Δ ▹ Z))) e (subP Pr (wk τ X) φ) = subP Pr (wkE τ X e) φ.
Proof. destruct e. rw (wkE_refl τ X). reflexivity. Qed.
Lemma impT_sub (Pr : PropF) {Δ Γ : Ctx C} (δ : Δ ⟶ Γ) (φ ψ : Tm Γ (prop Pr Γ)) :
  subP Pr δ (impT Pr φ ψ) = impT Pr (subP Pr δ φ) (subP Pr δ ψ).
Proof.
  refine (cat (all_sub Pr δ (prfT Pr φ) _) _).
  refine (cat (all_wkE Pr δ (prfT Pr φ) (prf_sub Pr δ φ) _) _).
  apply (ap (fun x => all Pr (prfT Pr (subP Pr δ φ)) x)).
  refine (cat (subP_comp Pr (pp _) _ ψ) _). refine (cat (ap (fun f => subP Pr f ψ) (pair_proj _ _)) _).
  exact (inv (subP_comp Pr δ (pp _) ψ)).
Qed.

(** [(∀ a b : A. R a b ⇒ Id(f a, f b))[σ] = ∀ a b : A[σ]. R[σ] a b ⇒ Id(f' a, f' b)], for
    [B[σ] = B'] and [f[σ⁺] ≃ f']. *)
Lemma respIn_sub {Pr : PropF} (Id : IdF (Pr := Pr)) {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (A : Ty Γ)
    (R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)) (B : Ty Γ) {B' : Ty Δ} (eB : B[σ] = B')
    (f : Tm (Γ ▹ A) (B[pp A])) (f' : Tm (Δ ▹ A[σ]) (B'[pp (A[σ])]))
    (hf : treq (Tm (Δ ▹ A[σ])) (f[wk σ A]ₜ) f') :
  subP Pr σ (respIn Id A R B f) = respIn Id (A[σ]) (subR Pr σ A R) B' f'.
Proof.
  pose (A' := A[σ]). pose (τ := wk σ A). pose (X2 := A[pp A]). pose (X2' := A'[pp A']).
  pose (θ2 := wkE τ X2 (e_pwk σ A A)).
  assert (S2 : snd2 A ∘ θ2 = τ ∘ snd2 A').
  { apply hom_ext.
    - refine (cat (inv (comp_assoc (pp A) (snd2 A) θ2)) _).
      refine (cat (ap (fun f => f ∘ θ2) (pair_proj _ _)) _).
      refine (cat (comp_assoc (pp A) (pp X2) θ2) _).
      refine (cat (ap (comp (pp A)) (pair_proj _ _)) _).
      refine (cat (inv (comp_assoc (pp A) τ (pp X2'))) _).
      refine (cat (ap (fun f => f ∘ pp X2') (pair_proj _ _)) _).
      refine (cat (comp_assoc σ (pp A') (pp X2')) _). refine (inv _).
      refine (cat (inv (comp_assoc (pp A) τ (snd2 A'))) _).
      refine (cat (ap (fun f => f ∘ snd2 A') (pair_proj _ _)) _).
      refine (cat (comp_assoc σ (pp A') (snd2 A')) _).
      exact (ap (comp σ) (pair_proj _ _)).
    - eapply treq_trans; [apply tsc_treq|].
      eapply treq_trans; [apply sub_treq, pv_treq|].
      eapply treq_trans; [apply sub_treq, treq_sym, treq_tr|].
      eapply treq_trans; [apply wkE_q|].
      eapply treq_trans; [|apply treq_sym, tsc_treq].
      eapply treq_trans; [|apply sub_treq, treq_sym, pv_treq].
      eapply treq_trans; [|apply sub_treq, treq_tr].
      eapply treq_trans; [|apply treq_sym, pv_treq].
      apply treq_tr. }
  refine (cat (all_sub Pr σ A _) (ap (fun x => all Pr A' x) _)).
  refine (cat (all_sub Pr τ X2 _) _).
  refine (cat (all_wkE Pr τ X2 (e_pwk σ A A) _) (ap (fun x => all Pr X2' x) _)).
  refine (cat (impT_sub Pr θ2 R _) _).
  refine (cat (ap (fun x => impT Pr x _) (inv (subP_wkE Pr τ X2 (e_pwk σ A A) R))) (ap (fun y => impT Pr _ y) _)).
  refine (cat (idP_sub Id θ2 _ _ _) _).
  refine (ap_dep2 (Tm _) (fun X t u => idP Id X t u)
            (cat (inv (ty_sub_comp (B[pp A]) (pp X2) θ2))
              (cat (ap (fun f => B[pp A][f]) (pair_proj _ _))
                (cat (ty_sub_comp (B[pp A]) τ (pp X2'))
                  (cat (ap (fun Y => Y[pp X2']) (e_pwk σ A B))
                    (ap (fun Y => Y[pp A'][pp X2']) eB))))) _ _); apply treq_tr_eq.
  - eapply treq_trans; [apply treq_sym, tsc_treq|].
    eapply treq_trans; [apply subTm_hom, pair_proj|].
    eapply treq_trans; [apply tsc_treq | apply sub_treq, hf].
  - eapply treq_trans; [apply sub_treq, treq_sym, treq_tr|].
    eapply treq_trans; [apply treq_sym, tsc_treq|].
    eapply treq_trans; [apply subTm_hom, S2|].
    eapply treq_trans; [apply tsc_treq|].
    eapply treq_trans; [apply sub_treq, hf | apply treq_tr].
Qed.

(** Naturality of induction and soundness, from proof irrelevance. The proposition [χ']
    is [χ] substituted along the weakening of [σ] to [Γ.A/R]. *)
Lemma qind_sub {Pr : PropF} {Id : IdF (Pr := Pr)} (Q : QuotF (Id := Id)) {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) {A : Ty Γ}
    {R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)} (χ : Tm (Γ ▹ quot Q A R) (prop Pr _))
    (k : Tm (Γ ▹ A) (prfT Pr (subP Pr (⟨pp A, qmk Q⟩) χ))) :
  (* [χ' = χ[σ⁺]], and [e : (El χ)[σ⁺] = El χ'] *)
  let χ' : Tm (Δ ▹ quot Q (A[σ]) (subR Pr σ A R)) (prop Pr _) :=
    subP Pr (wkE σ (quot Q A R) (quot_sub Q σ A R)) χ in
  forall k' : Tm (Δ ▹ A[σ]) (prfT Pr (subP Pr (⟨pp (A[σ]), qmk Q⟩) χ')),
  let e : trTy (quot_sub Q σ A R) ((prfT Pr χ)[wk σ (quot Q A R)]) = prfT Pr χ' :=
    cat (trTy_wk σ (quot Q A R) (quot_sub Q σ A R) (prfT Pr χ))
      (prf_sub Pr (wkE σ (quot Q A R) (quot_sub Q σ A R)) χ) in
  trTm e (trD (quot_sub Q σ A R) ((qind Q χ k)[wk σ (quot Q A R)]ₜ)) = qind Q χ' k'.
Proof. intros χ' k' e. apply prf_irrel. Qed.

Lemma qsound_sub {Pr : PropF} {Id : IdF (Pr := Pr)} (Q : QuotF (Id := Id)) {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) {A : Ty Γ}
    {R : Tm (Γ ▹ A ▹ A[pp A]) (prop Pr _)} :
  (* [e : (∀ a b. R a b ⇒ Id(mk a, mk b))[σ] = ∀ a b. R[σ] a b ⇒ Id(mk a, mk b)] *)
  let e : (prfT Pr (respIn Id A R (quot Q A R) (qmk Q)))[σ]
          = prfT Pr (respIn Id (A[σ]) (subR Pr σ A R) (quot Q (A[σ]) (subR Pr σ A R)) (qmk Q)) :=
    cat (prf_sub Pr σ _)
      (ap (prfT Pr) (respIn_sub Id σ A R (quot Q A R) (quot_sub Q σ A R) (qmk Q) (qmk Q)
                       (ex_intro _ _ (qmk_sub Q σ A R)))) in
  trTm e ((qsound Q (A := A) (R := R))[σ]ₜ) = qsound Q (A := A[σ]) (R := subR Pr σ A R).
Proof. intros e. apply prf_irrel. Qed.

(** ** Universes *)

Record UnivBase := {
  (** The universe [U] and the decoding [El X] of a code [X : U]. *)
  U : forall Γ, Ty Γ;
  (** [U[σ] = U] *)
  U_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), (U Γ)[σ] = U Δ;
  El : forall {Γ}, Tm Γ (U Γ) -> Ty Γ;
  (** [(El X)[σ] = El (X[σ])] *)
  El_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (X : Tm Γ (U Γ)), (El X)[σ] = El (trTm (U_sub σ) (X[σ]ₜ))
}.

Section Univ.
Context (V : UnivBase).

Definition subU {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (X : Tm Γ (U V Γ)) : Tm Δ (U V Δ) :=
  trTm (U_sub V σ) (X[σ]ₜ).
Definition varU (Γ : Ctx C) : Tm (Γ ▹ U V Γ) (U V _) := trTm (U_sub V (pp _)) (qq (U V Γ)).
(** A code over [Γ.El a], substituted along [σ]. *)
Definition subUx {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (a : Tm Γ (U V Γ)) (b : Tm (Γ ▹ El V a) (U V _)) :
    Tm (Δ ▹ El V (subU σ a)) (U V _) :=
  tr (fun Z => Tm (Δ ▹ Z) (U V (Δ ▹ Z))) (El_sub V σ a) (subU (wk σ (El V a)) b).
(** A relation over [Γ, x : El a, y : El a], substituted along [σ]. *)
Definition subRx (Pr : PropF) {Δ Γ : Ctx C} (σ : Δ ⟶ Γ) (a : Tm Γ (U V Γ))
    (R : Tm (Γ ▹ El V a ▹ (El V a)[pp _]) (prop Pr _)) :
    Tm (Δ ▹ El V (subU σ a) ▹ (El V (subU σ a))[pp _]) (prop Pr _) :=
  tr (fun Z => Tm (Δ ▹ Z ▹ Z[pp Z]) (prop Pr _)) (El_sub V σ a) (subR Pr σ (El V a) R).

(** The truncation [‖X‖ := ∀P:Prop. (∀(x : El X). P) ⇒ P]. *)
Definition truncT (Pr : PropF) {Γ : Ctx C} (X : Tm Γ (U V Γ)) : Tm Γ (prop Pr Γ) :=
  all Pr (prop Pr Γ)
    (impT Pr (all Pr (El V (subU (pp _) X)) (subP Pr (pp _) (varP Pr Γ))) (varP Pr Γ)).

End Univ.

(** The codes, in a universe, of Π, Σ, the finite types, W-types, quotients and
    propositions, with [El] of a code the former applied to the decodings. *)
Record Codes {P : PiF} {Sg : SigmaF} {F : FinF} {W : WF (P := P)} {Pr : PropF}
    {Id : IdF (Pr := Pr)} {Q : QuotF (Id := Id)} {V : UnivBase} := {
  (** [π(a, b) : U], with [El π(a, b) = Π(El a, El b)] and [π(a, b)[σ] = π(a[σ], b[σ⁺])]. *)
  piCode : forall {Γ} (a : Tm Γ (U V Γ)), Tm (Γ ▹ El V a) (U V _) -> Tm Γ (U V Γ);
  El_piCode : forall {Γ} (a : Tm Γ (U V Γ)) (b : Tm (Γ ▹ El V a) (U V _)),
    El V (piCode a b) = Pi P (El V a) (El V b);
  piCode_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (a : Tm Γ (U V Γ)) (b : Tm (Γ ▹ El V a) (U V _)),
    subU V σ (piCode a b) = piCode (subU V σ a) (subUx V σ a b);
  (** [sg(a, b) : U], with [El sg(a, b) = Σ(El a, El b)] and [sg(a, b)[σ] = sg(a[σ], b[σ⁺])]. *)
  sigmaCode : forall {Γ} (a : Tm Γ (U V Γ)), Tm (Γ ▹ El V a) (U V _) -> Tm Γ (U V Γ);
  El_sigmaCode : forall {Γ} (a : Tm Γ (U V Γ)) (b : Tm (Γ ▹ El V a) (U V _)),
    El V (sigmaCode a b) = Sigma Sg (El V a) (El V b);
  sigmaCode_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (a : Tm Γ (U V Γ)) (b : Tm (Γ ▹ El V a) (U V _)),
    subU V σ (sigmaCode a b) = sigmaCode (subU V σ a) (subUx V σ a b);
  (** The code of [0], natural, with [El] equal to [0]. *)
  zeroCode : forall Γ, Tm Γ (U V Γ);
  El_zeroCode : forall Γ, El V (zeroCode Γ) = zero F Γ;
  zeroCode_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), subU V σ (zeroCode Γ) = zeroCode Δ;
  (** The code of [1], natural, with [El] equal to [1]. *)
  oneCode : forall Γ, Tm Γ (U V Γ);
  El_oneCode : forall Γ, El V (oneCode Γ) = one F Γ;
  oneCode_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), subU V σ (oneCode Γ) = oneCode Δ;
  (** The code of [2], natural, with [El] equal to [2]. *)
  twoCode : forall Γ, Tm Γ (U V Γ);
  El_twoCode : forall Γ, El V (twoCode Γ) = two F Γ;
  twoCode_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), subU V σ (twoCode Γ) = twoCode Δ;
  (** [w(a, b) : U], with [El w(a, b) = W(El a, El b)] and [w(a, b)[σ] = w(a[σ], b[σ⁺])]. *)
  wCode : forall {Γ} (a : Tm Γ (U V Γ)), Tm (Γ ▹ El V a) (U V _) -> Tm Γ (U V Γ);
  El_wCode : forall {Γ} (a : Tm Γ (U V Γ)) (b : Tm (Γ ▹ El V a) (U V _)),
    El V (wCode a b) = wty W (El V a) (El V b);
  wCode_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (a : Tm Γ (U V Γ)) (b : Tm (Γ ▹ El V a) (U V _)),
    subU V σ (wCode a b) = wCode (subU V σ a) (subUx V σ a b);
  (** [a/R : U], with [El (a/R) = El a / R] and [(a/R)[σ] = a[σ]/R[σ]]. *)
  quotCode : forall {Γ} (a : Tm Γ (U V Γ)),
    Tm (Γ ▹ El V a ▹ (El V a)[pp _]) (prop Pr _) -> Tm Γ (U V Γ);
  El_quotCode : forall {Γ} (a : Tm Γ (U V Γ)) (R : Tm (Γ ▹ El V a ▹ (El V a)[pp _]) (prop Pr _)),
    El V (quotCode a R) = quot Q (El V a) R;
  quotCode_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (a : Tm Γ (U V Γ))
    (R : Tm (Γ ▹ El V a ▹ (El V a)[pp _]) (prop Pr _)),
    subU V σ (quotCode a R) = quotCode (subU V σ a) (subRx V Pr σ a R);
  (** [ι φ : U] for [φ : Prop], with [El (ι φ) = El φ] and [(ι φ)[σ] = ι (φ[σ])]. *)
  inclCode : forall {Γ}, Tm Γ (prop Pr Γ) -> Tm Γ (U V Γ);
  El_inclCode : forall {Γ} (φ : Tm Γ (prop Pr Γ)), El V (inclCode φ) = prfT Pr φ;
  inclCode_sub : forall {Δ Γ} (σ : Δ ⟶ Γ) (φ : Tm Γ (prop Pr Γ)),
    subU V σ (inclCode φ) = inclCode (subP Pr σ φ);
  (** The code of [Prop], natural, with [El] equal to [Prop]. *)
  propCode : forall Γ, Tm Γ (U V Γ);
  El_propCode : forall Γ, El V (propCode Γ) = prop Pr Γ;
  propCode_sub : forall {Δ Γ} (σ : Δ ⟶ Γ), subU V σ (propCode Γ) = propCode Δ
}.

(** ** The structure [TModel] *)

(** A model of the type theory: the type formers, [Prop] with [∀] and identity
    propositions, quotients, a universe [U] with codes, global choice for [U], the
    negations of excluded middle and of propositional extensionality, and
    consistency. *)
Record TModel := {
  tPi : PiF;
  tSigma : SigmaF;
  tFin : FinF;
  tW : WF (P := tPi);
  tProp : PropF;
  tId : IdF (Pr := tProp);
  tQuot : QuotF (Id := tId);
  tU : UnivBase;
  tCodes : Codes (Sg := tSigma) (F := tFin) (W := tW) (Q := tQuot) (V := tU);
  (** Global choice, a closed term of [Π(X : U). El ‖X‖ → El X]. *)
  choiceT : Tm (empty C)
    (Pi tPi (U tU (empty C))
       (Pi tPi (prfT tProp (truncT tU tProp (varU tU (empty C))))
          (El tU (subU tU (pp _) (varU tU (empty C))))));
  (** A closed term of [¬ ∀P:Prop. P ∨ ¬P]. *)
  notEM : Tm (empty C) (prfT tProp (negT tProp (EMT tProp (empty C))));
  (** A closed term of [¬ ∀P Q:Prop. (P ⇔ Q) ⇒ Id(P, Q)]. *)
  notPropext : Tm (empty C) (prfT tProp (negT tProp (propextT tId (empty C))));
  (** Consistency: [⊥] has no closed term. *)
  consistent : Tm (empty C) (prfT tProp (botT tProp (empty C))) -> False
}.

End Spec.

(** * Part II. Staged sets *)

Section Staged.

(** The stages: a well-ordered set [L] with least element [bot], written [0] in the comments. *)
Context (L : Set) (le : L -> L -> Prop) (bot : L)
  (le_refl : forall a, le a a)
  (le_trans : forall a b c, le a b -> le b c -> le a c)
  (le_antisym : forall a b, le a b -> le b a -> a = b)
  (le_total : forall a b, le a b \/ le b a)
  (bot_le : forall a, le bot a)
  (le_wf : well_founded (fun a b => le a b /\ a <> b)).

(** ** Maxima and least elements *)

(** [max(a, b)]. *)
Definition maxL (a b : L) : L := if decb (le a b) then b else a.

Lemma le_max_l a b : le a (maxL a b).
Proof. unfold maxL. destruct (decb (le a b)) eqn:E; [apply decb_spec, E | apply le_refl]. Qed.
Lemma le_max_r a b : le b (maxL a b).
Proof.
  unfold maxL. destruct (decb (le a b)) eqn:E; [apply le_refl|].
  destruct (le_total a b) as [h|h]; [|exact h]. rewrite (decb_true _ h) in E. discriminate.
Qed.
Lemma max_lub a b c : le a c -> le b c -> le (maxL a b) c.
Proof. unfold maxL. destruct (decb (le a b)); auto. Qed.
Lemma le_max_l' a b c : le a b -> le a (maxL b c).
Proof. intros h. exact (le_trans _ _ _ h (le_max_l _ _)). Qed.
Lemma le_max_r' a b c : le a c -> le a (maxL b c).
Proof. intros h. exact (le_trans _ _ _ h (le_max_r _ _)). Qed.
Lemma max_bot_l a : maxL bot a = a.
Proof. apply le_antisym; [apply max_lub; auto | apply le_max_r]. Qed.
Lemma max_bot_r a : maxL a bot = a.
Proof. apply le_antisym; [apply max_lub; auto | apply le_max_l]. Qed.

(** [lsolve] proves [le x y] for [y] a nest of maxima, from hypotheses [le u v]. *)
Ltac lsolveN n :=
  lazymatch n with
  | O => fail
  | S ?k =>
      repeat apply max_lub;
      first [ apply le_refl
            | apply le_max_l'; lsolveN k
            | apply le_max_r'; lsolveN k
            | match goal with h : le ?a ?b |- le ?a _ => apply (le_trans _ _ _ h); lsolveN k end ]
  end.
Ltac lsolve := solve [lsolveN 7].

(** Every nonempty subset of [L] has a least element. *)
Lemma exists_least (P : L -> Prop) : (exists l, P l) -> exists l, P l /\ forall m, P m -> le l m.
Proof.
  intros [l h]. revert h. induction l as [l IH] using (well_founded_ind le_wf). intros h.
  destruct (em (exists m, P m /\ le m l /\ m <> l)) as [[m [hm [hle hne]]]|hno].
  - exact (IH m (conj hle hne) hm).
  - exists l. split; [exact h|]. intros m hm. destruct (le_total l m) as [k|k]; [exact k|].
    destruct (em (m = l)) as [e|e]; [subst; apply le_refl|]. exfalso. apply hno. exists m. auto.
Qed.

(** Truth values [L∞ = L ∪ {∞}], with [∞ = None], ordered by [leT] with [∞] on top. A truth
    value [p] holds from stage [p] on. *)
Definition TV : Set := option L.
Definition leT (p q : TV) : Prop :=
  match p, q with _, None => True | None, Some _ => False | Some a, Some b => le a b end.

(** [inf P = min {l ∈ L | P l} ∈ L∞], with [min ∅ = ∞], and [leastB P = inf P ∈ L] when
    [P] holds somewhere. *)
Definition isInf (P : L -> Prop) (o : TV) : Prop :=
  match o with None => forall l, ~ P l | Some l => P l /\ forall m, P m -> le l m end.
Lemma inf_ex (P : L -> Prop) : exists o, isInf P o.
Proof.
  destruct (em (exists l, P l)) as [h|h].
  - destruct (exists_least P h) as [l hl]. exists (Some l). exact hl.
  - exists None. intros l hl. apply h. exists l. exact hl.
Qed.
Definition inf (P : L -> Prop) : TV := val (choice (isInf P) (inf_ex P)).
Lemma inf_spec (P : L -> Prop) : isInf P (inf P).
Proof. exact (prf (choice (isInf P) (inf_ex P))). Qed.
Lemma inf_le (P : L -> Prop) (k : L) : leT (inf P) (Some k) <-> exists l, P l /\ le l k.
Proof.
  pose proof (inf_spec P) as h. destruct (inf P) as [l|]; cbn in *.
  - split; [intros hk; exists l; split; [apply h|exact hk]|].
    intros [m [hm hk]]. exact (le_trans _ _ _ (proj2 h m hm) hk).
  - split; [intros []|]. intros [m [hm _]]. destruct (h m hm).
Qed.
Definition getL (o : TV) : L := match o with Some l => l | None => bot end.
Definition leastB (P : L -> Prop) : L := getL (inf P).
Lemma leastB_spec (P : L -> Prop) : (exists l, P l) -> P (leastB P) /\ forall m, P m -> le (leastB P) m.
Proof.
  intros [l hl]. unfold leastB. pose proof (inf_spec P) as h.
  destruct (inf P) as [k|]; [exact h|]. destruct (h l hl).
Qed.

Lemma leT_refl p : leT p p.
Proof. destruct p; cbn; auto. Qed.
Lemma leT_trans p q r : leT p q -> leT q r -> leT p r.
Proof.
  destruct p as [a|], q as [b|], r as [c|]; cbn; intros h1 h2; try exact I; try contradiction.
  exact (le_trans _ _ _ h1 h2).
Qed.
Lemma leT_bot p : leT p (Some bot) -> p = Some bot.
Proof. destruct p as [a|]; cbn; [intros h; rewrite (le_antisym _ _ h (bot_le a)); reflexivity | intros []]. Qed.
(** A truth value below no stage is [∞]. *)
Lemma leT_none p : (forall k, ~ leT p (Some k)) -> p = None.
Proof. destruct p as [a|]; [intros h; destruct (h a (le_refl a)) | reflexivity]. Qed.
Lemma leT_by_eq p q r : p = q -> leT q r -> leT p r.
Proof. intros e h. rewrite e. exact h. Qed.

(** ** Staged sets *)

(** A staged set [X = (|X|, ν)]: a set [|X| = carrier X] with the birthday function
    [ν = birth X : |X| → L]. *)
#[universes(polymorphic, cumulative)]
Record SSet@{u} := mkS { carrier : Type@{u}; birth : carrier -> L }.
Arguments mkS : clear implicits.

(** [⌞p⌟ = ({∗}, ∗ ↦ p)] for [p ∈ L], and [⌞∞⌟ = ∅]. *)
Definition DecT (p : TV) : Set := match p with Some _ => unit | None => Empty_set end.
Definition decB (p : TV) : DecT p -> L :=
  match p as p0 return DecT p0 -> L with Some l => fun _ => l | None => fun e => match e with end end.
Definition decode@{u} (p : TV) : SSet@{u} := mkS (DecT p) (decB p).

Lemma DecT_sub (p : TV) (x y : DecT p) : x = y.
Proof. destruct p; destruct x, y; reflexivity. Qed.
Lemma DecT_val (p : TV) (x : DecT p) : p = Some (decB p x).
Proof. destruct p; [reflexivity | destruct x]. Qed.
Definition decIntro (p : TV) (h : p <> None) : DecT p :=
  match p as p0 return p0 <> None -> DecT p0 with
  | Some _ => fun _ => tt | None => fun h => match h eq_refl with end end h.
Lemma decB_intro (p : TV) (h : p <> None) (l : L) : p = Some l -> decB p (decIntro p h) = l.
Proof. destruct p; [intros e; injection e; auto | intros e; discriminate]. Qed.

(** The birthday of a staged set, [ν(X) = min {ν(x) | x ∈ |X|} ∈ L∞]. *)
Definition nuS@{u} (X : SSet@{u}) : TV := inf (fun l => exists x : carrier X, birth X x = l).

Lemma nuS_le@{u} (X : SSet@{u}) (k : L) : leT (nuS X) (Some k) <-> exists x, le (birth X x) k.
Proof.
  unfold nuS. split.
  - intros h. apply inf_le in h. destruct h as [l [[x hx] hk]]. exists x. rewrite hx. exact hk.
  - intros [x hx]. apply inf_le. exists (birth X x). split; [exists x; reflexivity | exact hx].
Qed.
Lemma nuS_lb@{u} (X : SSet@{u}) (x : carrier X) : leT (nuS X) (Some (birth X x)).
Proof. apply nuS_le. exists x. apply le_refl. Qed.
Lemma nuS_ne@{u} (X : SSet@{u}) (x : carrier X) : nuS X <> None.
Proof. intros e. pose proof (nuS_lb X x) as h. rewrite e in h. exact h. Qed.

(** An element of least birthday of a nonempty staged set, chosen in the metatheory. *)
Lemma min_ex@{u} (X : SSet@{u}) : (exists x : carrier X, True) ->
  exists x : carrier X, forall y, le (birth X x) (birth X y).
Proof.
  intros [x _]. destruct (exists_least (fun l => exists x, birth X x = l)) as [l [[m hm] hl]].
  - exists (birth X x). exists x. reflexivity.
  - exists m. intros y. rewrite hm. apply hl. exists y. reflexivity.
Qed.
Definition minElt@{u} (X : SSet@{u}) (h : exists x : carrier X, True) : carrier X :=
  val (choice (fun x => forall y, le (birth X x) (birth X y)) (min_ex X h)).
Lemma minElt_min@{u} (X : SSet@{u}) h y : le (birth X (minElt X h)) (birth X y).
Proof. exact (prf (choice (fun x => forall y, le (birth X x) (birth X y)) (min_ex X h)) y). Qed.
Lemma minElt_nu@{u} (X : SSet@{u}) h l : nuS X = Some l -> le (birth X (minElt X h)) l.
Proof.
  intros e. pose proof (nuS_le X l) as [hk _]. rewrite e in hk.
  destruct (hk (le_refl l)) as [y hy]. exact (le_trans _ _ _ (minElt_min X h y) hy).
Qed.
Lemma DecT_inh@{u} (X : SSet@{u}) (d : DecT (nuS X)) : exists x : carrier X, True.
Proof.
  pose proof (DecT_val _ d) as e. pose proof (inf_spec (fun l => exists x : carrier X, birth X x = l)) as h.
  fold (nuS X) in h. rewrite e in h. destruct h as [[x _] _]. exists x. exact I.
Qed.

(** ** The staged product *)

(** [𝚷(X, Y)]: the functions [f] with [f(x) ∈ |Y(x)|] such that, for some [ℓ ∈ L],
    [ν(f(x)) ≤ max(ν(x), ℓ)] for all [x ∈ |X|] ([bndPi X Y f ℓ]); [ν(f)] is the least such [ℓ]. *)
Definition bndPi@{u} (X : SSet@{u}) (Y : carrier X -> SSet@{u}) (f : forall x, carrier (Y x)) (l : L) : Prop :=
  forall x, le (birth (Y x) (f x)) (maxL (birth X x) l).
Definition SPi@{u} (X : SSet@{u}) (Y : carrier X -> SSet@{u}) : SSet@{u} :=
  mkS (Sub (forall x, carrier (Y x)) (fun f => exists l, bndPi X Y f l)) (fun f => leastB (bndPi X Y (val f))).

Lemma SPi_bnd@{u} (X : SSet@{u}) (Y : carrier X -> SSet@{u}) (f : carrier (SPi X Y)) :
  bndPi X Y (val f) (birth (SPi X Y) f).
Proof. exact (proj1 (leastB_spec _ (prf f))). Qed.
Lemma SPi_least@{u} (X : SSet@{u}) (Y : carrier X -> SSet@{u}) (f : carrier (SPi X Y)) l :
  bndPi X Y (val f) l -> le (birth (SPi X Y) f) l.
Proof. exact (proj2 (leastB_spec _ (prf f)) l). Qed.
Definition mkPi@{u} (X : SSet@{u}) (Y : carrier X -> SSet@{u}) (g : forall x, carrier (Y x)) l
    (h : bndPi X Y g l) : carrier (SPi X Y) :=
  mkSub g (ex_intro _ l h).

(** ** Families of staged sets over a context *)

(** The staged sum [𝚺(Γ, A)], the context extension [Γ.A]: the pairs [(γ, a)] with
    [ν(γ, a) = max(ν(γ), ν(a))]. [Γ] has level [t], and the family [A] has level [u <= t]. *)
Definition extS@{u t | u <= t} (Γ : SSet@{t}) (A : carrier Γ -> SSet@{u}) : SSet@{t} :=
  mkS (Sig (carrier Γ) (fun γ => carrier (A γ))) (fun x => maxL (birth Γ (fst x)) (birth (A (fst x)) (snd x))).

Section Fam.
(** [t]: the universe of discourse, which contains every staged set of the model, contexts
    and types alike. [u <= t]: the level of the families [A] and [B]; it is [t] for the
    types of the model and the level of the codes for families of codes. *)
Universes u t.
Constraint u <= t.
Context {Γ : SSet@{t}} (A : carrier Γ -> SSet@{u}) (B : carrier (extS@{u t} Γ A) -> SSet@{u}).

(** [B_γ = a ↦ B(γ, a)], and [Π(A, B)(γ) = 𝚷(A(γ), B_γ)], with application, abstraction
    and the bounds of the staged product. *)
Definition fib (γ : carrier Γ) (a : carrier (A γ)) : SSet@{u} :=
  B (@mkSig@{t} (carrier Γ) (fun γ => carrier (A γ)) γ a).
Definition PiS (γ : carrier Γ) : SSet@{u} := SPi (A γ) (fib γ).

Definition piApp {γ : carrier Γ} (s : carrier (PiS γ)) (a : carrier (A γ)) : carrier (fib γ a) := val s a.
Definition piMk {γ : carrier Γ} (g : forall a, carrier (fib γ a)) (l : L) (h : bndPi (A γ) (fib γ) g l) :
  carrier (PiS γ) := mkPi (A γ) (fib γ) g l h.
Definition piApp_bound {γ : carrier Γ} (s : carrier (PiS γ)) (a : carrier (A γ)) :
  le (birth (fib γ a) (piApp s a)) (maxL (birth (A γ) a) (birth (PiS γ) s)) := SPi_bnd (A γ) (fib γ) s a.
Definition piMk_birth {γ : carrier Γ} (g : forall a, carrier (fib γ a)) l (h : bndPi (A γ) (fib γ) g l) :
  le (birth (PiS γ) (piMk g l h)) l := SPi_least (A γ) (fib γ) (piMk g l h) l h.
Lemma piExt {γ : carrier Γ} (s s' : carrier (PiS γ)) : (forall a, piApp s a = piApp s' a) -> s = s'.
Proof. intros h. apply sub_eq. exact (funext _ _ h). Qed.
Definition piBirth_least {γ : carrier Γ} (s : carrier (PiS γ)) l :
  bndPi (A γ) (fib γ) (piApp s) l -> le (birth (PiS γ) s) l := SPi_least (A γ) (fib γ) s l.

End Fam.

(** ** Well-founded trees *)

(** The trees [sup(x, f)] of the set-theoretic W-type of [|X|] and [x ↦ |Y(x)|]. *)
#[universes(polymorphic, cumulative)]
Inductive WT@{u} (X : Type@{u}) (Y : X -> Type@{u}) : Type@{u} :=
  wsup : forall x : X, (Y x -> WT X Y) -> WT X Y.
Arguments wsup {X Y} x f.

Section WSet.
(** [u]: the level of [X] and of the [Y x]; the W-type [WS] stays at level [u]. *)
Universe u.
Context (X : SSet@{u}) (Y : carrier X -> SSet@{u}).

(** [W(X, Y)]: the trees [sup(x, f)] with [f ∈ 𝚷(Y(x), W(X, Y))], born at
    [ν(sup(x, f)) = max(ν(x), ν(f))], where [ν(f)] is the least [ℓ] with
    [ν(f(y)) ≤ max(ν(y), ℓ)] for all [y]. [wgood] selects the trees whose subtrees all
    have such a bound. *)
Definition wbnd (x : carrier X) (f : carrier (Y x) -> L) (l : L) : Prop :=
  forall y, le (f y) (maxL (birth (Y x) y) l).
Fixpoint wbirth (w : WT (carrier X) (fun x => carrier (Y x))) : L :=
  match w with wsup x f => maxL (birth X x) (leastB (wbnd x (fun y => wbirth (f y)))) end.
Fixpoint wgood (w : WT (carrier X) (fun x => carrier (Y x))) : Prop :=
  match w with wsup x f => (forall y, wgood (f y)) /\ exists l, wbnd x (fun y => wbirth (f y)) l end.
Definition WS : SSet@{u} := mkS (Sub (WT (carrier X) (fun x => carrier (Y x))) wgood) (fun w => wbirth (val w)).
End WSet.

(** [W(A, B)(γ) = W(A(γ), B_γ)]. *)
Definition WFam@{u t | u <= t} {Γ : SSet@{t}} (A : carrier Γ -> SSet@{u})
    (B : carrier (extS@{u t} Γ A) -> SSet@{u}) (γ : carrier Γ) : SSet@{u} :=
  WS (A γ) (fib@{u t} A B γ).

Definition birth_tr@{u t} {T : Type@{u}} (F : T -> SSet@{t}) {x y : T} (e : x = y) (c : carrier (F x)) :
    birth (F y) (tr (fun z => carrier (F z)) e c) = birth (F x) c :=
  match e as e0 in _ = y0 return birth (F y0) (tr (fun z => carrier (F z)) e0 c) = birth (F x) c
  with eq_refl => eq_refl end.

(** ** Quotients of staged sets *)

Section QSet.
(** [u]: the level of [X]; the quotient [QS] stays at level [u]. *)
Universe u.
Context (X : SSet@{u}) (R : carrier X -> carrier X -> Prop).

(** [X/R]: the classes [[x]] of the equivalence relation [eqc] generated by [R], each born
    at the least birthday of a member, with a member [rep c] of least birthday chosen in
    the metatheory. *)
#[universes(cumulative)]
Inductive eqc : carrier X -> carrier X -> Prop :=
  | eqc_step x y : R x y -> eqc x y
  | eqc_refl x : eqc x x
  | eqc_sym x y : eqc x y -> eqc y x
  | eqc_trans x y z : eqc x y -> eqc y z -> eqc x z.

Definition isCls (c : carrier X -> Prop) : Prop := exists x, c = eqc x.
Definition clsBirth (c : carrier X -> Prop) : L := leastB (fun l => exists x, c x /\ birth X x = l).
Definition QS : SSet@{u} := mkS (Sub (carrier X -> Prop) isCls) (fun c => clsBirth (val c)).
Definition cls (x : carrier X) : carrier QS := mkSub (P := isCls) (eqc x) (ex_intro (fun y => eqc x = eqc y) x eq_refl).

Lemma eqc_ext x y : eqc x y -> eqc x = eqc y.
Proof.
  intros h. apply funext. intros z. apply propext.
  split; intros k; [exact (eqc_trans _ _ _ (eqc_sym _ _ h) k) | exact (eqc_trans _ _ _ h k)].
Qed.
Lemma cls_eq x y : eqc x y -> cls x = cls y.
Proof. intros h. apply sub_eq. exact (eqc_ext x y h). Qed.
Lemma cls_mem (c : carrier QS) : exists x, val c x.
Proof. destruct (prf c) as [x e]. exists x. exact (tr (fun P : Prop => P) (inv (ap (fun f => f x) e)) (eqc_refl x)). Qed.
Lemma rep_ex (c : carrier QS) : exists x, val c x /\ forall y, val c y -> le (birth X x) (birth X y).
Proof.
  destruct (exists_least (fun l => exists x, val c x /\ birth X x = l)) as [l [[x [hx e]] hl]].
  - destruct (cls_mem c) as [x hx]. exists (birth X x). exists x. split; [exact hx | reflexivity].
  - exists x. split; [exact hx|]. intros y hy. rewrite e. apply hl. exists y. split; [exact hy | reflexivity].
Qed.

Definition rep (c : carrier QS) : carrier X :=
  val (choice (fun x => val c x /\ forall y, val c y -> le (birth X x) (birth X y)) (rep_ex c)).
Lemma rep_spec (c : carrier QS) : val c (rep c) /\ forall y, val c y -> le (birth X (rep c)) (birth X y).
Proof. exact (prf (choice (fun x => val c x /\ forall y, val c y -> le (birth X x) (birth X y)) (rep_ex c))). Qed.

(** [[rep c] = c], [x ~ rep [x]], [ν(rep c) = ν(c)] and [ν([x]) ≤ ν(x)]. *)
Lemma cls_rep (c : carrier QS) : cls (rep c) = c.
Proof.
  apply sub_eq. cbn. destruct (prf c) as [x e].
  pose proof (tr (fun P : Prop => P) (ap (fun f => f (rep c)) e) (and1 (rep_spec c))) as h.
  exact (cat (inv (eqc_ext x (rep c) h)) (inv e)).
Qed.
Lemma rep_cls x : eqc x (rep (cls x)).
Proof. exact (and1 (rep_spec (cls x))). Qed.
Lemma rep_birth (c : carrier QS) : birth X (rep c) = birth QS c.
Proof.
  cbn. unfold clsBirth.
  assert (ex : exists l, exists x, val c x /\ birth X x = l)
    by (exists (birth X (rep c)); exists (rep c); split; [exact (and1 (rep_spec c)) | reflexivity]).
  destruct (leastB_spec _ ex) as [[m [hm e]] hl]. apply le_antisym.
  - rewrite <- e. exact (and2 (rep_spec c) m hm).
  - apply hl. exists (rep c). split; [exact (and1 (rep_spec c)) | reflexivity].
Qed.
Lemma cls_birth x : le (birth QS (cls x)) (birth X x).
Proof.
  cbn. unfold clsBirth.
  exact (and2 (leastB_spec _ (ex_intro _ _ (ex_intro _ x (conj (eqc_refl x) eq_refl)))) _
           (ex_intro _ x (conj (eqc_refl x) eq_refl))).
Qed.
End QSet.

(** [(A/R)(γ) = A(γ)/R_γ], where [a R_γ b] iff [R(γ, a, b) ≠ ∞]. *)
Definition QFam@{u t | Set < u, u <= t} {Γ : SSet@{t}} (A : carrier Γ -> SSet@{u})
    (R : carrier (extS@{u t} (extS@{u t} Γ A) (fun x => A (fst x))) -> TV) (γ : carrier Γ) : SSet@{u} :=
  QS (A γ) (fun a b => R (@mkSig@{t} _ (fun x => carrier (A (fst x))) (@mkSig@{t} _ (fun γ => carrier (A γ)) γ a) b) <> None).

(** [Δ Stg_i]: the staged sets of level [i], as a staged set of level [j > i], all born at [0]. *)
Definition uSat@{i j | i < j} : SSet@{j} := mkS@{j} SSet@{i} (fun _ => bot).

(** Transport lemmas. *)
Lemma tr_cong@{u v} {T : Type@{u}} (P : T -> Type@{v}) {x y : T} (e e' : x = y) (p q : P x) :
  p = q -> tr P e p = tr P e' q.
Proof. intros h. destruct (proof_irrel e e'). destruct h. reflexivity. Qed.
Lemma tr_irrel_l@{u v} {A : Type@{u}} (P : A -> Type@{v}) {x : A} (e : x = x) (p q : P x) :
  p = q -> tr P e p = q.
Proof. intros h. rw (tr_irrel P e p). exact h. Qed.

(** * Part III. The model *)

(** ** The category with families of staged sets *)

Section CwFS.
(** [t]: the universe of discourse; every staged set of the model, context or type, lives in
    [SSet@{t}]. [c1], [c2]: the levels of the collections of contexts and of types over a
    context. *)
Universes t c1 c2.
Constraint Set < t.
Constraint t < c1.
Constraint t < c2.

(** A context is a staged set of level [t], and a context morphism [σ : Δ → Γ] a staged map:
    [ν(σ(x)) ≤ ν(x)] for all [x ∈ |Δ|]. *)
Definition SHom (Δ Γ : SSet@{t}) : Type@{t} :=
  Sub (carrier Δ -> carrier Γ) (fun f => forall x, le (birth Γ (f x)) (birth Δ x)).
(** A type over [Γ] is a family [A : |Γ| → Stg], and a term of type [A] a section: a
    function [t] with [t(γ) ∈ |A(γ)|] and [ν(t(γ)) ≤ ν(γ)]. *)
Definition STy (Γ : SSet@{t}) : Type@{c2} := carrier Γ -> SSet@{t}.
Definition STm (Γ : SSet@{t}) (A : STy Γ) : Type@{t} :=
  Sub (forall γ, carrier (A γ)) (fun f => forall γ, le (birth (A γ) (f γ)) (birth Γ γ)).

(** Constructors of morphisms and terms, and extensionality. *)
Definition mkHom {Δ Γ : SSet@{t}} (f : carrier Δ -> carrier Γ)
    (h : forall x, le (birth Γ (f x)) (birth Δ x)) : SHom Δ Γ :=
  @mkSub _ (fun f => forall x, le (birth Γ (f x)) (birth Δ x)) f h.
Definition mkTm {Γ : SSet@{t}} {A : STy Γ} (f : forall γ, carrier (A γ))
    (h : forall γ, le (birth (A γ) (f γ)) (birth Γ γ)) : STm Γ A :=
  @mkSub _ (fun f => forall γ, le (birth (A γ) (f γ)) (birth Γ γ)) f h.

Lemma tm_eq {Γ : SSet@{t}} {A : STy Γ} (s s' : STm Γ A) : (forall γ, val s γ = val s' γ) -> s = s'.
Proof. intros h. apply sub_eq. apply funext. exact h. Qed.
(** Extensionality for types, at the level [c2] of types. *)
Definition sty_ext {Γ : SSet@{t}} (A B : STy Γ) (h : forall γ, A γ = B γ) : A = B := funext@{t c2} A B h.

Lemma hom_eq {Δ Γ : SSet@{t}} (σ τ : SHom Δ Γ) : (forall x, val σ x = val τ x) -> σ = τ.
Proof. intros h. apply sub_eq. apply funext. exact h. Qed.

(** [id], [σ ∘ δ], the empty context [⋄ = ⌞0⌟], [A[σ] = A ∘ σ], [t[σ] = t ∘ σ],
    [Γ.A = 𝚺(Γ, A)] with [p(γ, a) = γ] and [q(γ, a) = a], and [⟨σ, t⟩(δ) = (σ(δ), t(δ))]. *)
Definition sId (Γ : SSet@{t}) : SHom Γ Γ := mkHom (Δ := Γ) (Γ := Γ) (fun x => x) (fun x => le_refl _).
Definition sComp {Θ Δ Γ : SSet@{t}} (σ : SHom Δ Γ) (δ : SHom Θ Δ) : SHom Θ Γ :=
  mkHom (Δ := Θ) (Γ := Γ) (fun x => val σ (val δ x)) (fun x => le_trans _ _ _ (prf σ (val δ x)) (prf δ x)).
Definition sEmpty : SSet@{t} := mkS unit (fun _ => bot).
Definition sToEmpty (Γ : SSet@{t}) : SHom Γ sEmpty := mkHom (Δ := Γ) (Γ := sEmpty) (fun _ => Datatypes.tt) (fun x => bot_le _).
Definition sSub {Δ Γ : SSet@{t}} (A : STy Γ) (σ : SHom Δ Γ) : STy Δ := fun δ => A (val σ δ).
Definition sSubTm {Δ Γ : SSet@{t}} {A : STy Γ} (a : STm Γ A) (σ : SHom Δ Γ) : STm Δ (sSub A σ) :=
  mkTm (Γ := Δ) (A := sSub A σ) (fun δ => val a (val σ δ)) (fun δ => le_trans _ _ _ (prf a (val σ δ)) (prf σ δ)).
Definition sExt (Γ : SSet@{t}) (A : STy Γ) : SSet@{t} := extS@{t t} Γ A.
Definition sP {Γ : SSet@{t}} (A : STy Γ) : SHom (sExt Γ A) Γ := mkHom (Δ := sExt Γ A) (Γ := Γ) (fun x => fst x) (fun x => le_max_l _ _).
Definition sQ {Γ : SSet@{t}} (A : STy Γ) : STm (sExt Γ A) (sSub A (sP A)) :=
  mkTm (Γ := sExt Γ A) (A := sSub A (sP A)) (fun x => snd x) (fun x => le_max_r _ _).
Definition sPair {Δ Γ : SSet@{t}} {A : STy Γ} (σ : SHom Δ Γ) (a : STm Δ (sSub A σ)) : SHom Δ (sExt Γ A) :=
  mkHom (Δ := Δ) (Γ := sExt Γ A) (fun δ => mkSig (val σ δ) (val a δ)) (fun δ => max_lub _ _ _ (prf σ δ) (prf a δ)).

(** The laws of the CwF hold by function extensionality and computation. *)
Lemma sId_comp {Δ Γ : SSet@{t}} (σ : SHom Δ Γ) : sComp (sId Γ) σ = σ.
Proof. apply hom_eq. reflexivity. Qed.
Lemma sComp_id {Δ Γ : SSet@{t}} (σ : SHom Δ Γ) : sComp σ (sId Δ) = σ.
Proof. apply hom_eq. reflexivity. Qed.
Lemma sComp_assoc {Ξ Θ Δ Γ : SSet@{t}} (σ : SHom Δ Γ) (δ : SHom Θ Δ) (ε : SHom Ξ Θ) :
  sComp (sComp σ δ) ε = sComp σ (sComp δ ε).
Proof. apply hom_eq. reflexivity. Qed.
Lemma sToEmpty_unique {Γ : SSet@{t}} (σ : SHom Γ sEmpty) : σ = sToEmpty Γ.
Proof. apply hom_eq. intros x. destruct (val σ x). reflexivity. Qed.
Lemma sTm_sub_id {Γ : SSet@{t}} {A : STy Γ} (a : STm Γ A) : tr (STm Γ) eq_refl (sSubTm a (sId Γ)) = a.
Proof. apply tm_eq. reflexivity. Qed.
Lemma sTm_sub_comp {Θ Δ Γ : SSet@{t}} {A : STy Γ} (a : STm Γ A) (σ : SHom Δ Γ) (δ : SHom Θ Δ) :
  tr (STm Θ) eq_refl (sSubTm a (sComp σ δ)) = sSubTm (sSubTm a σ) δ.
Proof. apply tm_eq. reflexivity. Qed.
Lemma sPair_proj {Δ Γ : SSet@{t}} {A : STy Γ} (σ : SHom Δ Γ) (a : STm Δ (sSub A σ)) :
  sComp (sP A) (sPair σ a) = σ.
Proof. apply hom_eq. reflexivity. Qed.
Lemma sPair_var {Δ Γ : SSet@{t}} {A : STy Γ} (σ : SHom Δ Γ) (a : STm Δ (sSub A σ)) :
  tr (STm Δ) (cat (inv eq_refl) (ap (fun s => sSub A s) (sPair_proj σ a))) (sSubTm (sQ A) (sPair σ a)) = a.
Proof. apply tr_irrel_l. apply tm_eq. reflexivity. Qed.
Lemma sPair_eta {Δ Γ : SSet@{t}} {A : STy Γ} (τ : SHom Δ (sExt Γ A)) :
  sPair (sComp (sP A) τ) (tr (STm Δ) (inv eq_refl) (sSubTm (sQ A) τ)) = τ.
Proof. apply hom_eq. reflexivity. Qed.

(** The CwF of staged sets. The equations of types hold by [eq_refl]. *)
Definition stagedCwF : CwF@{c1 t c2 t} := {|
  Ctx := SSet@{t}; Hom := SHom; idH := sId; comp := fun Θ Δ Γ σ δ => sComp σ δ;
  id_comp := fun Δ Γ σ => sId_comp σ; comp_id := fun Δ Γ σ => sComp_id σ;
  comp_assoc := fun Ξ Θ Δ Γ σ δ ε => sComp_assoc σ δ ε;
  empty := sEmpty; toEmpty := sToEmpty; toEmpty_unique := fun Γ σ => sToEmpty_unique σ;
  Ty := STy; Tm := STm; sub := fun Δ Γ A σ => sSub A σ; subTm := fun Δ Γ A a σ => sSubTm a σ;
  ty_sub_id := fun Γ A => eq_refl; ty_sub_comp := fun Θ Δ Γ A σ δ => eq_refl;
  tm_sub_id := fun Γ A a => sTm_sub_id a; tm_sub_comp := fun Θ Δ Γ A a σ δ => sTm_sub_comp a σ δ;
  ext := sExt; pp := fun Γ A => sP A; qq := fun Γ A => sQ A; pair := fun Δ Γ A σ a => sPair σ a;
  pair_proj := fun Δ Γ A σ a => sPair_proj σ a; pair_var := fun Δ Γ A σ a => sPair_var σ a;
  pair_eta := fun Δ Γ A τ => sPair_eta τ |}.

Local Notation SC := stagedCwF.

(** [kill e] replaces an equation [e] between convertible types by [eq_refl]. *)
Ltac kill e := rw (proof_irrel e eq_refl); cbn.
(** [killet] does the same for an equation given by a [let] in the goal. *)
Ltac killet := let e := fresh "e" in intro e; clearbody e; kill e.
(** [killtr] collapses every transport in the goal along an equation between convertible sides. *)
Ltac killtr :=
  unfold trTm, trTy in *;
  repeat match goal with
  | |- context [tr ?P ?e ?x] =>
      lazymatch e with eq_refl => fail | _ => rw (proof_irrel e eq_refl) end
  end; cbn.

(** Two inequalities. *)
Lemma le_by_eq x y z : x = y -> le y z -> le x z.
Proof. intros e h. rewrite e. exact h. Qed.

Lemma max_comm_le a b : le (maxL a b) (maxL b a).
Proof. apply max_lub; [apply le_max_r | apply le_max_l]. Qed.

(** ** Π *)

(** [Π(A, B)(γ) = 𝚷(A(γ), B_γ)], [(λb)(γ) = (a ↦ b(γ, a))], born by [ν(γ)], and
    [(app s)(γ, a) = s(γ)(a)]. *)
Definition sPi {Γ : SSet@{t}} (A : STy Γ) (B : STy (sExt Γ A)) : STy Γ := PiS@{t t} A B.

Definition sLam {Γ : SSet@{t}} {A : STy Γ} {B : STy (sExt Γ A)} (b : STm (sExt Γ A) B) : STm Γ (sPi A B) :=
  mkTm (A := sPi A B)
    (fun γ => piMk A B (fun a => val b (mkSig γ a)) (birth Γ γ)
                (fun a => le_trans _ _ _ (prf b (mkSig γ a)) (max_comm_le _ _)))
    (fun γ => piMk_birth A B _ _ _).
Definition sApp {Γ : SSet@{t}} {A : STy Γ} {B : STy (sExt Γ A)} (s : STm Γ (sPi A B)) : STm (sExt Γ A) B :=
  mkTm (A := B) (fun x => piApp A B (val s (fst x)) (snd x))
    (fun x => le_trans _ _ _ (piApp_bound A B (val s (fst x)) (snd x))
                (le_trans _ _ _ (max_lub _ _ _ (le_max_l _ _) (le_max_r' _ _ _ (prf s (fst x)))) (max_comm_le _ _))).

(** β, η and [(λt)[σ] = λ(t[σ⁺])] hold by function extensionality and computation. *)
Definition stPi : PiF (C := SC).
Proof.
  refine {|
    Pi := fun (Γ : Ctx SC) A B => sPi A B;
    pi_sub := fun Δ Γ A B σ => eq_refl;
    lam := fun Γ A B b => sLam b;
    app := fun Γ A B s => sApp s;
    pi_beta := _; pi_eta := _; lam_sub := _
  |}.
  - intros Γ A B b. apply tm_eq. intros x. reflexivity.
  - intros Γ A B s0. apply tm_eq. intros γ. apply piExt. intros a. reflexivity.
  - intros Δ Γ A B b σ. apply tm_eq. intros δ. apply piExt. intros a. reflexivity.
Defined.

(** ** Σ *)

(** [Σ(A, B)(γ) = 𝚺(A(γ), B_γ)], with pairing [⟨t, u⟩(γ) = (t(γ), u(γ))] and the
    projections. *)
Section SigF.
(** [u <= t]: the level of the families [A] and [B], as in [Fam]; the sum [SigS] stays at
    level [u]. *)
Universes u.
Constraint u <= t.
Definition SigS {Γ : SSet@{t}} (A : carrier Γ -> SSet@{u}) (B : carrier (extS@{u t} Γ A) -> SSet@{u})
    (γ : carrier Γ) : SSet@{u} :=
  mkS (Sig (carrier (A γ)) (fun a => carrier (fib A B γ a)))
      (fun p => maxL (birth (A γ) (fst p)) (birth (fib A B γ (fst p)) (snd p))).
End SigF.

Definition sSigma {Γ : SSet@{t}} (A : STy Γ) (B : STy (sExt Γ A)) : STy Γ := SigS@{t} A B.

Definition stSigma : SigmaF (C := SC).
Proof.
  refine {|
    Sigma := fun (Γ : Ctx SC) A B => sSigma A B;
    sigma_sub := fun Δ Γ A B σ => eq_refl;
    spair := fun Γ A B a b => mkTm (A := sSigma A B) (fun γ => mkSig (val a γ) (val b γ))
               (fun γ => max_lub _ _ _ (prf a γ) (prf b γ));
    sfst := fun Γ A B s => mkTm (A := A) (fun γ => fst (val s γ)) (fun γ => le_trans _ _ _ (le_max_l _ _) (prf s γ));
    ssnd := fun Γ A B s => mkTm (A := sSub B (sec (C := SC) (mkTm (A := A) (fun γ => fst (val s γ))
                                                 (fun γ => le_trans _ _ _ (le_max_l _ _) (prf s γ)))))
               (fun γ => snd (val s γ)) (fun γ => le_trans _ _ _ (le_max_r _ _) (prf s γ));
    sigma_fst := fun Γ A B a b => ltac:(apply tm_eq; reflexivity);
    sigma_snd := fun Γ A B a b => ltac:(unfold trTm; apply tr_irrel_l; apply tm_eq; reflexivity);
    sigma_eta := fun Γ A B s => ltac:(apply tm_eq; reflexivity);
    spair_sub := fun Δ Γ σ A B a b => ltac:(killet; apply tm_eq; reflexivity);
    sfst_sub := fun Δ Γ σ A B s => ltac:(apply tm_eq; reflexivity);
    ssnd_sub := fun Δ Γ σ A B s => ltac:(killet; apply tm_eq; reflexivity)
  |}.
Defined.

(** ** The finite types *)

(** The finite types [0 = Δ∅], [1 = Δ{∗}] and [2 = Δ{tt, ff}]; the eliminator of [2] is
    the case distinction on [b(γ)]. *)
Definition zeroS@{u} : SSet@{u} := mkS Empty_set (fun e => match e with end).
Definition oneS@{u} : SSet@{u} := mkS unit (fun _ => bot).
Definition twoS@{u} : SSet@{u} := mkS bool (fun _ => bot).

Definition sTwoElim {Γ : SSet@{t}} (Cm : STy (sExt Γ (fun _ => twoS@{t})))
    (ct : STm Γ (sSub Cm (sec (C := SC) (mkTm (A := fun _ => twoS@{t}) (fun _ => true) (fun _ => bot_le _)))))
    (cf : STm Γ (sSub Cm (sec (C := SC) (mkTm (A := fun _ => twoS@{t}) (fun _ => false) (fun _ => bot_le _)))))
    (b : STm Γ (fun _ => twoS@{t})) : STm Γ (sSub Cm (sec (C := SC) b)).
Proof.
  refine (mkTm (A := sSub Cm (sec (C := SC) b))
    (fun γ => match val b γ as x return carrier (Cm (mkSig γ x)) with
              | true => val ct γ | false => val cf γ end) _).
  intros γ.
  change (le (birth (Cm (mkSig γ (val b γ)))
                (match val b γ as x return carrier (Cm (mkSig γ x)) with
                 | true => val ct γ | false => val cf γ end)) (birth Γ γ)).
  destruct (val b γ); [exact (prf ct γ) | exact (prf cf γ)].
Defined.

Definition stFin : FinF (C := SC).
Proof.
  refine {|
    zero := fun (Γ : Ctx SC) _ => zeroS@{t};
    zero_sub := fun Δ Γ σ => eq_refl;
    zero_elim := fun Γ Cm a => mkTm (A := sSub Cm (sec (C := SC) a))
                   (fun γ => match val a γ with end) (fun γ => match val a γ with end);
    one := fun Γ _ => oneS@{t};
    one_sub := fun Δ Γ σ => eq_refl;
    star := fun Γ => mkTm (A := fun _ => oneS@{t}) (fun _ => Datatypes.tt) (fun _ => bot_le _);
    two := fun Γ _ => twoS@{t};
    two_sub := fun Δ Γ σ => eq_refl;
    ttT := fun Γ => mkTm (A := fun _ => twoS@{t}) (fun _ => true) (fun _ => bot_le _);
    ffT := fun Γ => mkTm (A := fun _ => twoS@{t}) (fun _ => false) (fun _ => bot_le _);
    two_elim := fun Γ Cm ct cf b => sTwoElim Cm ct cf b;
    zero_elim_sub := fun Δ Γ σ Cm a => ltac:(killet; apply tm_eq; intros δ; destruct (val a (val σ δ)));
    star_sub := fun Δ Γ σ => ltac:(apply tm_eq; reflexivity);
    one_eta := fun Γ a => ltac:(apply tm_eq; intros γ; destruct (val a γ); reflexivity);
    tt_sub := fun Δ Γ σ => ltac:(apply tm_eq; reflexivity);
    ff_sub := fun Δ Γ σ => ltac:(apply tm_eq; reflexivity);
    two_elim_tt := fun Γ Cm ct cf => ltac:(apply tm_eq; reflexivity);
    two_elim_ff := fun Γ Cm ct cf => ltac:(apply tm_eq; reflexivity);
    two_elim_sub := fun Δ Γ σ Cm ct cf b =>
      ltac:(intros e1 e2 e3; clearbody e1 e2 e3; kill e1; kill e2; kill e3; apply tm_eq; intros δ; reflexivity)
  |}.
Defined.

(** ** Propositions *)

(** [Prop = Δ L∞], the constant family of the truth values, all born at [0], and
    [El φ = γ ↦ ⌞φ(γ)⌟]. *)
Definition tvS@{u} : SSet@{u} := mkS TV (fun _ => bot).
Definition sProp (Γ : SSet@{t}) : STy Γ := fun _ => tvS@{t}.
Definition sPrf {Γ : SSet@{t}} (φ : STm Γ (sProp Γ)) : STy Γ := fun γ => decode@{t} (val φ γ).
(** [∀(A, φ)(γ) = ν(𝚷(A(γ), ⌞φ(γ, -)⌟))]. *)
Definition sAll {Γ : SSet@{t}} (A : STy Γ) (φ : STm (sExt Γ A) (sProp _)) : STm Γ (sProp Γ) :=
  mkTm (A := sProp Γ) (fun γ => nuS (SPi (A γ) (fun a => decode@{t} (val φ (mkSig γ a))))) (fun γ => bot_le _).

(** Introduction: for a term [b] of [El φ] over [Γ.A], [(λb)(γ) ∈ 𝚷(A(γ), ⌞φ(γ, -)⌟)] is
    born by [ν(γ)], hence [∀(A, φ)(γ) ≤ ν(γ)]. *)
Definition sAllIntro {Γ : SSet@{t}} {A : STy Γ} {φ : STm (sExt Γ A) (sProp _)}
    (b : STm (sExt Γ A) (sPrf φ)) : STm Γ (sPrf (sAll A φ)).
Proof.
  refine (mkTm (A := sPrf (sAll A φ)) (fun γ => decIntro _ (nuS_ne _ (val (sLam b) γ))) _).
  intros γ. cbn.
  pose proof (leT_trans _ _ (Some (birth Γ γ)) (nuS_lb _ (val (sLam b) γ)) (prf (sLam b) γ)) as hl.
  rewrite (DecT_val _ (decIntro _ (nuS_ne _ (val (sLam b) γ)))) in hl. exact hl.
Defined.
(** Elimination: [app s'], with [s'(γ)] an element of [𝚷(A(γ), ⌞φ(γ, -)⌟)] of least
    birthday, chosen in the metatheory. *)
Definition sAllElim {Γ : SSet@{t}} {A : STy Γ} {φ : STm (sExt Γ A) (sProp _)}
    (s : STm Γ (sPrf (sAll A φ))) : STm (sExt Γ A) (sPrf φ).
Proof.
  refine (sApp (B := sPrf φ) (mkTm (A := sPi A (sPrf φ)) (fun γ => minElt _ (DecT_inh _ (val s γ))) _)).
  intros γ. exact (le_trans _ _ _ (minElt_nu _ _ _ (DecT_val _ (val s γ))) (prf s γ)).
Defined.

(** Proof irrelevance holds because [⌞p⌟] has at most one element. *)
Definition stProp : PropF (C := SC) :=
  @Build_PropF SC
    (fun Γ => sProp Γ)
    (fun Δ Γ σ => eq_refl)
    (fun Γ φ => sPrf φ)
    (fun Δ Γ σ φ => eq_refl)
    (fun Γ φ h h' => ltac:(apply tm_eq; intros; apply DecT_sub))
    (fun Γ A φ => sAll A φ)
    (fun Δ Γ σ A φ => ltac:(apply tm_eq; intros; reflexivity))
    (fun Γ A φ b => sAllIntro b)
    (fun Γ A φ s => sAllElim s).

(** ** Identity propositions *)

(** [Id_A(a, b)(γ) = 0] if [a(γ) = b(γ)], and [∞] otherwise. [refl a] is [γ ↦ ∗], and
    equality reflection holds because a term of [El Id_A(a, b)] gives [Id_A(a, b)(γ) ≠ ∞]. *)
Definition sIdP {Γ : SSet@{t}} (A : STy Γ) (a b : STm Γ A) : STm Γ (sProp Γ) :=
  mkTm (A := sProp Γ) (fun γ => if decb (val a γ = val b γ) then Some bot else None) (fun γ => bot_le _).

Lemma idv_refl {X : Type@{t}} (x : X) : (if decb (x = x) then Some bot else None) = Some bot.
Proof. rewrite (decb_true _ eq_refl). reflexivity. Qed.
Lemma idv_ne {X : Type@{t}} (x : X) : (if decb (x = x) then Some bot else None) <> None.
Proof. rewrite (idv_refl x). discriminate. Qed.

Definition sRefl {Γ : SSet@{t}} {A : STy Γ} (a : STm Γ A) : STm Γ (sPrf (sIdP A a a)) :=
  mkTm (A := sPrf (sIdP A a a)) (fun γ => decIntro _ (idv_ne (val a γ)))
    (fun γ => match inv (decB_intro _ (idv_ne (val a γ)) bot (idv_refl (val a γ))) in _ = l
                    return le l (birth Γ γ) with eq_refl => bot_le _ end).

Lemma sReflection {Γ : SSet@{t}} {A : STy Γ} {a b : STm Γ A} : STm Γ (sPrf (sIdP A a b)) -> a = b.
Proof.
  intros h. apply tm_eq. intros γ. pose proof (val h γ) as d. cbn in d. revert d.
  destruct (decb (val a γ = val b γ)) eqn:E; intros d; [exact (proj1 (decb_spec _) E) | destruct d].
Qed.

Definition stId : IdF (Pr := stProp) :=
  @Build_IdF SC stProp
    (fun Γ A a b => sIdP A a b)
    (fun Δ Γ σ A a b => ltac:(apply tm_eq; intros; reflexivity))
    (fun Γ A a => sRefl a)
    (fun Γ A a b h => sReflection h).

(** ** W-types *)

(** [W(A, B)(γ) = W(A(γ), B_γ)]. *)
Definition sW {Γ : SSet@{t}} (A : STy Γ) (B : STy (sExt Γ A)) : STy Γ := WFam@{t t} A B.

Section WTypes.
Context {Γ : SSet@{t}} (A : STy Γ) (B : STy (sExt Γ A)).
Local Notation Wt := (sW A B).
Local Notation W2 := (sSub (sSub (sW A B) (sP A)) (sP B)).
Local Notation wF' := (wF (C := SC) stPi A B (sW A B)).
Local Notation wCtx2' := (wCtx2 (C := SC) stPi A B (sW A B)).

(** [sup(γ, a, f) = sup(a, f)], with [ν(sup(a, f)) = max(ν(a), ν(f)) ≤ ν(γ, a, f)]. *)
Definition supVal (x : carrier wCtx2') : carrier (Wt (fst (fst x))).
Proof.
  refine (mkSub (P := wgood (A (fst (fst x))) (fib A B (fst (fst x))))
    (wsup (snd (fst x)) (fun b => val (piApp B W2 (snd x) b))) (conj (fun b => prf (piApp B W2 (snd x) b)) _)).
  exists (birth (PiS B W2 (fst x)) (snd x)). intros b. exact (piApp_bound B W2 (snd x) b).
Defined.

Lemma supVal_bound (x : carrier wCtx2') :
  le (birth (Wt (fst (fst x))) (supVal x)) (birth wCtx2' x).
Proof.
  destruct x as [[γ a] f]. cbn [fst snd].
  pose (P := wbnd (A γ) (fib A B γ) a (fun b => wbirth (A γ) (fib A B γ) (val (piApp B W2 f b)))).
  assert (hb : P (birth (PiS B W2 (mkSig γ a)) f)) by (intros b; exact (piApp_bound B W2 f b)).
  pose proof (proj2 (leastB_spec P (ex_intro _ _ hb)) _ hb) as h.
  change (le (maxL (birth (A γ) a) (leastB P))
             (maxL (maxL (birth Γ γ) (birth (A γ) a)) (birth (PiS B W2 (mkSig γ a)) f))).
  lsolve.
Qed.

Definition sSupT : STm wCtx2' (wSupTy (C := SC) stPi A B Wt) :=
  mkTm (A := wSupTy (C := SC) stPi A B Wt) supVal supVal_bound.

(** The recursor for a type [C] over [Γ.W(A, B)] and a step term [m], by structural
    recursion on the trees: [rec(γ, sup(a, f)) = m(γ)(a)(f)(b ↦ rec(γ, f(b)))]. [WRes γ w]
    is the set of the [c ∈ |C(γ, w)|] with [ν(c) ≤ max(ν(γ), ν(w))]. *)
Section WRec.
Context (Cm : STy (sExt Γ Wt)) (m : STm Γ (wMinorPi (C := SC) stPi A B Wt Cm sSupT)).
Local Notation IH := (wIH (C := SC) stPi A B Wt Cm).
Local Notation Minor := (wMinorTy (C := SC) stPi A B Wt Cm sSupT).
Local Notation T1 := (sPi wF' (sPi IH Minor)).

(** The step [m(γ)(a)(φ)(ih)] at a node. *)
Definition wStep (γ : carrier Γ) (a : carrier (A γ)) (φ : carrier (wF' (mkSig γ a)))
    (ih : carrier (IH (mkSig (mkSig γ a) φ))) : carrier (Cm (mkSig γ (supVal (mkSig (mkSig γ a) φ)))) :=
  piApp (Γ := wCtx2') IH Minor
    (piApp (Γ := sExt Γ A) wF' (sPi IH Minor) (piApp (Γ := Γ) A T1 (val m γ) a) φ) ih.

Definition wbound (γ : carrier Γ) (w : WT (carrier (A γ)) (fun a => carrier (fib A B γ a))) : L :=
  maxL (birth Γ γ) (wbirth (A γ) (fib A B γ) w).

Definition WRes (γ : carrier Γ) (w : carrier (Wt γ)) : Type@{t} :=
  Sub (carrier (Cm (mkSig γ w))) (fun c => le (birth (Cm (mkSig γ w)) c) (wbound γ (val w))).

Lemma eSup (γ : carrier Γ) (a : carrier (A γ)) (c : carrier (fib A B γ a) -> WT _ _)
    (g : wgood (A γ) (fib A B γ) (wsup a c)) (φ : carrier (wF' (mkSig γ a)))
    (E : forall b, mkSub (c b) (and1 g b) = piApp B W2 φ b) :
  supVal (mkSig (mkSig γ a) φ) = mkSub (P := wgood (A γ) (fib A B γ)) (wsup a c) g.
Proof.
  apply sub_eq. cbn. apply (ap (wsup a)). apply funext. intros b. exact (ap val (inv (E b))).
Qed.

Section Node.
Context (γ : carrier Γ) (a : carrier (A γ)) (c : carrier (fib A B γ a) -> WT _ _)
  (g : wgood (A γ) (fib A B γ) (wsup a c))
  (r : forall b, WRes γ (mkSub (c b) (and1 g b))).

Definition lw : L := leastB (wbnd (A γ) (fib A B γ) a (fun b => wbirth (A γ) (fib A B γ) (c b))).
Lemma hw : wbnd (A γ) (fib A B γ) a (fun b => wbirth (A γ) (fib A B γ) (c b)) lw.
Proof. exact (proj1 (leastB_spec _ (and2 g))). Qed.

Definition ihFun (φ : carrier (wF' (mkSig γ a))) (E : forall b, mkSub (c b) (and1 g b) = piApp B W2 φ b)
    (b : carrier (B (mkSig γ a))) : carrier (Cm (mkSig γ (piApp B W2 φ b))) :=
  tr (fun w => carrier (Cm (mkSig γ w))) (E b) (val (r b)).

Lemma ih_bound (φ : carrier (wF' (mkSig γ a))) (E : forall b, mkSub (c b) (and1 g b) = piApp B W2 φ b) :
  bndPi (sSub B (sP wF') (mkSig (mkSig γ a) φ)) (fib (sSub B (sP wF')) (sSub Cm (wRho (C := SC) stPi A B Wt))
          (mkSig (mkSig γ a) φ)) (ihFun φ E) (maxL (birth Γ γ) lw).
Proof.
  intros b. unfold ihFun.
  apply (le_by_eq _ _ _ (birth_tr (fun w => Cm (mkSig γ w)) (E b) (val (r b)))).
  pose proof (prf (r b)) as h1. pose proof (hw b) as h2. unfold wbound in h1. cbn in h1, h2. lsolve.
Qed.

(** The value at [sup(a, c)], computed along any [φ] with [φ(b) = c(b)], with the bound
    [max(ν(γ), ν(sup(a, c)))]. *)
Definition wNodeAt (φ : carrier (wF' (mkSig γ a))) (E : forall b, mkSub (c b) (and1 g b) = piApp B W2 φ b)
    (hφ : le (birth (wF' (mkSig γ a)) φ) lw) : WRes γ (mkSub (wsup a c) g).
Proof.
  pose (ih := piMk (Γ := wCtx2') (γ := mkSig (mkSig γ a) φ) (sSub B (sP wF'))
                (sSub Cm (wRho (C := SC) stPi A B Wt)) (ihFun φ E) (maxL (birth Γ γ) lw) (ih_bound φ E)).
  refine (mkSub (tr (fun w => carrier (Cm (mkSig γ w))) (eSup γ a c g φ E) (wStep γ a φ ih)) _).
  apply (le_by_eq _ _ _ (birth_tr (fun w => Cm (mkSig γ w)) (eSup γ a c g φ E) _)).
  pose (s1 := piApp (Γ := Γ) A T1 (val m γ) a).
  pose (s2 := piApp (Γ := sExt Γ A) wF' (sPi IH Minor) s1 φ).
  pose (gb := birth Γ γ). pose (ab := birth (A γ) a). pose (mb := birth (PiS A T1 γ) (val m γ)).
  pose (s1b := birth (PiS wF' (sPi IH Minor) (mkSig γ a)) s1).
  pose (s2b := birth (PiS IH Minor (mkSig (mkSig γ a) φ)) s2).
  pose (bφ := birth (wF' (mkSig γ a)) φ).
  pose (bih := birth (IH (mkSig (mkSig γ a) φ)) ih).
  pose (e3 := birth (Cm (mkSig γ (supVal (mkSig (mkSig γ a) φ)))) (piApp (Γ := wCtx2') IH Minor s2 ih)).
  assert (H3 : le e3 (maxL bih s2b)) by exact (piApp_bound (Γ := wCtx2') IH Minor s2 ih).
  assert (H2 : le s2b (maxL bφ s1b)) by exact (piApp_bound (Γ := sExt Γ A) wF' (sPi IH Minor) s1 φ).
  assert (H1 : le s1b (maxL ab mb)) by exact (piApp_bound (Γ := Γ) A T1 (val m γ) a).
  assert (H0 : le mb gb) by exact (prf m γ).
  assert (Hi : le bih (maxL gb lw)) by exact (piMk_birth (Γ := wCtx2') (γ := mkSig (mkSig γ a) φ)
                 (sSub B (sP wF')) (sSub Cm (wRho (C := SC) stPi A B Wt)) (ihFun φ E) (maxL (birth Γ γ) lw)
                 (ih_bound φ E)).
  assert (Hφ : le bφ lw) by exact hφ.
  change (le e3 (maxL gb (maxL ab lw))).
  clearbody e3 bih bφ s2b s1b mb ab gb. lsolve.
Defined.

(** The children of the node as an element of [Π(b : B a). W]. *)
Definition child (b : carrier (B (mkSig γ a))) : carrier (Wt γ) :=
  mkSub (P := wgood (A γ) (fib A B γ)) (c b) (and1 g b).
Definition φ0 : carrier (wF' (mkSig γ a)) :=
  piMk (Γ := sExt Γ A) (γ := mkSig γ a) B W2 child lw hw.
Definition wNode : WRes γ (mkSub (wsup a c) g) :=
  wNodeAt φ0 (fun b => eq_refl)
    (piMk_birth (Γ := sExt Γ A) (γ := mkSig γ a) B W2 child lw hw).

Lemma wNodeAt_irrel (φ φ' : carrier (wF' (mkSig γ a))) E E' h h' :
  φ = φ' -> wNodeAt φ E h = wNodeAt φ' E' h'.
Proof.
  intros e. destruct e. destruct (proof_irrel E E'). destruct (proof_irrel h h'). reflexivity.
Qed.

End Node.

(** The recursor, by structural recursion on the trees. *)
Fixpoint wrecF (γ : carrier Γ) (w : WT (carrier (A γ)) (fun a => carrier (fib A B γ a))) {struct w} :
    forall g : wgood (A γ) (fib A B γ) w, WRes γ (mkSub w g) :=
  match w as w0 return forall g : wgood (A γ) (fib A B γ) w0, WRes γ (mkSub w0 g) with
  | wsup a c => fun g => wNode γ a c g (fun b => wrecF γ (c b) (and1 g b))
  end.

Definition sWrec : STm (sExt Γ Wt) Cm :=
  mkTm (A := Cm) (fun x => val (wrecF (fst x) (val (snd x)) (prf (snd x))))
    (fun x => prf (wrecF (fst x) (val (snd x)) (prf (snd x)))).

(** The computation rule: [rec(γ, sup(a, f)) = m(γ)(a)(f)(ih)] for every [ih] with
    [ih(b) = rec(γ, f(b))]. *)
Lemma wrecF_node (γ : carrier Γ) (a : carrier (A γ)) (c : carrier (fib A B γ a) -> WT _ _)
    (g : wgood (A γ) (fib A B γ) (wsup a c)) (φ : carrier (wF' (mkSig γ a)))
    (E : forall b, mkSub (P := wgood (A γ) (fib A B γ)) (c b) (and1 g b) = piApp B W2 φ b)
    (hφ : le (birth (wF' (mkSig γ a)) φ) (lw γ a c))
    (ih : carrier (IH (mkSig (mkSig γ a) φ)))
    (hih : forall b, piApp (Γ := wCtx2') (γ := mkSig (mkSig γ a) φ) (sSub B (sP wF'))
                       (sSub Cm (wRho (C := SC) stPi A B Wt)) ih b
                     = tr (fun w => carrier (Cm (mkSig γ w))) (E b) (val (wrecF γ (c b) (and1 g b)))) :
  val (wrecF γ (wsup a c) g)
  = tr (fun w => carrier (Cm (mkSig γ w))) (eSup γ a c g φ E) (wStep γ a φ ih).
Proof.
  cbn [wrecF]. unfold wNode.
  assert (e0 : φ0 γ a c g = φ).
  { apply piExt. intros b. exact (E b). }
  refine (cat (ap (fun r0 : WRes γ (mkSub (wsup a c) g) => val r0) (wNodeAt_irrel γ a c g (fun b => wrecF γ (c b) (and1 g b)) (φ0 γ a c g) φ _ E _ hφ e0)) _).
  unfold wNodeAt. cbv zeta. cbn [val]. refine (tr_cong (fun w => carrier (Cm (mkSig γ w))) _ _ _ _ _). apply (ap (wStep γ a φ)). apply piExt. intros b.
  exact (inv (hih b)).
Qed.

End WRec.
End WTypes.

(** The recursor commutes with substitution, by induction on the trees. *)
Lemma wrecF_sub {Δ Γ : SSet@{t}} (σ : SHom Δ Γ) (A : STy Γ) (B : STy (sExt Γ A))
    (Cm : STy (sExt Γ (sW A B))) (m : STm Γ (wMinorPi (C := SC) stPi A B (sW A B) Cm (sSupT A B)))
    (δ : carrier Δ) (w : WT (carrier (A (val σ δ))) (fun a => carrier (fib A B (val σ δ) a))) g :
  val (wrecF A B Cm m (val σ δ) w g)
  = val (wrecF (sSub A σ) (sSub B (wk (C := SC) σ A)) (sSub Cm (wk (C := SC) σ (sW A B))) (sSubTm m σ) δ w g).
Proof.
  revert g. induction w as [a c IH]. intros g.
  pose (W2 := sSub (sSub (sW A B) (sP A)) (sP B)).
  set (γ := val σ δ).
  pose (φ := φ0 A B γ a c g).
  pose (E := fun b => @eq_refl _ (child A B γ a c g b)).
  pose (hφ := piMk_birth (Γ := sExt Γ A) (γ := mkSig γ a) B W2 (child A B γ a c g) (lw A B γ a c) (hw A B γ a c g)).
  pose (r := fun b => wrecF A B Cm m γ (c b) (and1 g b)).
  pose (ih := piMk (Γ := wCtx2 (C := SC) stPi A B (sW A B)) (γ := mkSig (mkSig γ a) φ)
                (sSub B (sP (wF (C := SC) stPi A B (sW A B)))) (sSub Cm (wRho (C := SC) stPi A B (sW A B)))
                (ihFun A B Cm γ a c g r φ E) (maxL (birth Γ γ) (lw A B γ a c)) (ih_bound A B Cm γ a c g r φ E)).
  refine (cat (wrecF_node A B Cm m γ a c g φ E hφ ih (fun b => eq_refl)) (cat _ (inv
    (wrecF_node (sSub A σ) (sSub B (wk (C := SC) σ A)) (sSub Cm (wk (C := SC) σ (sW A B))) (sSubTm m σ)
        δ a c g φ E hφ ih
        (fun b => ap (tr (fun w => carrier (Cm (mkSig γ w))) (E b)) (IH b (and1 g b))))))).
  refine (tr_cong (fun w => carrier (Cm (mkSig γ w))) _ _ _ _ _). reflexivity.
Qed.

Definition stW : WF (C := SC) (P := stPi).
Proof.
  refine (@Build_WF SC stPi (fun Γ A B => sW A B) (fun Δ Γ σ A B => eq_refl)
            (fun Γ A B => sSupT A B) ?[sup_sub] (fun Γ A B Cm m => sWrec A B Cm m) ?[wrec_sup] ?[wrec_sub]).
  [sup_sub]: { intros Δ Γ σ A B e e'. clearbody e' e. revert e'. kill e. intros e'. kill e'.
    apply tm_eq. intros x. apply sub_eq. reflexivity. }
  [wrec_sup]: { intros Γ A B Cm m e. clearbody e. kill e. apply tm_eq. intros [[γ a] f].
    pose (W2 := sSub (sSub (sW A B) (sP A)) (sP B)).
    pose (cf := fun b => val (piApp B W2 f b)).
    pose (gf := prf (supVal A B (mkSig (mkSig γ a) f))).
    pose (lamIH := val (sLam (sSubTm (sWrec A B Cm m) (wRho (C := SC) stPi A B (sW A B)))) (mkSig (mkSig γ a) f)).
    refine (cat _ (inv (wrecF_node A B Cm m γ a cf gf f (fun b => eq_refl)
                         (piBirth_least B W2 f (lw A B γ a cf) (hw A B γ a cf gf)) lamIH
                         (fun b => eq_refl)))).
    apply inv. refine (tr_irrel_l (fun w => carrier (Cm (mkSig γ w))) _ _ _ _). reflexivity. }
  [wrec_sub]: { intros Δ Γ σ A B Cm m e. clearbody e. kill e. apply tm_eq. intros [δ w].
    exact (wrecF_sub σ A B Cm m δ (val w) (prf w)). }
Defined.

(** ** The logic of staged sets *)

Lemma DecT_ne (p : TV) (x : DecT p) : p <> None.
Proof. destruct p; [discriminate | destruct x]. Qed.

(** [∀(A, φ)] holds at [γ] from stage [k] on iff each [φ(γ, a)] holds from [max(ν a, k)] on. *)
Lemma sAll_le {Γ : SSet@{t}} (A : STy Γ) (φ : STm (sExt Γ A) (sProp _)) (γ : carrier Γ) (k : L) :
  leT (val (sAll A φ) γ) (Some k) <-> forall a, leT (val φ (mkSig γ a)) (Some (maxL (birth (A γ) a) k)).
Proof.
  cbn. split.
  - intros h a. apply nuS_le in h. destruct h as [f hf].
    pose proof (SPi_bnd _ _ f a) as hb. cbn in hb.
    rewrite (DecT_val _ (val f a)). cbn.
    eapply le_trans; [exact hb | apply max_lub; [apply le_max_l | apply le_max_r'; exact hf]].
  - intros h. apply nuS_le.
    assert (hne : forall a, (val φ (mkSig γ a) : TV) <> None).
    { intros a e. specialize (h a). revert h. rw e. intros h. exact h. }
    assert (hb : bndPi (A γ) (fun a => decode@{t} (val φ (mkSig γ a))) (fun a => decIntro _ (hne a)) k).
    { intros a. pose proof (h a) as ha. rewrite (DecT_val _ (decIntro _ (hne a))) in ha. exact ha. }
    exists (mkPi (A γ) (fun a => decode@{t} (val φ (mkSig γ a))) (fun a => decIntro _ (hne a)) k hb).
    exact (SPi_least (A γ) (fun a => decode@{t} (val φ (mkSig γ a)))
             (mkPi (A γ) (fun a => decode@{t} (val φ (mkSig γ a))) (fun a => decIntro _ (hne a)) k hb) k hb).
Qed.

(** [φ ⇒ ψ] holds at [γ] from [k] on iff [ψ] holds at [γ] from [max(l, k)] on, where [l]
    is the stage from which [φ] holds at [γ]. *)
Lemma impT_le {Γ : SSet@{t}} (φ ψ : STm Γ (sProp Γ)) (γ : carrier Γ) (k : L) :
  leT (val (impT stProp φ ψ) γ) (Some k) <-> (forall l, (val φ γ : TV) = Some l -> leT (val ψ γ) (Some (maxL l k))).
Proof.
  unfold impT. split.
  - intros h l e. pose proof (proj1 (sAll_le _ _ γ k) h) as h'.
    assert (hne : (val φ γ : TV) <> None) by (rw e; discriminate).
    pose proof (h' (decIntro _ hne)) as h2. cbn in h2.
    rewrite (decB_intro _ hne l e) in h2. exact h2.
  - intros h. apply (proj2 (sAll_le _ _ γ k)). intros x. cbn.
    exact (h (decB _ x) (DecT_val _ x)).
Qed.

(** [El φ] has a term iff [φ(γ) ≤ ν(γ)] for every [γ]. *)
Lemma prfElim {Γ : SSet@{t}} {φ : STm Γ (sProp Γ)} (h : STm Γ (sPrf φ)) (γ : carrier Γ) :
  leT (val φ γ) (Some (birth Γ γ)).
Proof. pose proof (prf h γ) as hb. cbn in hb. rewrite (DecT_val _ (val h γ)). exact hb. Qed.

Lemma prf_ne {Γ : SSet@{t}} (φ : STm Γ (sProp Γ)) (h : forall γ, leT (val φ γ) (Some (birth Γ γ))) γ :
  (val φ γ : TV) <> None.
Proof. intros e. pose proof (h γ) as hγ. revert hγ. rw e. intros hγ. exact hγ. Qed.

Definition prfIntro {Γ : SSet@{t}} (φ : STm Γ (sProp Γ)) (h : forall γ, leT (val φ γ) (Some (birth Γ γ))) :
    STm Γ (sPrf φ).
Proof.
  refine (mkTm (A := sPrf φ) (fun γ => decIntro (val φ γ) (prf_ne φ h γ)) _).
  intros γ. cbn. pose proof (h γ) as hγ. rewrite (DecT_val _ (decIntro (val φ γ) (prf_ne φ h γ))) in hγ.
  exact hγ.
Defined.

(** ** Quotients *)

(** [(A/R)(γ) = A(γ)/R_γ], [mk(γ, a) = [a]], [lift f (γ, c) = f(γ, rep c)], and induction
    through [[rep c] = c]. *)
Definition sQuot {Γ : SSet@{t}} (A : STy Γ) (R : STm (sExt (sExt Γ A) (sSub A (sP A))) (sProp _)) : STy Γ :=
  QFam@{t t} A (val R).

Section Quot.
Context {Γ : SSet@{t}} (A : STy Γ) (R : STm (sExt (sExt Γ A) (sSub A (sP A))) (sProp _)).

Definition relAt (γ : carrier Γ) (a b : carrier (A γ)) : Prop := (val R (mkSig (mkSig γ a) b) : TV) <> None.

Definition sQmk : STm (sExt Γ A) (sSub (sQuot A R) (sP A)) :=
  mkTm (A := sSub (sQuot A R) (sP A)) (fun x => cls (A (fst x)) (relAt (fst x)) (snd x))
    (fun x => le_trans _ _ _ (cls_birth _ _ (snd x)) (le_max_r _ _)).

(** A function respecting [R] is constant on the classes of the generated relation. *)
Lemma resp_eqc (B : STy Γ) (f : STm (sExt Γ A) (sSub B (sP A)))
    (h : STm Γ (sPrf (respIn stId (C := SC) A R B f))) (γ : carrier Γ) (a b : carrier (A γ)) :
  eqc (A γ) (relAt γ) a b -> val f (mkSig γ a) = val f (mkSig γ b).
Proof.
  intros e. induction e as [a b r | a | a b _ IH | a b c _ IH1 _ IH2].
  - pose proof (prfElim h γ) as h0. unfold respIn in h0.
    pose proof (proj1 (sAll_le _ _ γ _) h0 a) as h1.
    pose proof (proj1 (sAll_le (Γ := sExt Γ A) _ _ (mkSig γ a) _) h1 b) as h2.
    destruct (val R (mkSig (mkSig γ a) b)) as [l|] eqn:El; [|destruct (r El)].
    pose proof (proj1 (impT_le _ _ _ _) h2 l El) as h3. cbn in h3.
    revert h3. killtr.
    destruct (decb (val f (mkSig γ a) = val f (mkSig γ b))) eqn:Eq; [intros _ | intros []].
    exact (proj1 (decb_spec _) Eq).
  - reflexivity.
  - exact (inv IH).
  - exact (cat IH1 IH2).
Qed.

Definition sQlift (B : STy Γ) (f : STm (sExt Γ A) (sSub B (sP A))) (h : STm Γ (sPrf (respIn stId (C := SC) A R B f))) :
    STm (sExt Γ (sQuot A R)) (sSub B (sP (sQuot A R))).
Proof.
  refine (mkTm (A := sSub B (sP (sQuot A R))) (fun x => val f (mkSig (fst x) (rep _ _ (snd x)))) _).
  intros x. pose proof (prf f (mkSig (fst x) (rep _ _ (snd x)))) as hf. cbn in hf |- *.
  rewrite (rep_birth _ _ (snd x)) in hf. exact hf.
Defined.

Definition sQind (χ : STm (sExt Γ (sQuot A R)) (sProp _))
    (k : STm (sExt Γ A) (sPrf (subP (C := SC) stProp (pair (c := SC) (pp (c := SC) A) sQmk) χ))) :
    STm (sExt Γ (sQuot A R)) (sPrf χ).
Proof.
  apply prfIntro. intros [γ c]. pose proof (prfElim k (mkSig γ (rep _ _ c))) as hk.
  apply (leT_by_eq _ _ _ (ap (fun z => val χ (mkSig γ z)) (inv (cls_rep (A γ) (relAt γ) c)))).
  eapply leT_trans; [exact hk|].
  change (le (maxL (birth Γ γ) (birth (A γ) (rep (A γ) (relAt γ) c)))
             (maxL (birth Γ γ) (birth (QS (A γ) (relAt γ)) c))).
  rewrite (rep_birth (A γ) (relAt γ) c). apply le_refl.
Defined.

Definition sQsound : STm Γ (sPrf (respIn stId (C := SC) A R (sQuot A R) sQmk)).
Proof.
  apply prfIntro. intros γ. unfold respIn. apply (proj2 (sAll_le _ _ γ _)). intros a.
  apply (proj2 (sAll_le (Γ := sExt Γ A) _ _ (mkSig γ a) _)). intros b.
  apply (proj2 (impT_le _ _ _ _)). intros l El. killtr.
  match goal with |- context [decb ?P] => destruct (decb P) eqn:E end; [exact (bot_le _) |].
  exfalso. assert (H : relAt γ a b) by (intros e; pose proof (cat (inv El) e) as e'; discriminate e').
  match type of E with decb ?P = false =>
    assert (hp : P) by exact (cls_eq (A γ) (relAt γ) a b (eqc_step _ _ a b H));
    rewrite (decb_true P hp) in E; discriminate
  end.
Defined.

End Quot.

(** The substituted relation, with its transport along a convertible equation removed. *)
Lemma subR_red {Δ Γ : SSet@{t}} (σ : SHom Δ Γ) (A : STy Γ) (R : STm (sExt (sExt Γ A) (sSub A (sP A))) (sProp _)) :
  subR (C := SC) stProp σ A R
  = subP (C := SC) stProp (wk (C := SC) (wk (C := SC) σ A) (sub (c := SC) A (pp (c := SC) A))) R.
Proof.
  unfold subR.
  exact (tr_irrel (fun Z : STy (sExt Δ (sSub A σ)) => STm (sExt (sExt Δ (sSub A σ)) Z) (sProp _))
           (e_pwk (C := SC) σ A A) _).
Qed.

Lemma sQuot_sub {Δ Γ : SSet@{t}} (σ : SHom Δ Γ) (A : STy Γ) (R : STm (sExt (sExt Γ A) (sSub A (sP A))) (sProp _)) :
  sSub (sQuot A R) σ = sQuot (sSub A σ) (subR (C := SC) stProp σ A R).
Proof. rw (subR_red σ A R). reflexivity. Qed.

Definition stQuot : QuotF (C := SC) (Id := stId).
Proof.
  refine (@Build_QuotF SC stProp stId (fun Γ A R => sQuot A R) (fun Δ Γ σ A R => sQuot_sub σ A R)
            (fun Γ A R => sQmk A R) _ (fun Γ A R B f h => sQlift A R B f h) _ _
            (fun Γ A R χ k => sQind A R χ k) (fun Γ A R => sQsound A R)).
  - intros Δ Γ σ A R e. clearbody e. revert e. rw (subR_red σ A R). intros e. kill e. apply tm_eq. intros x. reflexivity.
  - intros Γ A R B f h e. clearbody e. kill e. apply tm_eq. intros x.
    exact (inv (resp_eqc A R B f h (fst x) (snd x) _ (rep_cls _ _ (snd x)))).
  - intros Δ Γ σ A R B f h h' e. clearbody e. revert h' e. generalize (sQuot_sub σ A R).
    rw (subR_red σ A R). intros e0. kill e0. intros h' e. kill e. revert h'. killtr. intros h'. apply tm_eq. intros x. reflexivity.
Defined.

(** ** Universes *)

Section Univ1.
(** [u]: the level of the codes, the small staged sets of the paper. The universe [sU] is
    [SSet@{u}] as a staged set in the universe of discourse [t], hence [u < t]. *)
Universe u.
Constraint u < t.

(** [Type = Δ Stg_u], the constant family of the staged sets of level [u], all born at [0],
    and [El X = X]. *)
Definition sU (Γ : SSet@{t}) : STy Γ := fun _ => uSat@{u t}.
Definition sEl {Γ : SSet@{t}} (X : STm Γ (sU Γ)) : STy Γ := fun γ => val X γ.
Definition mkCode {Γ : SSet@{t}} (f : carrier Γ -> SSet@{u}) : STm Γ (sU Γ) :=
  mkTm (A := sU Γ) f (fun γ => bot_le _).

Definition stUnivB : UnivBase (C := SC) :=
  @Build_UnivBase SC (fun Γ => sU Γ) (fun Δ Γ σ => eq_refl) (fun Γ X => sEl X) (fun Δ Γ σ X => eq_refl).

(** The codes of the type formers are the constructions themselves, at the level [u]. *)
Definition stCodes : Codes (C := SC) (Sg := stSigma) (F := stFin) (W := stW) (Q := stQuot) (V := stUnivB).
Proof.
  refine (@Build_Codes SC stPi stSigma stFin stW stProp stId stQuot stUnivB
    (fun Γ a b => mkCode (PiS@{u t} (fun γ => val a γ) (fun x => val b x))) _ _
    (fun Γ a b => mkCode (SigS@{u} (fun γ => val a γ) (fun x => val b x))) _ _
    (fun Γ => mkCode (fun _ => zeroS@{u})) _ _
    (fun Γ => mkCode (fun _ => oneS@{u})) _ _
    (fun Γ => mkCode (fun _ => twoS@{u})) _ _
    (fun Γ a b => mkCode (WFam@{u t} (fun γ => val a γ) (fun x => val b x))) _ _
    (fun Γ a R => mkCode (QFam@{u t} (fun γ => val a γ) (val R))) _ _
    (fun Γ φ => mkCode (fun γ => decode@{u} (val φ γ))) _ _
    (fun Γ => mkCode (fun _ => tvS@{u})) _ _).
  all: intros.
  all: try (apply tm_eq; intros; reflexivity).
  all: try reflexivity.
  all: try (apply sty_ext; intros; reflexivity).
  all: unfold subRx; cbn;
    match goal with |- context [subR _ ?σ ?A ?R] => rw (subR_red σ A R) end;
    apply tm_eq; intros; reflexivity.
Defined.

End Univ1.

Lemma leT_some p k : leT p (Some k) -> exists l, p = Some l /\ le l k.
Proof. destruct p as [l|]; cbn; [intros h; exists l; split; [reflexivity | exact h] | intros []]. Qed.

(** ** Global choice *)

Section Choice.
(** [i]: the level of the codes, as [u] in [Univ1]; global choice picks an element of a
    code of level [i]. *)
Universe i.
Constraint Set < i.
Constraint i < t.

(** The truncation of [X] holds from stage [l] on only if [X] has an element born by [l]. *)
Lemma trunc_le {Γ : SSet@{t}} (X : STm Γ (sU@{i} Γ)) (γ : carrier Γ) (l : L) :
  leT (val (truncT (C := SC) stUnivB@{i} stProp X) γ) (Some l) ->
  exists y : carrier (val X γ), le (birth (val X γ) y) l.
Proof.
  intros h. unfold truncT in h.
  pose proof (proj1 (sAll_le _ _ γ l) h (nuS (val X γ))) as h1.
  assert (hS : leT (val (sAll (sEl (subU (C := SC) stUnivB@{i} (sP (sProp Γ)) X))
                              (subP (C := SC) stProp (sP _) (varP (C := SC) stProp Γ)))
                        (mkSig γ (nuS (val X γ)))) (Some bot)).
  { apply (proj2 (sAll_le _ _ _ _)). intros y. cbn. rewrite max_bot_r. apply nuS_lb. }
  pose proof (leT_bot _ hS) as eS.
  pose proof (proj1 (impT_le _ _ _ _) h1 bot eS) as h2.
  change (leT (nuS (val X γ)) (Some (maxL bot (maxL bot l)))) in h2.
  rewrite max_bot_l, max_bot_l in h2. apply nuS_le in h2. exact h2.
Qed.

Section Pt.
Context (x : carrier (sExt (sExt sEmpty (sU@{i} sEmpty))
                       (sPrf (truncT (C := SC) stUnivB@{i} stProp (varU (C := SC) stUnivB@{i} sEmpty))))).

Lemma choice_inh : exists y : carrier (snd (fst x)), le (birth (snd (fst x)) y) (decB _ (snd x)).
Proof.
  apply (trunc_le (varU (C := SC) stUnivB@{i} sEmpty) (fst x)).
  apply (leT_by_eq _ _ _ (DecT_val _ (snd x))). apply leT_refl.
Qed.

(** [choice(X, h) = c(X)], an element of [X] of least birthday, chosen in the metatheory.
    It is born by [‖X‖ ≤ ν(X, h)]. *)
Definition chooseAt : carrier (snd (fst x)) :=
  minElt (snd (fst x)) (match choice_inh with ex_intro _ y _ => ex_intro _ y I end).

Lemma chooseAt_bound :
  le (birth (snd (fst x)) chooseAt)
     (birth (sExt (sExt sEmpty (sU@{i} sEmpty))
                  (sPrf (truncT (C := SC) stUnivB@{i} stProp (varU (C := SC) stUnivB@{i} sEmpty)))) x).
Proof.
  destruct choice_inh as [y hy] eqn:E.
  pose proof (minElt_min (snd (fst x)) (match choice_inh with ex_intro _ y _ => ex_intro _ y I end) y) as hm.
  unfold chooseAt. cbn. eapply le_trans; [exact hm|]. eapply le_trans; [exact hy|]. apply le_max_r.
Qed.
End Pt.

Definition sChoice :
  STm sEmpty
    (sPi (sU@{i} sEmpty)
       (sPi (sPrf (truncT (C := SC) stUnivB@{i} stProp (varU (C := SC) stUnivB@{i} sEmpty)))
          (sEl (subU (C := SC) stUnivB@{i} (sP _) (varU (C := SC) stUnivB@{i} sEmpty))))) :=
  sLam (sLam (mkTm (A := sEl (subU (C := SC) stUnivB@{i} (sP _) (varU (C := SC) stUnivB@{i} sEmpty)))
                 chooseAt chooseAt_bound)).

End Choice.

(** ** Values of the encodings *)

Lemma imp_val {Γ : SSet@{t}} (φ ψ : STm Γ (sProp Γ)) (γ : carrier Γ) (k : L) :
  (forall l, (val φ γ : TV) = Some l -> leT (val ψ γ) (Some (maxL l k))) ->
  exists l, (val (impT stProp φ ψ) γ : TV) = Some l /\ le l k.
Proof. intros h. apply leT_some. exact (proj2 (impT_le _ _ _ _) h). Qed.

Lemma none_imp {Γ : SSet@{t}} (φ ψ : STm Γ (sProp Γ)) (γ : carrier Γ) :
  (val φ γ : TV) = None -> (val (impT stProp φ ψ) γ : TV) = Some bot.
Proof.
  intros e. apply leT_bot. apply (proj2 (impT_le _ _ _ _)). intros l e'.
  pose proof (cat (inv e) e') as e''. discriminate e''.
Qed.

(** [⊥ = ∞], [¬φ = ∞] for [φ ≠ ∞], [¬∞ = 0], and [φ ∧ ψ ≤ max(φ, ψ)]. *)
Lemma bot_none {Γ : SSet@{t}} (γ : carrier Γ) : (val (botT (C := SC) stProp Γ) γ : TV) = None.
Proof.
  apply leT_none. intros k h. unfold botT in h.
  exact (proj1 (sAll_le _ _ γ k) h None).
Qed.

Lemma neg_none {Γ : SSet@{t}} (φ : STm Γ (sProp Γ)) (γ : carrier Γ) :
  (val φ γ : TV) <> None -> (val (negT stProp φ) γ : TV) = None.
Proof.
  intros hne. apply leT_none. intros k h. unfold negT in h.
  destruct (val φ γ : TV) as [l|] eqn:e; [|exact (hne eq_refl)].
  pose proof (proj1 (impT_le _ _ _ _) h l e) as h'.
  revert h'. rw (bot_none γ). intros [].
Qed.

Lemma neg_some {Γ : SSet@{t}} (φ : STm Γ (sProp Γ)) (γ : carrier Γ) :
  (val φ γ : TV) = None -> (val (negT stProp φ) γ : TV) = Some bot.
Proof. apply none_imp. Qed.

Lemma and_le {Γ : SSet@{t}} (φ ψ : STm Γ (sProp Γ)) (γ : carrier Γ) a b :
  (val φ γ : TV) = Some a -> (val ψ γ : TV) = Some b -> leT (val (andT stProp φ ψ) γ) (Some (maxL a b)).
Proof.
  intros ea eb. unfold andT. apply (proj2 (sAll_le _ _ γ _)). intros r.
  apply (proj2 (impT_le _ _ _ _)). intros l1 e1.
  pose proof (proj1 (impT_le _ _ _ _) (leT_by_eq _ _ _ e1 (leT_refl _)) a ea) as h1.
  pose proof (proj1 (impT_le _ _ _ _) h1 b eb) as h2.
  eapply leT_trans; [exact h2|]. change (le (maxL b (maxL a l1)) (maxL l1 (maxL bot (maxL a b)))). lsolve.
Qed.

(** [φ ∨ ψ] with [ψ] false holds by stage [k] only if [φ] does. *)
Lemma or_le_inv {Γ : SSet@{t}} (φ ψ : STm Γ (sProp Γ)) (γ : carrier Γ) (k m : L) :
  (val ψ γ : TV) = None -> (val φ γ : TV) = Some m -> leT (val (orT stProp φ ψ) γ) (Some k) -> le m k.
Proof.
  intros eψ eφ h. unfold orT in h.
  pose proof (proj1 (sAll_le _ _ γ k) h (Some m)) as h1.
  assert (e1 : (val (impT (C := SC) stProp (subP (C := SC) stProp (sP (sProp Γ)) φ) (varP (C := SC) stProp Γ))
                  (mkSig γ (Some m)) : TV) = Some bot).
  { apply leT_bot. apply (proj2 (impT_le _ _ _ _)). intros l e.
    pose proof (cat (inv eφ) e) as e'. injection e' as e'. rewrite <- e'. cbn. rewrite max_bot_r. apply le_refl. }
  pose proof (proj1 (impT_le _ _ _ _) h1 bot e1) as h2.
  pose proof (none_imp (subP (C := SC) stProp (sP (sProp Γ)) ψ) (varP (C := SC) stProp Γ) (mkSig γ (Some m)) eψ) as e2.
  pose proof (proj1 (impT_le _ _ _ _) h2 bot e2) as h3.
  change (le m (maxL bot (maxL bot (maxL (birth (sProp Γ γ) (Some m)) k)))) in h3.
  cbn in h3. rewrite max_bot_l, max_bot_l, max_bot_l in h3. exact h3.
Qed.

(** ** The model *)

Section TheModel.
(** [i]: the level of the codes of the universe [sU]. The model [stagedModel] is
    polymorphic in [i] below the universe of discourse [t]. The quotient codes ([QFam])
    need [Set < i]. *)
Universe i.
Constraint Set < i.
Constraint i < t.

(** ** The failure of propositional extensionality and of excluded middle *)

(** For [v ≠ 0], propositional extensionality holds at no stage: at [(P, Q) = (0, v)],
    [P ⇔ Q] holds from [v] on, and [Id(P, Q) = ∞]. *)
Lemma propext_not_le (v : L) (hv : v <> bot) {Γ : SSet@{t}} (γ : carrier Γ) (k : L) :
  ~ leT (val (propextT (C := SC) stId Γ) γ) (Some k).
Proof.
  intros h. unfold propextT in h.
  pose proof (proj1 (sAll_le _ _ γ k) h (Some bot)) as h1.
  pose proof (proj1 (sAll_le (Γ := sExt Γ (sProp Γ)) _ _ (mkSig γ (Some bot)) _) h1 (Some v)) as h2.
  set (x := mkSig (mkSig γ (Some bot)) (Some v) : carrier (sExt (sExt Γ (sProp Γ)) (sProp _))) in h2.
  set (P := subP (C := SC) stProp (sP (sProp (sExt Γ (sProp Γ)))) (varP (C := SC) stProp Γ)) in h2.
  set (Q := varP (C := SC) stProp (sExt Γ (sProp Γ))) in h2.
  assert (eP : (val P x : TV) = Some bot) by reflexivity.
  assert (eQ : (val Q x : TV) = Some v) by reflexivity.
  destruct (imp_val P Q x v (fun l e => match cat (inv eP) e in _ = o return
                                         (match o with Some l0 => leT (val Q x) (Some (maxL l0 v)) | None => True end)
                                       with eq_refl => tr (fun z => leT z (Some (maxL bot v))) (inv eQ)
                                                           (le_max_r bot v) end))
    as [lx [ex hlx]].
  destruct (imp_val Q P x bot (fun l e => tr (fun z => leT z (Some (maxL l bot))) (inv eP) (bot_le _)))
    as [ly [ey hly]].
  pose proof (and_le (impT (C := SC) stProp P Q) (impT (C := SC) stProp Q P) x lx ly ex ey) as hand.
  destruct (leT_some _ _ hand) as [l' [el' _]].
  pose proof (proj1 (impT_le _ _ _ _) h2 l' el') as h3.
  revert h3. cbn.
  match goal with |- context [decb ?R] =>
    rewrite (decb_false R (fun e => hv (inv (ap (fun o : TV => match o with Some z => z | None => bot end) e))))
  end.
  intros [].
Qed.

(** Without a greatest element, excluded middle holds at no stage: for [k ∈ L] and [m] not
    below [k], [P ∨ ¬P] at [P = m] holds from [m] on only. *)
Lemma em_not_le (nomax : forall l, exists m, ~ le m l) {Γ : SSet@{t}} (γ : carrier Γ) (k : L) :
  ~ leT (val (EMT (C := SC) stProp Γ) γ) (Some k).
Proof.
  intros h. unfold EMT in h. destruct (nomax (maxL bot k)) as [m hm].
  pose proof (proj1 (sAll_le _ _ γ k) h (Some m)) as h1.
  apply hm. refine (or_le_inv (varP (C := SC) stProp Γ) (negT (C := SC) stProp (varP (C := SC) stProp Γ))
                     (mkSig γ (Some m)) _ m _ eq_refl h1).
  apply neg_none. discriminate.
Qed.

(** A closed proposition whose value is [∞] has a refutation. *)
Lemma refute (φ : STm sEmpty (sProp sEmpty)) (hφ : forall k, ~ leT (val φ Datatypes.tt) (Some k)) :
  STm sEmpty (sPrf (negT (C := SC) stProp φ)).
Proof.
  apply prfIntro. intros []. apply leT_by_eq with (q := Some bot); [|exact (bot_le _)].
  apply neg_some. apply leT_none. exact hφ.
Qed.

(** The refutation of propositional extensionality, for a stage [v ≠ 0]. *)
Definition sNotPropext (v : L) (hv : v <> bot) :
  Tm (empty SC) (prfT stProp (negT stProp (propextT stId (empty SC)))) :=
  refute _ (fun k => propext_not_le v hv (Γ := sEmpty) Datatypes.tt k).

(** The refutation of excluded middle, for stages without a greatest element. *)
Definition sNotEM (nomax : forall l, exists m, ~ le m l) :
  Tm (empty SC) (prfT stProp (negT stProp (EMT stProp (empty SC)))) :=
  refute _ (fun k => em_not_le nomax (Γ := sEmpty) Datatypes.tt k).

(** Consistency: [⊥ = ∞] decodes to the empty staged set, and a closed term of [El ⊥]
    gives an element of [Empty_set]. *)
Definition sConsistent : Tm (empty SC) (prfT stProp (botT stProp (empty SC))) -> False :=
  fun h => DecT_ne _ (val h Datatypes.tt) (bot_none (Γ := sEmpty) Datatypes.tt).

(** Without a greatest element, some stage is not below [0]. *)
Definition stageNZ (nomax : forall l, exists m, ~ le m l) : L :=
  val (choice (fun m => ~ le m bot) (nomax bot)).

Lemma stageNZ_ne (nomax : forall l, exists m, ~ le m l) : stageNZ nomax <> bot.
Proof.
  intros e. exact (prf (choice (fun m => ~ le m bot) (nomax bot)) (tr (fun z => le z bot) (inv e) (le_refl bot))).
Qed.

(** The model, for stages without a greatest element. *)
Definition stagedModel (nomax : forall l, exists m, ~ le m l) : TModel (C := SC) :=
  @Build_TModel SC stPi stSigma stFin stW stProp stId stQuot
    stUnivB@{i} stCodes@{i}
    sChoice@{i} (sNotEM nomax) (sNotPropext (stageNZ nomax) (stageNZ_ne nomax)) sConsistent.

End TheModel.

End CwFS.

End Staged.

(** * Part IV. The stages [nat] *)

From Stdlib Require Import PeanoNat Wf_nat.

Lemma nat_lt_wf : well_founded (fun a b : nat => a <= b /\ a <> b).
Proof.
  intros n. induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf).
  constructor. intros m [h1 h2]. apply IH. apply Nat.le_neq. split; assumption.
Qed.

(** [nat] has no greatest element. *)
Lemma nat_nomax : forall l : nat, exists m, ~ Peano.le m l.
Proof. intros l. exists (S l). exact (Nat.nle_succ_diag_l l). Qed.

(** The model of Theorem 1.1, for the stages [nat]. *)
Definition natModel@{t c1 c2 i | Set < t, t < c1, t < c2, Set < i, i < t} :=
  stagedModel@{t c1 c2 i} nat Peano.le 0 Nat.le_refl Nat.le_trans Nat.le_antisymm Nat.le_ge_cases
    Nat.le_0_l nat_lt_wf nat_nomax.

(** * Part V. The universes classify the types *)

(** In the sense of Hofmann and Streicher: for every context [Γ], decoding [sEl] and
    [mkCode] are mutually inverse between the codes, the terms of [sU Γ], and the
    families [carrier Γ -> SSet@{u}], the types of size [u]; and both commute with
    substitution. *)

Section Classification.
Context (L : Set) (le : L -> L -> Prop) (bot : L)
  (le_trans : forall a b c, le a b -> le b c -> le a c)
  (bot_le : forall a, le bot a).
(** [t], [c1], [c2] as in [CwFS], and [u] the level of the codes as [i] in [TheModel]. *)
Universes t c1 c2 u.
Constraint Set < t.
Constraint t < c1.
Constraint t < c2.
Constraint Set < u.
Constraint u < t.

Local Notation Code Γ := (STm@{t c1 c2} L le Γ (sU@{t c1 c2 u} L bot Γ)).
Local Notation code f := (mkCode@{t c1 c2 u} L le bot bot_le f).

(** Decoding a constructed code gives back the family. *)
Lemma sEl_mkCode {Γ : SSet@{t} L} (f : carrier _ Γ -> SSet@{u} L) :
  sEl@{t c1 c2 u} L le bot (code f) = f.
Proof. reflexivity. Qed.

(** Every code is constructed from its decoding [fun γ => val X γ], which is [sEl X]
    at the level [u]. *)
Lemma mkCode_sEl {Γ : SSet@{t} L} (X : Code Γ) : code (fun γ => val X γ) = X.
Proof. apply tm_eq. intros γ. reflexivity. Qed.

(** Constructing codes commutes with substitution. *)
Lemma mkCode_sub {Δ Γ : SSet@{t} L} (σ : SHom@{t c1 c2} L le Δ Γ) (f : carrier _ Γ -> SSet@{u} L) :
  sSubTm L le le_trans (code f) σ = code (fun δ => f (val σ δ)).
Proof. apply tm_eq. intros δ. reflexivity. Qed.

(** The three together: decoding is a bijection between codes and types of size [u],
    natural in the context. *)
Lemma univ_classifies :
  (forall (Γ : SSet@{t} L) (f : carrier _ Γ -> SSet@{u} L), sEl@{t c1 c2 u} L le bot (code f) = f) /\
  (forall (Γ : SSet@{t} L) (X : Code Γ), code (fun γ => val X γ) = X) /\
  (forall (Δ Γ : SSet@{t} L) (σ : SHom@{t c1 c2} L le Δ Γ) (f : carrier _ Γ -> SSet@{u} L),
     sSubTm L le le_trans (code f) σ = code (fun δ => f (val σ δ))).
Proof.
  split; [|split].
  - intros Γ f. exact (sEl_mkCode f).
  - intros Γ X. exact (mkCode_sEl X).
  - intros Δ Γ σ f. exact (mkCode_sub σ f).
Qed.

End Classification.
