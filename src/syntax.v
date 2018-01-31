(** * The syntax of terms, types and substitutions

The syntax of terms, types and substitutions should be flexible. For instance, we may or
may not tag lambda abstractions with their domains and codomains. We may or may not use
explicit subtitutions, etc. In order to deal with the possibilities, we define a type
class [Syntax] which can then be instantiated in several ways.

*)

(** Universe levels for a type theory with a hierarchy of universes. This is a bit of a
   hack, and in the future we migth want to use instead a more abstract structure for
   universe levels.
*)
Inductive level : Type :=
| uni : nat -> level
| prop : level
.

(** An auxiliary type class used solely or the purpose of introducing a nice notation
    for substitution extension. *)
Class CONS A B := _sbcons : A -> B -> B.
Notation "u ⋅ σ" := (_sbcons u σ) (at level 20, right associativity).

(** An auxiliary type class used solely or the purpose of introducing a nice notation
    for substitution action. *)
Class SUBST substitution tt :=
  _subst : tt -> substitution -> tt.
Notation "t [ σ ]" := (_subst t σ) (at level 4).

(** An auxiliary type class used solely or the purpose of introducing a nice notation for
    context extension. *)
Class EXTEND A B := _extend : A -> B -> A.
Notation "Γ , A" := (_extend Γ A) (at level 19, left associativity).

Section SyntaxDefinition.

(** The syntax of type theory as a class.

    Some call it "pre-syntax" or "raw syntax" because it does not capture any
    well-formedness requirements. Those are present in the [TypeTheory] class defined
    below.

    We may interpret this class definition as giving constructors for inductive types,
    which results in a fully annotated syntax with explicit substitutions, as given in
    [annotated_syntax]. But there are many other possibilities.

    For example, suppose you want lambda abstractions that are *not* annotated with their
    domains and codomains. Then you would define [myLam : term -> term] and instantiate
    [lam] below as [lam := (fun _ _ t => myLam t)]. That is, a particular instance may
    drop some arguments of term or type constructors. In the extreme, we could define
    terms to have type [unit] and have them all be equal to [()]. This would be quite silly
    but it would demonstrate the point that *syntax need not be inductively defined*.
    (If you want to prove inversion theorems then you will need a suitably inductively
     defined syntax.)

   Also, suppose you want a type theory which omits some of the type constructors below.
   For example, suppose you do not want any universes. Then in your instance of syntax
   you should define values [Junk : type] and [junk : type] and set [Uni := fun lvl => Junk]
   and interpret the [uniXYZ] constructors as [junk]. Your typing rule should never mention
   [Junk] or [junk], and when you configure universes, make sure to state something like

   [[
     Local Instance haveUniverses : config.Universes := {| config.flagUniverses := config.No |}.
   ]]

   This way the library will never get stuck on [Junk] or [junk].

   You may also wish to treat substitutions as meta-level operations. We are working on providing
   support for this, but the present [Syntax] class already allows you to instantiate substitutions
   as meta-level operations. In particular, [Subst] and [subst] need not be type and term constructors.
   Instead, they can be meta-level operations that act on terms.
 *)
Class Syntax := {
  (* Syntactic categories *)
  context : Type;
  type : Type;
  term : Type;
  substitution : Type;

  (* Contexts *)
  ctxempty : context;
  ctxextend :> EXTEND context type;

  (* Types *)
  Prod : type -> type -> type; (* product type *)
  Id : type -> term -> term -> type; (* identity type *)
  Empty : type;  (* empty type *)
  Unit : type; (* unit type *)
  Bool : type; (* boolean type *)
  BinaryProd : type -> type -> type; (* simple product *)
  Uni : level -> type; (* universe with a level *)
  El : level -> term -> type; (* the decoding of a universe element *)
  (* TODO: Cond : type -> term -> type -> type, elimination of booleans into types,
     and possibly similarly for Empty, Unit, ... *)
  (* TODO: dependent sums *)

  (* Terms *)
  var : nat -> term; (* de Bruijn index *)
  lam : type -> type -> term -> term; (* lambda abstraction *)
  app : term -> type -> type -> term -> term; (* application *)
  refl : type -> term -> term; (* reflexivity *)
  j : type -> term -> type -> term -> term -> term -> term; (* identity elimination *)
  exfalso : type -> term -> term; (* falsity elimination *)
  unit : term; (* the element of the unit type *)
  true : term; (* boolean truth *)
  false : term; (* boolean falsehood *)
  cond : type -> term -> term -> term -> term; (* dependent boolean elimnation *)
  pair : type -> type -> term -> term -> term; (* simple pair *)
  proj1 : type -> type -> term -> term; (* simple first projection *)
  proj2 : type -> type -> term -> term; (* simple second projection *)
  uniProd : level -> level -> term -> term -> term; (* the name of a product type *)
  uniId : level -> term -> term -> term -> term; (* the name of an identity type *)
  uniEmpty : level -> term; (* the name of the empty type *)
  uniUnit : level -> term; (* the name of the unit type *)
  uniBool : nat -> term; (* the name of the boolean type *)
  uniBinaryProd : level -> level -> term -> term -> term; (* the name of the simple product type *)
  uniUni : level -> term; (* the name of a universe *)

  (* Substitutions *)

  Subst :> SUBST substitution type; (* the action of a substitution on a type *)
  subst :> SUBST substitution term;  (* the action of a substitution on a term *)

  sbid : substitution; (* the identity substitution *)
  sbcons :> CONS term substitution; (* a substitution extended with action on index 0 *)
  sbweak : substitution; (* weakening substitution *)

  (* Equations governing substitutions. *)
  sbidterm :
    forall {t : term}, t[sbid] = t;
  sbidtype :
    forall {T : type}, T[sbid] = T;
  sbconszero :
    forall {σ u}, (var 0)[u ⋅ σ] = u;
  sbconssucc :
    forall {σ u n}, (var (S n))[u ⋅ σ] = (var n)[σ];
  sbweakvar :
    forall {n}, (var n)[sbweak] = var (S n);

  (* Equations governing substitution actions. *)
  SubstProd :
    forall {σ A B},
      (Prod A B)[σ] = Prod A[σ] B[(var 0) ⋅ σ];
  SubstId :
    forall {σ A u v},
      (Id A u v)[σ] = Id A[σ] u[σ] v[σ];
  SubstEmpty :
    forall {σ}, Empty[σ] = Empty;
  SubstUnit :
    forall {σ}, Unit[σ] = Unit;
  SubstBool :
    forall {σ}, Bool[σ] = Bool;
  SubstBinaryProd :
    forall {σ A B},
      (BinaryProd A B)[σ] = BinaryProd A[σ] B[σ];
  SubstUni :
    forall {σ l},
      (Uni l)[σ] = Uni l;
  SubstEl :
    forall {σ l a},
      (El l a)[σ] = El l a[σ];

  substLam :
    forall {σ A B t},
      (lam A B t)[σ] = lam A[σ] B[var 0 ⋅ σ] t[var 0 ⋅ σ];
  substApp :
    forall {σ A B u v},
      (app u A B v)[σ] = app u[σ] A[σ] B[var 0 ⋅ σ] v[σ];
  substRefl :
    forall {σ A u},
      (refl A u)[σ] = refl A[σ] u[σ];
  substJ :
    forall {σ A u C w v p},
      (j A u C w v p)[σ] =
      j A[σ] u[σ] C[var 0 ⋅ var 0 ⋅ σ] w[σ] v[σ] p[σ];
  substExfalso :
    forall {σ A u},
      (exfalso A u)[σ] = exfalso A[σ] u[σ];
  substUnit :
    forall {σ}, unit[σ] = unit;
  substTrue :
    forall {σ}, true[σ] = true;
  substFalse :
    forall {σ}, false[σ] = false;
  substCond :
    forall {σ C u v w},
      (cond C u v w)[σ] = cond C[var 0 ⋅ σ] u[σ] v[σ] w[σ];
  substPair :
    forall {σ A B u v},
      (pair A B u v)[σ] = pair A[σ] B[σ] u[σ] v[σ];
  substProjOne :
    forall {σ A B p},
      (proj1 A B p)[σ] = proj1 A[σ] B[σ] p[σ];
  substProjTwo :
    forall {σ A B p},
      (proj2 A B p)[σ] = proj2 A[σ] B[σ] p[σ];
  substUniProd :
    forall {σ l1 l2 a b},
      (uniProd l1 l2 a b)[σ] =
      uniProd l1 l2 a[σ] b[var 0 ⋅ σ];
  substUniId :
    forall {σ l a u v},
      (uniId l a u v)[σ] = uniId l a[σ] u[σ] v[σ];
  substUniEmpty :
    forall {σ l}, (uniEmpty l)[σ] = uniEmpty l;
  substUniUnit :
    forall {σ l}, (uniUnit l)[σ] = uniUnit l;
  substUniBool :
    forall {σ l}, (uniBool l)[σ] = uniBool l;
  substUniBinaryProd :
    forall {σ l1 l2 a b},
      (uniBinaryProd l1 l2 a b)[σ] = uniBinaryProd l1 l2 a[σ] b[σ];
  substUniUni :
    forall {σ l}, (uniUni l)[σ] = uniUni l;

  (* A shorthand for simple function type *)
  Arrow := fun (A B :  type) => Prod A B[sbweak]
}.

(** A type theory over a given syntax [S] is given by 6 judgment forms.
    We use underscores here so that the names without underscores can be
    used in the instantiations of this type class. 

    The judgment form "is a substitution" is defined separately below.
*)
Class TypeTheory (S : Syntax) := {
  _isctx : context -> Type; (* is a context *)
  _istype : context -> type -> Type; (* is a type in context *)
  _isterm : context -> term -> type -> Type; (* is a term of type in context *)
  _eqctx : context -> context -> Type; (* equal contexts *)
  _eqtype : context -> type -> type -> Type; (* equal types in context *)
  _eqterm : context -> term -> term -> type -> Type (* equal terms at type in context *)
}.

(** We define a separate type class for the judgment form "is a substitition",
    because such a judgment form may or may not actually be present in a type theory,
    depending on whether substitutions are explicit or meta-level.
 *)
Class SubstitutionTyping (S : Syntax) (T : TypeTheory S) := {
  (* Typing of substitutions *)
  issubst : substitution -> context -> context -> Type;

  SubstSbid : forall {Γ}, _isctx Γ -> issubst sbid Γ Γ;
  SubstWeak : forall {Γ A}, _isctx Γ -> _istype Γ A -> issubst sbweak (Γ,A) Γ;
  SubstCtxConv :
    forall {σ Γ Δ Δ'},
      _eqctx Δ' Δ ->
      issubst σ Γ Δ ->
      issubst σ Γ Δ';
  SubstCons :
    forall {σ u Γ Δ A},
      issubst σ Γ Δ ->
      _istype Δ A ->
      _isterm Γ u A[σ] ->
      issubst (u ⋅ σ) Γ (Δ, A);

  TySubst :
    forall {σ Γ Δ A},
      issubst σ Γ Δ ->
      _istype Δ A ->
      _istype Γ A[σ];
  TermSubst :
    forall {σ Γ Δ A u},
      issubst σ Γ Δ ->
      _istype Δ A ->
      _isterm Δ u A ->
      _isterm Γ u[σ] A[σ]
}.

End SyntaxDefinition.
