Require config.
Require Import config_tactics.

Require Import syntax. (* The syntax of ett/ptt. *)
Require Import tt.

Require ptt ett ett_sanity.
Require pxtt eitt.
Require ctt.
Require Import eval.
Require Import hml.

Section Translation.

(* For a term in CTT to be well-typed we need to evaluate it to ITT and
   check there. *)
Definition Cisctx G := eitt.isctx (eval_ctx G).
Definition Cissubst sbs G D :=
  eitt.issubst (eval_substitution sbs) (eval_ctx G) (eval_ctx D).
Definition Cistype G A :=
  eitt.istype (eval_ctx G) (eval_type A).
Definition Cisterm G u A :=
  eitt.isterm (eval_ctx G) (eval_term u) (eval_type A).

(* We do something similar for coercions. *)
(* Definition CisContextCoercion c G D := *)
(*   ctt.isContextCoercion c (eval_ctx G) (eval_ctx D). *)

(* This lemma might need to be relocated in itt or so. *)
(* Lemma inversion_sbcomp : *)
(*   forall {sbs sbt G D}, *)
(*     eitt.issubst (sbcomp sbs sbt) G D -> *)
(*     { E : context & *)
(*       eitt.issubst sbs E D * *)
(*       eitt.issubst sbt G E *)
(*     }%type. *)
(* Proof. *)
(*   intros sbs sbt G D h. *)
(*   assert ( *)
(*       forall sbr, *)
(*         sbr = sbcomp sbs sbt -> eitt.issubst sbr G D -> *)
(*         { E : context & *)
(*           eitt.issubst sbs E D * *)
(*           eitt.issubst sbt G E *)
(*         }%type *)
(*   ). *)
(*   { intros sbr eq. induction 1 ; try discriminate. *)
(*     - inversion eq. subst. *)
(*       exists D. split ; assumption. *)
(*     - subst. destruct (IHX X eq_refl) as [E [h1 h2]]. *)
(*       exists E. split. *)
(*       + ceapply SubstCtxConv. *)
(*         * exact h1. *)
(*         * capply CtxRefl. *)
(*           (* We need sanity to conclude. *) *)
(*           admit. *)
(*         * assumption. *)
(*       + ceapply SubstCtxConv. *)
(*         * exact h2. *)
(*         * assumption. *)
(*         * capply CtxRefl. *)
(*           (* We need sanity to conclude. *) *)
(*           admit. *)
(*   } *)
(*   capply (X (sbcomp sbs sbt) eq_refl h). *)
(* Admitted. *)

(* Lemma inversion_substitution : *)
(*   forall {c1' c2' sbs' G D}, *)
(*     Cissubst (ctt.sbcoerce (c1', c2') sbs') G D -> *)
(*     { Gi : context & *)
(*       { Di : context & *)
(*         eitt.issubst (ctt.ctxco_inv c1') (eval_ctx G) Gi * *)
(*         eitt.issubst (eval_substitution' sbs') Gi Di   * *)
(*         eitt.issubst (ctt.ctxco_map c2') Di (eval_ctx D) *)
(*       } *)
(*     }%type. *)
(* Proof. *)
(*   intros c1' c2' sbs' G D h. *)
(*   unfold Cissubst in h. simpl in h. *)
(*   destruct (inversion_sbcomp h) as [E1 [h1 h2]]. *)
(*   destruct (inversion_sbcomp h2) as [E2 [h3 h4]]. *)
(*   exists E2, E1. repeat split ; assumption. *)
(* Defined. *)

(* Some lemma to apply a coercion to a substitution rather than on a
   substitution' *)
(* Definition coerce_substitution (sbs : ctt.substitution) (sc : ctt.substCoerce) *)
(*   : ctt.substitution *)
(*   := match sbs,sc with *)
(*     | ctt.sbcoerce (c1',c2') sbs', (c1,c2) => *)
(*       ctt.sbcoerce (ctt.contextComp c1 c1', ctt.contextComp c2 c2') sbs' *)
(*     end. *)

(* Lemma coerce_substitution_typing *)
(*   { sbs c1 c2 G D G' D' } *)
(*   (hsbs : Cissubst sbs G D) *)
(*   (hc1 : CisContextCoercion c1 G G') (hc2 : CisContextCoercion c2 D D') *)
(*   : Cissubst (coerce_substitution sbs (c1,c2)) G' D'. *)
(* Proof. *)
(*   unfold coerce_substitution. destruct sbs as [[c1' c2'] sbs']. *)
(*   unfold Cissubst. simpl. *)
(*   destruct (inversion_substitution hsbs) as (Gi & Di & [[h1 h2] h3]). *)
(*   ceapply SubstComp. *)
(*   - ceapply SubstComp. *)
(*     + ceapply SubstComp. *)
(*       * destruct hc1 as [[_ h] _]. exact h. *)
(*       * eassumption. *)
(*     + eassumption. *)
(*   - ceapply SubstComp. *)
(*     + eassumption. *)
(*     + destruct hc2 as [[h _] _]. exact h. *)
(* Defined. *)

(* Same thing but on a type. *)
(* Lemma inversion_Subst : *)
(*   forall { G A sbs }, *)
(*     eitt.istype G (Subst A sbs) -> *)
(*     { D : context & *)
(*       eitt.issubst sbs G D * *)
(*       eitt.istype D A *)
(*     }%type. *)
(* Proof. *)
(*   intros G A sbs h. *)
(*   assert ( *)
(*     forall B, *)
(*       B = Subst A sbs -> *)
(*       eitt.istype G B -> *)
(*       { D : context & *)
(*         eitt.issubst sbs G D * *)
(*         eitt.istype D A *)
(*       }%type *)
(*   ). *)
(*   { intros B eq. induction 1 ; try discriminate. *)
(*     - subst. destruct (IHX X eq_refl) as [E [h1 h2]]. *)
(*       exists E. split. *)
(*       + ceapply SubstCtxConv. *)
(*         * eassumption. *)
(*         * assumption. *)
(*         * (* Once again we need sanity for ITT *) *)
(*           capply CtxRefl. *)
(*           admit. *)
(*       + assumption. *)
(*     - inversion eq. subst. *)
(*       exists D. split ; assumption. *)
(*   } *)
(*   apply (X (Subst A sbs) eq_refl h). *)
(* Admitted. *)

(* Lemma inversion_type : *)
(*   forall {G c' A'}, *)
(*     Cistype G (ctt.Coerce c' A') -> *)
(*     { D : context & *)
(*       eitt.issubst (ctt.ctxco_inv c') (eval_ctx G) D * *)
(*       eitt.istype D (eval_type' A') *)
(*     }%type. *)
(* Proof. *)
(*   intros G c' A' h. *)
(*   unfold Cistype in h. simpl in h. *)
(*   destruct (inversion_Subst h) as [E [h1 h2]]. *)
(*   exists E. split ; assumption. *)
(* Defined. *)

(* Definition coerce_type (A : ctt.type) (tc : ctt.typeCoerce) : ctt.type := *)
(*   match A with *)
(*   | ctt.Coerce c A' => *)
(*     ctt.Coerce (ctt.contextComp tc c) A' *)
(*   end. *)

(* Lemma coerce_type_typing *)
(*   { G D A c } *)
(*   (hA : Cistype G A) *)
(*   (hc : CisContextCoercion c G D) *)
(*   : Cistype D (coerce_type A c). *)
(* Proof. *)
(*   unfold coerce_type. destruct A as [c' A']. *)
(*   unfold Cistype. simpl. *)
(*   destruct (inversion_type hA) as [E [h1 h2]]. *)
(*   ceapply TySubst. *)
(*   - ceapply SubstComp. *)
(*     + destruct hc as [[_ h] _]. exact h. *)
(*     + eassumption. *)
(*   - assumption. *)
(* Defined. *)



(* Lemma hml_substitution_change : *)
(*   forall sc1 sc2 sbs sbs', *)
(*     hml_substitution sbs (ctt.sbcoerce sc1 sbs') -> *)
(*     hml_substitution sbs (ctt.sbcoerce sc2 sbs'). *)
(* Proof. *)
(*   intros sc1 sc2 sbs. *)
(*   induction 2. *)
(*   case_eq h ; intros. *)
(*   - apply hml_sbzero. *)
Definition hml_substitution_change
    sc1 sc2 sbs sbs'
    (h : hml_substitution sbs (ctt.sbcoerce sc1 sbs'))
  : hml_substitution sbs (ctt.sbcoerce sc2 sbs')
  := match h with
    | hml_sbzero h1 h2  => hml_sbzero h1 h2
    | hml_sbweak h1     => hml_sbweak h1
    | hml_sbshift h1 h2 => hml_sbshift h1 h2
    | hml_sbid          => hml_sbid
    | hml_sbcomp h1 h2  => hml_sbcomp h1 h2
    end.

Definition hml_type_change
    c1 c2 A A'
    (h : hml_type A (ctt.Coerce c1 A'))
  : hml_type A (ctt.Coerce c2 A')
  := match h with
    | hml_Prod h1 h2  => hml_Prod h1 h2
    | hml_Id h1 h2 h3 => hml_Id h1 h2 h3
    | hml_Subst h1 h2 => hml_Subst h1 h2
    | hml_Empty       => hml_Empty
    | hml_Unit        => hml_Unit
    | hml_Bool        => hml_Bool
    end.


Structure istrans_ctx (G : context) (G' : ctt.context) :=
  {
    isctx_derive : Cisctx G' ;
    isctx_hom : hml_context G G'
  }.

Structure istrans_subst
          (sbs : substitution)
          (G' D' : ctt.context) (sbs' : ctt.substitution)
  :=
  {
    issubst_derive : Cissubst sbs' G' D' ;
    issubst_hom : hml_substitution sbs sbs'
  }.

Structure istrans_type (A : type) (G' : ctt.context) (A' : ctt.type) :=
  {
    istype_derive : Cistype G' A' ;
    istype_hom : hml_type A A'
  }.

Structure istrans_term (u : term) (G' : ctt.context) (u' : ctt.term) (A' : ctt.type) :=
  {
    isterm_derive : Cisterm G' u' A' ;
    isterm_hom : hml_term u u'
  }.

(* Notion of equivalences. *)
Parameter equiv_type : ctt.context -> ctt.type -> ctt.type -> Type.
Parameter equiv_term : ctt.context -> ctt.term -> ctt.term -> ctt.type -> Type.
(* Should we use coercions as the corresponding definition for equiv_type? *)

(* Seems like this notation screws up the other one. *)
(* Notation "{ x : A & y : B & P }" := *)
(*   (sigT (A:=A) (fun x => sigT (A:=B) (fun y => P))) *)
(*   : type_scope. *)

Ltac todo := exact todo.

Fixpoint trans_term
  {G G' u A A'}
  (H : pxtt.isterm G u A)
  (HG : istrans_ctx G G')
  (HA : istrans_type A G' A')
  : { u' : ctt.term
    & istrans_term u G' u' A' }.
Proof.
  (**** trans_term ****)
  - { destruct H.

      (* TermTyConv *)
      - todo.

      (* TermCtxConv *)
      - todo.

      (* TermSubst *)
      - todo.

      (* TermVarZero *)
      - todo.

      (* TermVarSucc *)
      - todo.

      (* TermAbs *)
      - todo.

      (* TermApp *)
      - todo.

      (* TermRefl *)
      - todo.

      (* TermJ *)
      - todo.

      (* TermExfalso *)
      - todo.

      (* TermUnit *)
      - todo.

      (* TermTrue *)
      - todo.

      (* TermFalse *)
      - todo.

      (* TermCond *)
      - todo.
    }
Defined.

(* Fixpoint trans_ctx {G} (H : pxtt.isctx G) {struct H} : *)
(*   { G' : ctt.context & istrans_ctx G G' } *)

(* with trans_subst_left {G G' D sbs} (H : pxtt.issubst sbs G D) *)
(*                   (Ht : istrans_ctx G G') {struct H} : *)
(*        { D' : ctt.context & *)
(*          istrans_ctx D D' * *)
(*          { sbt : ctt.substitution & istrans_subst sbs G' D' sbt } }%type *)

(* (* this one might not be needed? *) *)
(* (* with trans_subst_right {G D D' sbs} (H : E.issubst sbs G D) *) *)
(* (*                   (Ht : istrans_ctx D D') {struct H} : *) *)
(* (*        { G' : ctt.context & { sbt : ctt.substitution & ctt.issubst sbt G' D' } } *) *)

(* with trans_type {G G' A} (H : pxtt.istype G A) (Ht : istrans_ctx G G') {struct H} : *)
(*        { A' : ctt.type & *)
(*               istrans_type A G' A' * *)
(*               (* this component might not be needed? *) *)
(*               forall A'' (Hty : istrans_type A G' A''), equiv_type G' A' A'' *)
(*        }%type *)

(* with trans_term *)
(*        {G u A G' A'} *)
(*        (H : pxtt.isterm G u A) *)
(*        (HG : istrans_ctx G G') *)
(*        (HA : istrans_type A G' A') {struct H} *)
(*      : { u' : ctt.term & *)
(*          istrans_term u G' u' A' * *)
(*          (* this component might not be needed? *) *)
(*          forall u'' (Hu : istrans_term u G' u'' A'), equiv_term G' u' u'' A' *)
(*        }%type *)

(* with trans_eqctx_left *)
(*        {G G' D} *)
(*        (H : pxtt.eqctx G D) *)
(*        (HG : istrans_ctx G G') {struct H} *)
(*      : { D' : ctt.context & *)
(*          istrans_ctx D D' * *)
(*          { c : ctt.contextCoercion & *)
(*            CisContextCoercion c G' D' *)
(*          } *)
(*        }%type *)

(* with trans_eqctx_right *)
(*        {G D D'} *)
(*        (H : pxtt.eqctx G D) *)
(*        (HD : istrans_ctx D D') {struct H} *)
(*      : { G' : ctt.context & *)
(*          istrans_ctx G G' * *)
(*          { c : ctt.contextCoercion & *)
(*            CisContextCoercion c G' D' *)
(*          } *)
(*        }%type. *)

(* Proof. *)
(*   (****** trans_ctx ******) *)
(*   - { destruct H ; doConfig. *)

(*       (* CtxEmpty *) *)
(*       - exists ctt.ctxempty. *)
(*         split. *)
(*         + constructor. *)
(*         + constructor. *)

(*       (* CtxExtend *) *)
(*       - destruct (trans_ctx _ i) as [G' HGisG']. *)
(*         destruct (trans_type G G' A i0 HGisG') as (A' & HAisA' & _). *)
(*         exists (ctt.ctxextend G' A'). *)
(*         split. *)
(*         + constructor. *)
(*           * now destruct HGisG'. *)
(*           * now destruct HAisA'. *)
(*         + constructor. *)
(*           * now destruct HGisG'. *)
(*           * now destruct HAisA'. *)
(*     } *)

(*   (****** trans_subst_left ******) *)
(*   - { destruct H ; doConfig. *)

(*       (* SubstZero *) *)
(*       - destruct (trans_type G G' A i0 Ht) as (A' & HAisA' & _). *)
(*         destruct (trans_term G u A G' A' i Ht HAisA') as (u' & Huisu' & _). *)
(*         exists (ctt.ctxextend G' A'). *)
(*         { split. *)
(*           - constructor. *)
(*             + unfold Cisctx. simpl. *)
(*               capply CtxExtend. *)
(*               now inversion HAisA'. *)
(*             + constructor. *)
(*               * now inversion Ht. *)
(*               * now inversion HAisA'. *)
(*           - exists (ctt.sbcoerce *)
(*                  ctt.idSb *)
(*                  (ctt.sbzero A' u')). *)
(*             split. *)
(*             + unfold Cissubst. simpl. *)
(*               { ceapply SubstComp. *)
(*                 - ceapply SubstComp. *)
(*                   + ceapply SubstId. now inversion Ht. *)
(*                   + ceapply SubstZero. now inversion Huisu'. *)
(*                 - capply SubstId. ceapply CtxExtend. *)
(*                   now inversion HAisA'. *)
(*               } *)
(*             + constructor. *)
(*               * now destruct HAisA'. *)
(*               * now destruct Huisu'. *)
(*         } *)

(*       (* SubstWeak *) *)
(*       - destruct Ht as [HG' hom]. *)
(*         inversion hom. subst. *)
(*         exists G'0. *)
(*         { split. *)
(*           - constructor. *)
(*             + todo. (* The proof needs to be changed *) *)
(*             + assumption. *)
(*           - exists (ctt.sbcoerce *)
(*                  ctt.idSb *)
(*                  (ctt.sbweak A')). *)
(*             split. *)
(*             + (* To type it we need to recover that A' is a type. *) *)
(*               inversion HG'. subst. *)
(*               (* We need to now how to evaluate coercions. *) *)
(*               unfold Cissubst. simpl. *)
(*               { ceapply SubstComp. *)
(*                 - ceapply SubstComp. *)
(*                   + ceapply SubstId. assumption. *)
(*                   + ceapply SubstWeak. assumption. *)
(*                 - ceapply SubstId. todo. *)
(*               } *)
(*             + econstructor ; eassumption. *)
(*         } *)

(*       (* SubstShift *) *)
(*       - destruct Ht as [HG' hom]. *)
(*         inversion hom. subst. *)
(*         rename G'0 into G'. rename X into homG. rename X0 into homAs. *)
(*         inversion homAs. subst. *)
(*         rename A'0 into A'. rename X into homA. rename X0 into homs. *)
(*         (* What we probably want is something similar to the other *)
(*            translation functions where we can take in some homologous *)
(*            object to build a path between them? *) *)

(*         (* We probably want to use sbs' that we already have. *) *)
(*         (* assert (HtG : istrans_ctx G G'0). *) *)
(*         (* { split. *) *)
(*         (*   - now inversion HG'. *) *)
(*         (*   - assumption. *) *)
(*         (* } *) *)
(*         (* destruct (trans_subst_left G G'0 D sbs H HtG) as [D' [sbt h]]. *) *)
(*         (* exists (ctt.ctxextend D' A'0). exists () *) *)
(*         inversion HG'. subst. *)
(*         (* Now that's great, but the inversion doesn't give us that A'σ' is well *)
(*            typed and thus that σ' is as well, yielding a Δ' for us to play with. *)
(*          *) *)
(*         todo. *)

(*       (* SubstId *) *)
(*       - exists G'. *)
(*         split ; try assumption. *)
(*         exists (ctt.sbcoerce ctt.idSb ctt.sbid). *)
(*         split. *)
(*         + unfold Cissubst. simpl. *)
(*           { ceapply SubstComp. *)
(*             - ceapply SubstComp. *)
(*               + ceapply SubstId. now inversion Ht. *)
(*               + ceapply SubstId. now inversion Ht. *)
(*             - ceapply SubstId. now inversion Ht. *)
(*           } *)
(*         + constructor. *)

(*       (* SubstComp *) *)
(*       - destruct (trans_subst_left G G' D sbs H Ht) as (D' & HD' & sbs' & Hsbs). *)
(*         destruct (trans_subst_left D D' E sbt H0 HD') as (E' & HE' & sbt' & ?). *)
(*         exists E'. *)
(*         split. *)
(*         + assumption. *)
(*         + exists (ctt.sbcoerce *)
(*                ctt.idSb *)
(*                (ctt.sbcomp sbt' sbs')). *)
(*           { split. *)
(*             - unfold Cissubst. simpl. *)
(*               ceapply SubstComp. *)
(*               + { ceapply SubstComp. *)
(*                   - ceapply SubstId. now inversion Ht. *)
(*                   - ceapply SubstComp. *)
(*                     + inversion Hsbs. eassumption. *)
(*                     + inversion i2. eassumption. *)
(*                 } *)
(*               + ceapply SubstId. now inversion HE'. *)
(*             - constructor. *)
(*               + now inversion i2. *)
(*               + now inversion Hsbs. *)
(*           } *)

(*       (* SubstCtxConv *) *)
(*       - rename G' into G2'. *)
(*         destruct (trans_eqctx_right G1 G2 G2' e Ht) as (G1' & HG1 & c1 & Hc1). *)
(*         destruct (trans_subst_left G1 G1' D1 sbs H HG1) *)
(*           as (D1' & HD1 & sbs' & Hsbs). *)
(*         destruct (trans_eqctx_left D1 D1' D2 e0 HD1) as (D2' & HD2 & c2 & Hc2). *)
(*         exists D2'. *)
(*         split. *)
(*         + assumption. *)
(*         + exists (coerce_substitution sbs' (c1,c2)). *)
(*           split. *)
(*           * { eapply coerce_substitution_typing. *)
(*               - destruct Hsbs. eassumption. *)
(*               - eassumption. *)
(*               - eassumption. *)
(*             } *)
(*           * destruct Hsbs as [_ hml]. *)
(*             unfold coerce_substitution. destruct sbs'. destruct s. *)
(*             eapply hml_substitution_change. eassumption. *)
(*     } *)

(*   (****** trans_subst_right ******) *)
(*   (* - { destruct H. *) *)

(*   (*     (* SubstZero *) *) *)
(*   (*     - admit. *) *)

(*   (*     (* SubstWeak *) *) *)
(*   (*     - admit. *) *)

(*   (*     (* SubstShift *) *) *)
(*   (*     - admit. *) *)

(*   (*     (* SubstId *) *) *)
(*   (*     - admit. *) *)

(*   (*     (* SubstComp *) *) *)
(*   (*     - admit. *) *)

(*   (*     (* SubstCtxConv *) *) *)
(*   (*     - admit. *) *)
(*   (*   } *) *)

(*   (****** trans_type ******) *)
(*   - { destruct H ; doConfig. *)

(*       (* TyCtxConv *) *)
(*       - rename G' into D'. *)
(*         destruct (trans_eqctx_right G D D' e Ht) as (G' & HGisG' & c & Hc). *)
(*         destruct (trans_type G G' A H HGisG') as [A' [HA fA]]. *)
(*         exists (coerce_type A' c). split. *)
(*         + { split. *)
(*             - eapply coerce_type_typing. *)
(*               + destruct HA. eassumption. *)
(*               + assumption. *)
(*             - destruct HA. *)
(*               unfold coerce_type. destruct A'. *)
(*               eapply hml_type_change. eassumption. *)
(*           } *)
(*         + todo. (* Same as always, we need to be sure what an equivalence is. *) *)

(*       (* TySubst *) *)
(*       - destruct (trans_subst_left G G' D sbs i Ht) as [D' [HD [sbt Hsbt]]]. *)
(*         destruct (trans_type D D' A H HD) as [A' [HAisA' fA]]. *)
(*         exists (ctt.Coerce ctt.idTy (ctt.Subst A' sbt)). *)
(*         split. *)
(*         + split. *)
(*           * { unfold Cistype. simpl. *)
(*               ceapply TySubst. *)
(*               - ceapply SubstId. now destruct Ht. *)
(*               - ceapply TySubst. *)
(*                 + destruct Hsbt. eassumption. *)
(*                 + destruct HAisA'. assumption. *)
(*             } *)
(*           * { apply hml_Subst. *)
(*               - now destruct HAisA'. *)
(*               - now destruct Hsbt. *)
(*             } *)
(*         + todo. (* Same again. *) *)

(*       (* TyProd *) *)
(*       - destruct (trans_type G G' A H0 Ht) as [A' [HAisA' fA]]. *)
(*         pose (Gx := syntax.ctxextend G A). *)
(*         pose (Gx' := ctt.ctxextend G' A'). *)
(*         assert (Hex : istrans_ctx Gx Gx'). *)
(*         { split. *)
(*           - unfold Cisctx. simpl. *)
(*             apply eitt.CtxExtend. *)
(*             + destruct Ht. assumption. *)
(*             + destruct HAisA'. assumption. *)
(*           - apply hml_ctxextend. *)
(*             + destruct Ht. assumption. *)
(*             + destruct HAisA'. assumption. *)
(*         } *)
(*         destruct (trans_type Gx Gx' B H Hex) as [B' [HBisB' fB]]. *)
(*         exists (ctt.Coerce (ctt.idTy (eval_ctx G')) (ctt.Prod A' B')). *)
(*         split. *)
(*         + { split. *)
(*             - unfold Cistype. simpl. *)
(*               eapply eitt.TySubst. *)
(*               + eapply eitt.SubstId. now destruct Ht. *)
(*               + eapply eitt.TyProd. *)
(*                 * now destruct HAisA'. *)
(*                 * now destruct HBisB'. *)
(*             - apply hml_Prod. *)
(*               + now destruct HAisA'. *)
(*               + now destruct HBisB'. *)
(*           } *)
(*         + todo. (* Same here. *) *)

(*       (* TyId *) *)
(*       - destruct (trans_type G G' A H Ht) as [A' [HA fA]]. *)
(*         destruct (trans_term G u A G' A' i0 Ht HA) as [u' [Hu fu]]. *)
(*         destruct (trans_term G v A G' A' i1 Ht HA) as [v' [Hv fv]]. *)
(*         exists (ctt.Coerce (ctt.idTy (eval_ctx G')) (ctt.Id A' u' v')). *)
(*         split. *)
(*         + split. *)
(*           * { unfold Cistype. simpl. *)
(*               eapply eitt.TySubst. *)
(*               - eapply eitt.SubstId. now destruct Ht. *)
(*               - eapply eitt.TyId. *)
(*                 + now destruct HA. *)
(*                 + now destruct Hu. *)
(*                 + now destruct Hv. *)
(*             } *)
(*           * destruct HA ; destruct Hu ; destruct Hv ; now constructor. *)
(*         + intros A'' HA''. *)
(*           (* Without a notion of equivalence, no hope to complete this goal. *) *)
(*           todo. *)

(*       (* TyEmpty *) *)
(*       - exists (ctt.Coerce (ctt.idTy (eval_ctx G')) ctt.Empty). split. *)
(*         + split. *)
(*           * { unfold Cistype. simpl. *)
(*               eapply eitt.TySubst. *)
(*               - eapply eitt.SubstId. now destruct Ht. *)
(*               - eapply eitt.TyEmpty. now destruct Ht. *)
(*             } *)
(*           * constructor. *)
(*         + intros A'' HA''. (* destruct HA'' as [H hom]. *) *)
(*           (* inversion hom. subst. *) *)
(*           todo. *)

(*       (* TyUnit *) *)
(*       - exists (ctt.Coerce (ctt.idTy (eval_ctx G')) ctt.Unit). split. *)
(*         + split. *)
(*           * { unfold Cistype. simpl. *)
(*               eapply eitt.TySubst. *)
(*               - eapply eitt.SubstId. now destruct Ht. *)
(*               - eapply eitt.TyUnit. now destruct Ht. *)
(*             } *)
(*           * constructor. *)
(*         + todo. *)

(*       (* TyBool *) *)
(*       - exists (ctt.Coerce (ctt.idTy (eval_ctx G')) ctt.Bool). split. *)
(*         + split. *)
(*           * { unfold Cistype. simpl. *)
(*               eapply eitt.TySubst. *)
(*               - eapply eitt.SubstId. now destruct Ht. *)
(*               - eapply eitt.TyBool. now destruct Ht. *)
(*             } *)
(*           * constructor. *)
(*         + todo. *)

(*     } *)

(*   (****** trans_term ******) *)
(*   - todo. *)

(*   (****** trans_eqctx_left ******) *)
(*   - { destruct H ; doConfig. *)

(*       (* CtxRefl *) *)
(*       - exists G'. split. *)
(*         + assumption. *)
(*         + exists (ctt.contextId (eval_ctx G')). *)
(*           unfold CisContextCoercion. apply ctt.isCoercionContextId. *)
(*           now destruct HG. *)

(*       (* CtxSym *) *)
(*       - rename G' into D'. rename HG into HD. *)
(*         destruct (trans_eqctx_right G D D' H HD) as [G' [HG [c Hc]]]. *)
(*         exists G'. split. *)
(*         + assumption. *)
(*         + exists (ctt.contextInv c). *)
(*           eapply ctt.isCoercionContextInv. assumption. *)

(*       (* CtxTrans *) *)
(*       - destruct (trans_eqctx_left G G' D H HG) as [D' [HD [c1 Hc1]]]. *)
(*         destruct (trans_eqctx_left D D' E H0 HD) as [E' [HE [c2 Hc2]]]. *)
(*         exists E'. split. *)
(*         + assumption. *)
(*         + exists (ctt.contextComp c2 c1). *)
(*           eapply ctt.isCoercionContextComp ; eassumption. *)

(*       (* EqCtxEmpty *) *)
(*       - exists G'. split. *)
(*         + assumption. *)
(*         + exists (ctt.contextId (eval_ctx G')). *)
(*           unfold CisContextCoercion. apply ctt.isCoercionContextId. *)
(*           now destruct HG. *)

(*       (* EqCtxExtend *) *)
(*       - destruct HG as [HGA Hhom]. inversion Hhom. subst. *)
(*         rename X into homG. rename X0 into homA. rename G'0 into G'. *)
(*         inversion HGA. subst. *)
(*         assert (HGisG' : istrans_ctx G G'). *)
(*         { split ; assumption. } *)
(*         destruct (trans_eqctx_left G G' D H HGisG') as [D' [HD [cc Hcc]]]. *)
(*         (* We now need to be able to translate type equalities. *) *)
(*         todo. *)

(*     } *)

(*   (****** trans_eqctx_right ******) *)
(*   - { destruct H ; doConfig. *)

(*       (* CtxRefl *) *)
(*       - rename D' into G'. rename HD into HG. *)
(*         exists G'. split. *)
(*         + assumption. *)
(*         + exists (ctt.contextId (eval_ctx G')). *)
(*           unfold CisContextCoercion. apply ctt.isCoercionContextId. *)
(*           now destruct HG. *)

(*       (* CtxSym *) *)
(*       - rename D' into G'. rename HD into HG. *)
(*         destruct (trans_eqctx_left G G' D H HG) as [D' [HD [c Hc]]]. *)
(*         exists D'. split. *)
(*         + assumption. *)
(*         + exists (ctt.contextInv c). *)
(*           eapply ctt.isCoercionContextInv. assumption. *)

(*       (* CtxTrans *) *)
(*       - rename HD into HE. rename D' into E'. *)
(*         destruct (trans_eqctx_right D E E' H0 HE) as [D' [HD [c2 Hc2]]]. *)
(*         destruct (trans_eqctx_right G D D' H HD) as [G' [HG [c1 Hc1]]]. *)
(*         exists G'. split. *)
(*         + assumption. *)
(*         + exists (ctt.contextComp c2 c1). *)
(*           eapply ctt.isCoercionContextComp ; eassumption. *)

(*       (* EqCtxEmpty *) *)
(*       - rename D' into G'. rename HD into HG. *)
(*         exists G'. split. *)
(*         + assumption. *)
(*         + exists (ctt.contextId (eval_ctx G')). *)
(*           unfold CisContextCoercion. apply ctt.isCoercionContextId. *)
(*           now destruct HG. *)

(*       (* EqCtxExtend *) *)
(*       - destruct HD as [HDB Hhom]. inversion Hhom. subst. *)
(*         rename X into homD. rename X0 into homB. *)
(*         rename G' into D'. rename A' into B'. *)
(*         inversion HDB. subst. *)
(*         assert (HDisD' : istrans_ctx D D'). *)
(*         { split ; assumption. } *)
(*         destruct (trans_eqctx_right G D D' H HDisD') as [G' [HG [cc Hcc]]]. *)
(*         (* We now need to be able to translate type equalities. *) *)
(*         todo. *)

(*     } *)

(* Defined. *)

End Translation.
