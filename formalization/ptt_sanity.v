(* Sanity theorems for ptt. *)

Require Import syntax.
Require Import ptt.
Require Import ptt_tactics ptt_admissible.

Definition sane_issubst sbs G D :
  issubst sbs G D -> isctx G * isctx D.
Proof.
  intro H ; destruct H.

  (* SubstZero *)
  { split.

    - assumption.
    - now apply CtxExtend.
  }

  (* SubstWeak *)
  { split.

    - now apply CtxExtend.
    - assumption.
  }

  (* SubstShift *)
  { split.

    - apply CtxExtend.
      + assumption.
      + now apply (@TySubst G D).
    - now apply CtxExtend.
  }

  (* SubstId *)
  { split.
    - assumption.
    - assumption.
  }

  (* SubstComp *)
  { split.
    - assumption.
    - assumption.
  }

  (* SubstCtxConv *)
  { split.
    - assumption.
    - assumption.
  }
Defined.

Definition sane_istype G A :
  istype G A -> isctx G.
Proof.
  intro H; destruct H ; assumption.
Defined.

Definition sane_isterm' G u A :
  isterm G u A -> istype G A.
Proof.
  intro H ; destruct H.

  (* TermTyConv *)
  { assumption. }

  (* TermCtxConv *)
  { now apply (@TyCtxConv G D). }

  (* TermSubst *)
  { now apply (@TySubst G D A sbs). }

  (* TermVarZero *)
  { eapply TySubst.
    - now eapply SubstWeak.
    - assumption.
    - now apply (@CtxExtend G A).
    - eassumption.
  }

  (* TermVarSucc *)
  { apply (@TySubst (ctxextend G B) G).
    - now apply SubstWeak.
    - assumption.
    - now apply CtxExtend.
    - assumption.
  }

  (* TermAbs *)
  { now apply (@TyProd). }

  (* TermApp *)
  { apply (@TySubst G (ctxextend G A)).
    - now apply SubstZero.
    - assumption.
    - assumption.
    - now apply CtxExtend.
  }

  (* TermRefl *)
  { now apply TyId. }

  (* TermJ *)
  { magic. Unshelve. all:strictmagic. }

  (* TermExfalso *)
  { assumption. }

  (* TermUnit *)
  { now apply TyUnit. }

  (* TermTrue *)
  { now apply TyBool. }

  (* TermFalse *)
  { now apply TyBool. }

  (* TermCond *)
  { eapply (@TySubst G (ctxextend G Bool)).
    + apply SubstZero.
      * assumption.
      * now apply TyBool.
      * assumption.
    + assumption.
    + assumption.
    + apply CtxExtend.
      * assumption.
      * now apply TyBool.
  }
Defined.


Definition sane_isterm G u A :
  isterm G u A -> isctx G * istype G A.
Proof.
  intro H.
  pose (K := sane_isterm' G u A H).
  split ; [now apply (@sane_istype G A) | assumption].
Defined.

Definition sane_eqtype' G A B :
  eqtype G A B -> istype G A * istype G B.
Proof.
  intro H ; destruct H.

  (* EqTyCtxConv *)
  { split.
    - { now apply (@TyCtxConv G D). }
    - { now apply (@TyCtxConv G D). }
  }

  (* EqTyRefl*)
  { split ; assumption. }

  (* EqTySym *)
  { split ; assumption. }

  (* EqTyTrans *)
  { split ; assumption. }

  (* EqTyIdSubst *)
  { split.
    - eapply TySubst.
      + now apply SubstId.
      + assumption.
      + assumption.
      + eassumption.
    - assumption.
  }

  (* EqTySubstComp *)
  { split.
    - apply (@TySubst G D) ; auto.
      apply (@TySubst D E) ; auto.
    - apply (@TySubst G E) ; auto.
      apply (@SubstComp G D E) ; auto.
  }

  (* EqTySubstProd *)
  { split.
    - { apply (@TySubst G D) ; auto using TyProd. }
    - { apply TyProd ; auto.
        + apply (@TySubst _ (ctxextend D A)) ; auto.
          * now apply SubstShift.
          * apply CtxExtend ; auto.
            now apply (@TySubst G D).
          * now apply CtxExtend.
        + now apply (@TySubst G D).
      }
  }

  (* EqTySubstId *)
  { split.
    - { apply (@TySubst G D) ; auto using TyId. }
    - { apply TyId ; auto using (@TySubst G D), (@TermSubst G D). }
  }

  (* EqTySubstEmpty *)
  { split.
    - { apply (@TySubst G D) ; auto using TyEmpty. }
    - { now apply TyEmpty. }
  }

  (* EqTySubstUnit *)
  { split.
    - { apply (@TySubst G D) ; auto using TyUnit. }
    - { now apply TyUnit. }
  }

  (* EqTySubstBool *)
  { split.
    - { apply (@TySubst G D) ; auto using TyBool. }
    - { now apply TyBool. }
  }

  (* EqTyExfalso *)
  { split ; assumption. }

  (* CongProd *)
  { split.
    - { now apply TyProd. }
    - { apply TyProd ; auto.
        apply (@TyCtxConv (ctxextend G A1)) ; auto using CtxExtend.
        apply EqCtxExtend ; auto using CtxRefl.
      }
  }

  (* CongId *)
  { split.
    - { now apply TyId. }
    - { apply TyId.
        - assumption.
        - assumption.
        - now apply (@TermTyConv G A B v1).
        - now apply (@TermTyConv G A B v2).
      }
  }

  (* CongTySubst *)
  { split.
    - { now apply (@TySubst G D). }
    - { now apply (@TySubst G D). }
  }

Defined.

Theorem sane_eqctx G D :
  eqctx G D -> isctx G * isctx D.
Proof.
  intro H ; destruct H.

  (* CtxRefl *)
  { split.
    - assumption.
    - assumption.
  }

  (* CtxSym *)
  { split.
    - assumption.
    - assumption.
  }

  (* CtxTrans *)
  { split.
    - assumption.
    - assumption.
  }

  (* EqCtxEmpty *)
  { split.
    - now apply CtxEmpty.
    - now apply CtxEmpty.
  }

  (* EqCtxExtend *)
  { split.
    - now apply CtxExtend.
    - apply CtxExtend.
      + assumption.
      + apply (@TyCtxConv G D) ; auto.
  }

Defined.


Theorem sane_eqtype G A B :
  eqtype G A B -> isctx G * istype G A * istype G B.
Proof.
  intro H.
  destruct (sane_eqtype' G A B H).
  auto using (sane_istype G A).
Defined.

Theorem sane_eqsubst' sbs sbt G D :
  eqsubst sbs sbt G D -> issubst sbs G D * issubst sbt G D.
Proof.
  intro H ; destruct H.

  (* SubstRefl *)
  - { split.
      - assumption.
      - assumption.
    }

  (* SubstSym *)
  - { split.
      - assumption.
      - assumption.
    }

  (* SubstTrans *)
  - { split.
      - assumption.
      - assumption.
    }

  (* CongSubstZero *)
  - { split.
      - now apply SubstZero.
      - apply (@SubstCtxConv G2 G1 (ctxextend G2 A2) (ctxextend G1 A1)) ;
          auto using CtxExtend, CtxRefl, CtxSym.
        + apply SubstZero ;
            auto using (@TyCtxConv G1 G2), (@TermCtxConv G1 G2), (@TermTyConv G1 A1 A2).
        + apply EqCtxExtend ;
            auto using (@TyCtxConv G1 G2), CtxSym, (@EqTyCtxConv G1 G2), EqTySym.
        + apply CtxExtend ; auto using (@TyCtxConv G1 G2).
    }

  (* CongSubstWeak *)
  - { split.
      - now apply SubstWeak.
      - apply (@SubstCtxConv (ctxextend G2 A2) (ctxextend G1 A1) G2 G1) ;
          auto using CtxExtend, CtxRefl.
        + apply SubstWeak ; auto.
          now apply (@TyCtxConv G1, G2).
        + apply EqCtxExtend ; auto using (@TyCtxConv G1 G2), CtxSym.
          apply (@EqTyCtxConv G1 G2) ; auto using EqTySym.
        + now apply CtxSym.
        + apply CtxExtend ; auto.
          now apply (@TyCtxConv G1 G2).
    }

  (* CongSubstShift *)
  - { split.
      - now apply SubstShift.
      - apply (@SubstCtxConv (ctxextend G2 (Subst A2 sbs2)) _ (ctxextend D A2) _) ;
          auto using CtxExtend.
        + apply SubstShift ; auto.
          apply (@SubstCtxConv G1 _ D D) ; auto using CtxRefl.
        + apply EqCtxExtend ; auto.
          * apply (@TySubst G2 D) ; auto.
            apply (@SubstCtxConv G1 _ D D); auto using CtxRefl.
          * apply (@TyCtxConv G1 G2); auto.
            now apply (@TySubst G1 D).
          * now apply CtxSym.
          * apply (@EqTyCtxConv G1 G2); auto using (@TySubst G1 D).
            apply (@CongTySubst G1 D) ; auto using EqTySym, SubstSym.
        + apply EqCtxExtend ; auto using EqTySym, CtxRefl.
        + apply CtxExtend ; auto.
          apply (@TyCtxConv G1 G2) ; auto.
          now apply (@TySubst G1 D).
        + apply CtxExtend ; auto.
          now apply (@TySubst G1 D).
    }

  (* CongSubstComp *)
  - { split.
      - now apply (@SubstComp G D E).
      - now apply (@SubstComp G D E).
    }

  (* EqSubstCtxConv *)
  - { split.
      - now apply (@SubstCtxConv G1 G2 D1 D2).
      - now apply (@SubstCtxConv G1 G2 D1 D2).
    }

  (* CompAssoc *)
  - { split.
      - apply (@SubstComp G E F) ; auto.
        now apply (@SubstComp G D E).
      - apply (@SubstComp G D F); auto.
        now apply (@SubstComp D E F).
    }

  (* WeakNat *)
  - { split.
      - apply (@SubstComp _ (ctxextend D A)) ;
          auto using CtxExtend, (@TySubst G D), SubstShift, SubstWeak.
      - apply (@SubstComp _ G) ;
          auto using CtxExtend, (@TySubst G D), SubstWeak.
    }

  (* WeakZero *)
  - { split.
      - apply (@SubstComp _ (ctxextend G A)) ;
          auto using CtxExtend, SubstZero, SubstWeak.
      - now apply SubstId.
    }

  (* ShiftZero *)
  - { split.
      - apply (@SubstComp _ (ctxextend G (Subst A sbs))) ;
          auto using CtxExtend, (@TySubst G D), SubstZero, (@TermSubst G D), SubstShift.
      - apply (@SubstComp _ D) ;
          auto using CtxExtend, SubstZero.
    }

  (* CompShift *)
  - { split.
      - apply (@SubstComp _ (ctxextend D (Subst A sbt))) ;
          auto using CtxExtend, (@TySubst D E), SubstShift.
        + { apply (@SubstCtxConv (ctxextend G (Subst (Subst A sbt) sbs)) _
                                 (ctxextend D (Subst A sbt))) ;
            auto using CtxExtend, (@TySubst D E), (@TySubst G D), (@TySubst G E),
                       (@SubstComp G D E), SubstShift, CtxRefl.
            apply EqCtxExtend ;
                auto using CtxRefl, (@TySubst G D), (@TySubst D E),
                           (@TySubst G E), (@SubstComp G D E).
              now apply (@EqTySubstComp G D E).
          }
        + apply CtxExtend ; auto.
          apply (@TySubst G E) ; auto using (@SubstComp G D E).
      - apply SubstShift ; auto using (@SubstComp G D E).
    }

  (* CompIdRight *)
  - { split.
      - apply (@SubstComp G G D) ; auto using SubstId.
      - assumption.
    }

  (* CompIdLeft *)
  - { split.
      - apply (@SubstComp G D D) ; auto using SubstId.
      - assumption.
    }
Defined.

Theorem sane_eqsubst sbs sbt G D :
  eqsubst sbs sbt G D -> isctx G * isctx D * issubst sbs G D * issubst sbt G D.
Proof.
  intro H.
  destruct (sane_eqsubst' sbs sbt G D H).
  auto using (sane_issubst sbs G D).
Defined.

Theorem sane_eqterm' G u v A :
  eqterm G u v A -> isterm G u A * isterm G v A.
Proof.
  intro H ; destruct H.

  (* EqTyConv *)
  - { split.
      - { now apply (@TermTyConv G A B u). }
      - { now apply (@TermTyConv G A B v). }
    }

  (* EqCtxConv *)
  - { split.
      - { now apply (@TermCtxConv G D A). }
      - { now apply (@TermCtxConv G D A). }
    }

  (* EqRefl *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* EqSym *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* EqTrans *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* EqIdSubst *)
  - { split.
      - { apply (@TermTyConv G (Subst A (sbid G)) A).
          - apply (@TermSubst G G) ; auto using SubstId.
          - now apply EqTyIdSubst.
          - assumption.
          - apply (@TySubst G G) ; auto using SubstId.
          - assumption.
        }
      - { assumption. }
    }

  (* EqSubstComp *)
  - { split.
      - { apply (@TermTyConv G (Subst (Subst A sbt) sbs) (Subst A (sbcomp sbt sbs))).
          - apply (@TermSubst G D) ; auto.
            + now apply (@TermSubst D E).
            + now apply (@TySubst D E).
          - now apply (@EqTySubstComp G D E).
          - assumption.
          - apply (@TySubst G D) ; auto.
            now apply (@TySubst D E).
          - apply (@TySubst G E) ; auto.
            now apply (@SubstComp G D E).
        }
      - { apply (@TermSubst G E) ; auto.
          now apply (@SubstComp G D E).
        }
    }

  (* EqSubstWeak *)
  - { split.
      - { apply (@TermSubst _ G) ; auto using CtxExtend.
          now apply SubstWeak.
        }
      - { now apply TermVarSucc. }
    }


  (* EqSubstZeroZero *)
  - { split.
      - { apply (@TermTyConv G (Subst (Subst A (sbweak G A)) (sbzero G A u))).
          - apply (@TermSubst _ (ctxextend G A)) ; auto using CtxExtend.
            + now apply SubstZero.
            + now apply TermVarZero.
            + apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
          - apply (@EqTyTrans G _ (Subst A (sbid G))) ; auto.
            + { apply (@EqTyTrans _ _ (Subst A (sbcomp (sbweak G A) (sbzero G A u)))) ; auto.
                - apply (@EqTySubstComp G (ctxextend G A) G) ;
                    auto using CtxExtend, (@SubstComp G (ctxextend G A)) , SubstWeak, SubstZero.
                - apply (@CongTySubst G G) ;
                    auto using CtxExtend, (@SubstComp G (ctxextend G A)) , SubstWeak, SubstZero, SubstId, EqTyRefl, WeakZero.
                - apply (@TySubst _ (ctxextend G A)) ; auto using CtxExtend, SubstZero.
                  apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
                - apply (@TySubst _ G) ; auto.
                  + apply (@SubstComp _ (ctxextend G A)) ; auto using CtxExtend, SubstWeak, SubstZero.
                - apply (@TySubst _ G) ; auto using SubstId.
              }
            + now apply EqTyIdSubst.
            + apply (@TySubst _ (ctxextend G A)) ; auto using CtxExtend.
              * now apply SubstZero.
              * apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
            + apply (@TySubst _ G) ; auto using SubstId.
          - assumption.
          - apply (@TySubst _ (ctxextend G A)) ; auto using CtxExtend.
            + now apply SubstZero.
            + apply (@TySubst _ G) ; auto using CtxExtend.
              now apply SubstWeak.
          - assumption.
        }
      - { assumption. }
    }

  (* EqSubstZeroSucc *)
  - { split.
      - { apply (@TermTyConv G (Subst (Subst A (sbweak G B)) (sbzero G B u))).
          - apply (@TermSubst G (ctxextend G B)) ; auto using CtxExtend.
            + now apply SubstZero.
            + now apply TermVarSucc.
            + apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
          - apply EqTySym ; magic.
          - assumption.
          - apply (@TySubst _ (ctxextend G B)) ; auto using CtxExtend, SubstZero.
            apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
          - assumption.
        }
      - { assumption. }
    }

  (* EqSubstShiftZero *)
  - { split.
      - { eapply TermTyConv.
          - eapply TermSubst.
            + eapply SubstShift ; eassumption.
            + magic.
            + constructor.
              * assumption.
              * eapply TySubst ; eassumption.
            + eapply TySubst ; try eassumption ; magic.
            + magic.
          - apply EqTyWeakNat ; magic.
          - constructor.
            + assumption.
            + eapply TySubst ; eassumption.
          - eapply TySubst.
            + eapply SubstShift ; eassumption.
            + eapply TySubst ; magic.
            + constructor.
              * assumption.
              * eapply TySubst ; eassumption.
            + magic.
          - eapply TySubst.
            + eapply SubstWeak.
              * eapply TySubst ; eassumption.
              * assumption.
            + eapply TySubst ; eassumption.
            + constructor. (* There may be room for maigc improvement here *)
              * assumption.
              * eapply TySubst ; eassumption.
            + magic.
        }
      - { magic. }
    }

  (* EqSubstShiftSucc *)
  - { split.
      - { magic. Unshelve. all:strictmagic. }
      - { magic. }
    }

  (* EqSubstAbs *)
  - { split.
      - { magic. Unshelve. all:strictmagic. }
      - { magic. }
    }

  (* EqSubstApp *)
  - { split.
      - { magic. }
      - { magic. Unshelve. all:strictmagic. }
    }

  (* EqSubstRefl *)
  - { split.
      - { magic. Unshelve. all:strictmagic. }
      - { magic. }
    }

  (* EqSubstJ *)
  - { split.
      - { magic. Unshelve. all:strictmagic. }
      - { magic.
          Unshelve. all:try (check_goal ; assumption).
          all:try okmagic.
          Unshelve. all:try okmagic.
          Unshelve.
          (* 27:instantiate (1 := subst (refl (Subst A sbs) (subst u sbs)) *)
          (*                           (sbweak G (Subst A sbs))). *)
          all:try (eapply EqRefl).
          all:try okmagic.
          Unshelve. all:try (check_goal ; assumption).
          all:try okmagic. Unshelve.
          all:try (eapply EqRefl).
          all:try okmagic. Unshelve.
          all:match goal with
              | |- eqterm _ _ _ _ => idtac
              | |- eqtype _ _ _ => idtac
              | _ => shelve
              end.
          11:instantiate(1 := subst u (sbweak _ _)).
          12:instantiate(1 := var 0).
          13:instantiate(1 := subst u (sbweak _ _)).
          14:instantiate(1 := var 0).
          15:instantiate(1 := subst u (sbweak _ _)).
          16:instantiate(1 := var 0).
          17:instantiate(1 := subst u (sbweak _ _)).
          18:instantiate(1 := var 0).
          19:instantiate(1 := subst u (sbweak _ _)).
          20:instantiate(1 := var 0).
          21:instantiate(1 := subst u (sbweak _ _)).
          22:instantiate(1 := var 0).
          23:instantiate(1 := subst u (sbweak _ _)).
          24:instantiate(1 := var 0).
          25:instantiate(1 := subst u (sbweak _ _)).
          26:instantiate(1 := var 0).
          27:instantiate(1 := subst u (sbweak _ _)).
          28:instantiate(1 := var 0).
          29:instantiate(1 := subst u (sbweak _ _)).
          30:instantiate(1 := var 0).
          31:instantiate(1 := subst u (sbweak _ _)).
          32:instantiate(1 := var 0).
          33:instantiate(1 := subst u (sbweak _ _)).
          34:instantiate(1 := var 0).
          35:instantiate(1 := subst u (sbweak _ _)).
          36:instantiate(1 := var 0).
          37:instantiate(1 := subst u (sbweak _ _)).
          38:instantiate(1 := var 0).
          39:instantiate(1 := subst u (sbweak _ _)).
          40:instantiate(1 := var 0).
          41:instantiate(1 := subst u (sbweak _ _)).
          42:instantiate(1 := var 0).
          43:instantiate(1 := subst u (sbweak _ _)).
          44:instantiate(1 := var 0).
          50:instantiate(1 := subst u (sbweak _ _)).
          51:instantiate(1 := var 0).
          52:instantiate(1 := subst u (sbweak _ _)).
          53:instantiate(1 := var 0).
          59:instantiate(1 := subst u (sbweak _ _)).
          60:instantiate(1 := var 0).
          61:instantiate(1 := subst u (sbweak _ _)).
          62:instantiate(1 := var 0).
          63:instantiate(1 := subst u (sbweak _ _)).
          64:instantiate(1 := var 0).
          65:instantiate(1 := subst u (sbweak _ _)).
          66:instantiate(1 := var 0).
          67:instantiate(1 := subst u (sbweak _ _)).
          68:instantiate(1 := var 0).
          69:instantiate(1 := subst u (sbweak _ _)).
          70:instantiate(1 := var 0).
          71:instantiate(1 := subst u (sbweak _ _)).
          72:instantiate(1 := var 0).
          73:instantiate(1 := subst u (sbweak _ _)).
          74:instantiate(1 := var 0).
          75:instantiate(1 := subst u (sbweak _ _)).
          76:instantiate(1 := var 0).
          77:instantiate(1 := subst u (sbweak _ _)).
          78:instantiate(1 := var 0).
          79:instantiate(1 := subst u (sbweak _ _)).
          80:instantiate(1 := var 0).
          81:instantiate(1 := subst u (sbweak _ _)).
          82:instantiate(1 := var 0).
          83:instantiate(1 := subst u (sbweak _ _)).
          84:instantiate(1 := var 0).
          85:instantiate(1 := subst u (sbweak _ _)).
          86:instantiate(1 := var 0).
          87:instantiate(1 := subst u (sbweak _ _)).
          88:instantiate(1 := var 0).
          89:instantiate(1 := subst u (sbweak _ _)).
          90:instantiate(1 := var 0).
          91:instantiate(1 := subst u (sbweak _ _)).
          92:instantiate(1 := var 0).
          93:instantiate(1 := subst u (sbweak _ _)).
          94:instantiate(1 := var 0).
          all:try okmagic.
          1:instantiate(1 := refl _ _).
          1:magic.
          fail.
          (* We should find something better that this below *)
          1:instantiate (1 := subst (subst p sbs) (sbcomp (sbweak _ _) (sbweak _ _))).
          1:magic.
          all:instantiate (1 := var 0).



          all:try okmagic.
          all:instantiate ()


          all:try okmagic.
          Unshelve. all:try (check_goal ; assumption).
          28:eapply EqRefl.
          31:eapply EqRefl.
          54:eapply EqRefl.
          all:try okmagic.
          Unshelve. all:try (check_goal ; assumption).
          24:eapply EqRefl.


          (* magic shouldn't shelve this! *)
          fail.
        }
    }

  (* EqSubstExfalso *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstUnit *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstTrue *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstFalse *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstCond *)
  - { split.
      - { magic. }
      - { magic.
          Unshelve. all:magic.
          Unshelve. all:strictmagic.
        }
    }

  (* EqTermExfalso *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* UnitEta *)
  - { split.
      - { assumption. }
      - { magic. }
    }

  (* EqReflection *)
  - { split.
      - { assumption. }
      - { magic. }
    }

  (* ProdBeta *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CondTrue *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CondFalse *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* ProdEta *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* JRefl *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongAbs *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongApp *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongRefl *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongJ *)
  - { split.
      - { magic. }
      - { magic.
          Unshelve. all:try magic.
          Unshelve. all:try magic.
          Unshelve. all:admit.
        }
    }

  (* CongCond *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongTermSubst *)
  - { split.
      - { magic. }
      - { magic. }
    }

Defined.

Theorem sane_eqterm G u v A :
  eqterm G u v A -> isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  intro H.
  destruct (sane_eqterm' G u v A H).
  auto using (@sane_isterm G u A).
Defined.
