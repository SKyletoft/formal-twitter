open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Data.Empty                            using (⊥-elim)
open import Data.Product                          using (∃-syntax)
open import Data.String                           using (_≟_)
open import Data.Unit                             using (tt)
open import Function                              using (_∘_; _$_; const)
open import Relation.Binary.Definitions           using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
                                                         sym; trans; subst)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Relation.Nullary.Negation.Core        using (¬_)

open import Helpers
open import Lemmas

module Proofs
  (SessionId PostId : Set)
  (new-sid : CreateNew SessionId)
  (new-pid : CreateNew PostId)
  (_≟ₚ_ : DecidableEquality PostId)
  (_≟ₛᵢ_ : DecidableEquality SessionId)
  where
open import Twitter SessionId PostId new-sid new-pid _≟ₚ_ _≟ₛᵢ_

open import Add PostId _≟ₚ_ Post
  using    ()
  renaming (add to add-post; add-same to add-post-same; add-at to add-post-at;
            add-no to add-post-no; add-inj to add-post-inj; add-used to add-post-used;
            add-used-keep to add-post-used-keep; add-posts to add-post-posts;
            add-prop to add-post-prop; add-prop² to add-post-prop²;
            add-present to add-post-present; add-witness to add-post-witness)

open import Add String _≟_ Account
  using    ()
  renaming (add to add-account-at; add-same to add-account-same; add-no to add-account-no)

open import Update SessionId _≟ₛᵢ_ SessionStatus unused
  using    ()
  renaming (update to add-session-at; update-same to add-session-same;
            update-no to add-session-no; update-no-¬ to add-session-no-¬;
            update-used to add-session-used;
            update-used-keep to add-session-used-keep)

--------------------------------------------------------------------------------
--                                PROOF-TYPES                                 --
--------------------------------------------------------------------------------

PostDoesntExistBeforePosting =
  ∀ {before after sid pid txt parent} →
  Step before (publish sid txt parent) after (created-post pid) →
  (pid ∉ World.newest-first before) ∧ (World.post-at before pid ≡ nothing)

CantReplyToDeletedTweet =
  ∀ {before after sid txt parent pid post} →
  World.post-at before parent ≡ just post →
  Post.status post            ≡ deleted →
  ¬ Step before (publish sid txt (just parent)) after (created-post pid)

CantReplyToTweetYouCantRead =
  ∀ {before after sid pid txt parent} →
  ¬ CanReadPost before sid parent →
  ¬ Step before (publish sid txt (just parent)) after (created-post pid)

CantMakePublicReplyToPrivateParent =
  ∀ {before after pid sid txt parent post parent-post} →
  World.post-at before parent ≡ just parent-post →
  World.post-at after pid     ≡ just post →
  Post.visibility parent-post ≡ followers-only →
  Post.visibility post        ≡ everyone →
  ¬ Step before (publish sid txt (just parent)) after (created-post pid)

CantDeleteOthersTweets =
  ∀ {before after sid pid post user} →
  World.session-at before sid ≡ active user →
  World.post-at before pid    ≡ just post →
  Post.author post            ≢ user →
  ¬ Step before (delete sid pid) after success

CantLikeForOtherAccount =
  ∀ {before after pid sid acc post post' user other-user} →
  ValidSession before sid acc user →
  user                        ≢ other-user →
  World.session-at before sid ≡ active user →
  World.post-at before pid    ≡ just post →
  other-user                  ∉ Post.likes post →
  World.post-at after pid     ≡ just post' →
  other-user                  ∈ Post.likes post' →
  ¬ Step before (like sid pid) after success

FailedDeleteDoesNothing =
  ∀ {before after sid pid status} →
  Step before (delete sid pid) after status →
  status ≢ success →
  before ≡ after

FailedPostDoesNothing =
  ∀ {before after sid txt parent status} →
  Step before (publish sid txt parent) after status →
  ¬ (∃[ pid ] status ≡ created-post pid) →
  before ≡ after

FailedLikeDoesNothing =
  ∀ {before after sid pid status} →
  Step before (like sid pid) after status →
  status ≢ success →
  before ≡ after

FailedUnlikeDoesNothing =
  ∀ {before after sid pid status} →
  Step before (unlike sid pid) after status →
  status ≢ success →
  before ≡ after

FailedFollowDoesNothing =
  ∀ {before after sid status user} →
  Step before (follow sid user) after status →
  status ≢ success →
  before ≡ after

FailedUnfollowDoesNothing =
  ∀ {before after sid status user} →
  Step before (unfollow sid user) after status →
  status ≢ success →
  before ≡ after

FailedRegisterDoesNothing =
  ∀ {before after status user passwd} →
  Step before (register user passwd) after status →
  status ≢ success →
  before ≡ after

FailedLoginDoesNothing =
  ∀ {before after status user passwd} →
  Step before (authenticate user passwd) after status →
  ¬ (∃[ sid ] status ≡ issued-session sid) →
  before ≡ after

StepExists =
  (before : World) →
  (cmd : Command) →
  ∃[ after ] ∃[ result ]
  Step before cmd after result

--------------------------------------------------------------------------------
--                                  HELPERS                                   --
--------------------------------------------------------------------------------

deleted≢live            : deleted ≢ live                   ; deleted≢live ()
everyone≢followers-only : everyone ≢ followers-only        ; everyone≢followers-only ()
active≢unused           : ∀ {user} → active user ≢ unused  ; active≢unused ()
unused≢active           : ∀ {user} → unused ≢ active user  ; unused≢active ()
revoked≢active          : ∀ {user} → revoked ≢ active user ; revoked≢active ()
revoked≢unused          : revoked ≢ unused                 ; revoked≢unused ()

new-reply-private :
  ∀ {username txt user parent-id ppost} →
  Post.visibility ppost ≡ followers-only →
  Post.visibility (new-reply username txt user parent-id ppost) ≡ followers-only
new-reply-private {ppost = record { visibility = everyone }} ()
new-reply-private {ppost = record { visibility = followers-only }} refl = refl

update-vs : ∀{w s s₁ a u} → ValidSession w s₁ a u → s ≡ s₁ → ValidSession w s a u
update-vs vs refl = vs

expired-access :
  ∀ {w cmd sid} →
  extract-sid cmd ≡ just sid →
  ¬ (∃[ acc ] ∃[ user ] ValidSession w sid acc user) →
  Step w cmd w expired
expired-access msid-eq ¬vs =
  failed-access λ {eq (acc , username , vs) →
                   ¬vs (acc , username ,
                     update-vs vs (just-injective (trans (sym msid-eq) eq)))}

add-post-replies :
  ∀ {f : PostId → Maybe Post} →
  ∀ {pid p} →
  f pid ≡ nothing →
  Post.replies p ≡ [] →
  (∀ {ppid ppost cpid} →
      cpid ∈ Post.replies ppost →
      f ppid ≡ just ppost →
      ∃[ cpost ] f cpid ≡ just cpost
      ∧ Post.parent cpost ≡ just ppid
      ∧ cpid ≢ ppid) →
  ∀ {parent-pid parent-post child-pid} →
  child-pid ∈ Post.replies parent-post →
  add-post f pid p parent-pid ≡ just parent-post →
  ∃[ cpost ] add-post f pid p child-pid ≡ just cpost
             ∧ Post.parent cpost ≡ just parent-pid
             ∧ child-pid ≢ parent-pid
add-post-replies {f = f} {pid = pid} absent re-empty Fold
                 {parent-pid} {parent-post} {child-pid} child∈ peq =
  Dec-elim (pid ≟ₚ parent-pid)
    (λ eq →
      let parent-post≡p = add-post-inj peq eq
      in ⊥-elim
         ∘ ∈[]
         ∘ subst (λ rs → child-pid ∈ rs) re-empty
         ∘ subst (λ pp → child-pid ∈ Post.replies pp) parent-post≡p
         $ child∈)
    (λ ne →
      let w-eq = trans (sym (add-post-no ne)) peq
          child-post , child-eq , parent-eq , child-ne′ = Fold child∈ w-eq
          child-ne : pid ≢ child-pid
          child-ne e = nothing≢just
            (trans (sym absent)
              (subst (λ z → f z ≡ just child-post) (sym e) child-eq))
      in child-post , trans (add-post-no child-ne) child-eq , parent-eq , child-ne′)

make-new-post :
  ∀ {pid} →
  (w : World) →
  (user : String) →
  (txt : String) →
  (acc : Account) →
  pid ∉ World.used-post-ids w →
  ∃[ after ] PostIsNew w after pid (new-post user txt acc)
make-new-post
  {pid}
  w@(world account-at session-at post-at follows newest-first used-post-ids
           used-session-ids only-used-pids only-used-sids only-valid-sessions
           only-valid-posts only-valid-replies no-duplicate-replies
           no-duplicate-likes no-duplicate-posts)
  user txt acc ∉w =
    after , post-is-new absent add-post-same
  where
    p : Post
    p = post user txt (Account.default-visibility acc) live [] [] nothing

    absent : post-at pid ≡ nothing
    absent = snd only-used-pids ∉w

    pid∉newest : pid ∉ newest-first
    pid∉newest = ∉-witnessed absent only-valid-posts

    after : World
    after = world account-at
                  session-at
                  (add-post post-at pid p)
                  follows
                  (pid ∷ newest-first)
                  (pid ∷ used-post-ids)
                  used-session-ids
                  (add-post-used ∉w only-used-pids)
                  only-used-sids
                  only-valid-sessions
                  (add-post-posts only-valid-posts (∉-distinct absent only-valid-posts))
                  (add-post-replies absent refl only-valid-replies)
                  (add-post-prop p tt no-duplicate-replies)
                  (add-post-prop p tt no-duplicate-likes)
                  (uniq-cons pid newest-first pid∉newest no-duplicate-posts)

reply-to : Post → PostId → Post
reply-to (post author text visibility status likes replies parent) pid' =
  post author text visibility status likes (pid' ∷ replies) parent

parent-of-reply-to :
  ∀ {q : Post} {i : PostId} → Post.parent (reply-to q i) ≡ Post.parent q
parent-of-reply-to = refl

replies-of-reply-to :
  ∀ {q : Post} {i : PostId} → Post.replies (reply-to q i) ≡ i ∷ Post.replies q
replies-of-reply-to = refl

new-reply-parent :
  ∀ {username txt user parent-id ppost} →
  Post.parent (new-reply username txt user parent-id ppost) ≡ just parent-id
new-reply-parent {ppost = record { visibility = everyone }} = refl
new-reply-parent {ppost = record { visibility = followers-only }} = refl

new-reply-replies :
  ∀ {username txt user parent-id ppost} →
  Post.replies (new-reply username txt user parent-id ppost) ≡ []
new-reply-replies {ppost = record { visibility = everyone }} = refl
new-reply-replies {ppost = record { visibility = followers-only }} = refl

new-reply-likes :
  ∀ {username txt user parent-id ppost} →
  Post.likes (new-reply username txt user parent-id ppost) ≡ []
new-reply-likes {ppost = record { visibility = everyone }} = refl
new-reply-likes {ppost = record { visibility = followers-only }} = refl

post-status-live :
  ∀ {a t v s l r pa'} → s ≡ live → post a t v s l r pa' ≡ post a t v live l r pa'
post-status-live {s = s} refl = refl

add-post-parent-replies :
  ∀ {f : PostId → Maybe Post} {pid ppid : PostId} (ppost p : Post) →
  pid ≢ ppid →
  f ppid ≡ just ppost →
  f pid ≡ just p →
  Post.parent p ≡ just ppid →
  (∀ {parent-pid parent-post child-pid} →
      child-pid ∈ Post.replies parent-post →
      f parent-pid ≡ just parent-post →
      ∃[ child-post ] f child-pid ≡ just child-post
                      ∧ Post.parent child-post ≡ just parent-pid
                      ∧ child-pid ≢ parent-pid) →
  ∀ {parent-pid parent-post child-pid} →
  child-pid ∈ Post.replies parent-post →
  add-post f ppid (reply-to ppost pid) parent-pid ≡ just parent-post →
  ∃[ child-post ] add-post f ppid (reply-to ppost pid) child-pid ≡ just child-post
                  ∧ Post.parent child-post ≡ just parent-pid
                  ∧ child-pid ≢ parent-pid
add-post-parent-replies {f} {pid} {ppid} ppost p pid≢ppid fppid fp prnt Fold
                        {parent-pid} {parent-post} {child-pid} child∈ peq =
  Dec-elim (ppid ≟ₚ parent-pid)
    (λ e →
      let peq′ = trans (sym (add-post-at {f = f} {k = ppid} {v = reply-to ppost pid}
                                           {parent-pid} e)) peq
          m′ = subst (λ pp → child-pid ∈ Post.replies pp) (sym (just-injective peq′))
                 child∈
      in Dec-elim (child-pid ≟ₚ pid)
        (λ e2 →
          p ,
          trans (add-post-no (λ ne → pid≢ppid (trans (sym e2) (sym ne))))
                (subst (λ z → f z ≡ just p) (sym e2) fp) ,
          trans prnt (cong just e) ,
          λ ne → pid≢ppid (trans (sym e2) (trans ne (sym e))))
        (λ ne2 →
          let cpost , ceq , cpar , cne = Fold (∈-not-head ne2 m′) fppid
          in cpost , trans (add-post-no (λ eₙ → cne (sym eₙ))) ceq
                 , trans cpar (cong just e)
                 , λ ne → cne (trans ne (sym e))))
    (λ ne →
      let w-eq = trans (sym (add-post-no {f = f} {k = ppid} {v = reply-to ppost pid}
                                          {parent-pid} ne)) peq
      in Dec-elim (child-pid ≟ₚ ppid)
        (λ e2 →
          let cpost , ceq , cpar , cne = Fold child∈ w-eq
              cpost≡ppost =
                just-injective
                  (trans (sym (subst (λ z → f z ≡ just cpost) e2 ceq)) fppid)
          in reply-to ppost pid ,
             add-post-at {f = f} {k = ppid} {v = reply-to ppost pid} {child-pid}
               (sym e2) ,
             trans (parent-of-reply-to {q = ppost} {i = pid})
                   (subst (λ q → Post.parent q ≡ just parent-pid) cpost≡ppost cpar) ,
             cne)
        (λ ne2 →
          let cpost , ceq , cpar , cne = Fold child∈ w-eq
          in cpost , trans (add-post-no (λ eₙ → ne2 (sym eₙ))) ceq , cpar , cne))

make-new-reply :
  ∀ {pid ppid} →
  (w : World) → (user : String) → (txt : String) → (acc : Account) →
  (ppost : Post) →
  World.post-at w ppid ≡ just ppost →
  pid ∉ World.used-post-ids w →
  ∃[ after ] PostIsNew w after pid (new-reply user txt acc ppid ppost)
make-new-reply
  {pid} {ppid}
  w@(world account-at session-at post-at follows newest-first used-post-ids
           used-session-ids only-used-pids only-used-sids only-valid-sessions
           only-valid-posts only-valid-replies no-duplicate-replies
           no-duplicate-likes no-duplicate-posts)
  user txt acc ppost pb ∉w = after , post-is-new absent is-present
  where
    p = new-reply user txt acc ppid ppost

    absent : post-at pid ≡ nothing
    absent = snd only-used-pids ∉w

    pid≢ppid : pid ≢ ppid
    pid≢ppid e =
      nothing≢just
        (trans (sym absent)
               (subst (λ z → post-at z ≡ just ppost) (sym e) pb))

    ppid≢pid : ppid ≢ pid
    ppid≢pid e = pid≢ppid (sym e)

    pid∉newest : pid ∉ newest-first
    pid∉newest = ∉-witnessed absent only-valid-posts

    pid∉ppost-replies : pid ∉ Post.replies ppost
    pid∉ppost-replies m =
      let cpost , ceq , _ , _ = only-valid-replies m pb
      in nothing≢just (trans (sym (snd only-used-pids ∉w)) ceq)

    F₁ = add-post post-at pid p

    F₁-posts = add-post-posts only-valid-posts (∉-distinct absent only-valid-posts)

    F₁-replies = add-post-replies absent
                     (new-reply-replies {username = user} {txt = txt} {user = acc}
                                        {parent-id = ppid} {ppost = ppost})
                     only-valid-replies

    F₁-used = add-post-used ∉w only-used-pids

    pb₁ : F₁ ppid ≡ just ppost
    pb₁ = trans (add-post-no pid≢ppid) pb

    is-present : add-post F₁ ppid (reply-to ppost pid) pid ≡ just p
    is-present = trans (add-post-no ppid≢pid) add-post-same

    uniq-of-new-reply : uniq (Post.replies p)
    uniq-of-new-reply =
      uniq-≡[] (Post.replies p)
               (new-reply-replies {username = user} {txt = txt} {user = acc}
                                  {parent-id = ppid} {ppost = ppost})

    uniq-of-reply-to : uniq (Post.replies (reply-to ppost pid))
    uniq-of-reply-to = uniq-cons pid (Post.replies ppost) pid∉ppost-replies
                         (no-duplicate-replies pb)

    uniq-of-new-likes : uniq (Post.likes p)
    uniq-of-new-likes =
      uniq-≡[] (Post.likes p)
               (new-reply-likes {username = user} {txt = txt} {user = acc}
                                {parent-id = ppid} {ppost = ppost})

    after : World
    after = world account-at
                  session-at
                  (add-post F₁ ppid (reply-to ppost pid))
                  follows
                  (pid ∷ newest-first)
                  (pid ∷ used-post-ids)
                  used-session-ids
                  (add-post-used-keep (reply-to ppost pid) pb₁ F₁-used)
                  only-used-sids
                  only-valid-sessions
                  (add-post-witness p (reply-to ppost pid) F₁-posts)
                  (add-post-parent-replies ppost p pid≢ppid pb₁
                    (add-post-same {f = post-at} {k = pid} {v = p})
                    (new-reply-parent {username = user} {txt = txt} {user = acc}
                                      {parent-id = ppid} {ppost = ppost})
                    F₁-replies)
                  (add-post-prop² p (reply-to ppost pid) uniq-of-new-reply
                    uniq-of-reply-to
                      no-duplicate-replies)
                  (add-post-prop² p (reply-to ppost pid) uniq-of-new-likes
                      (no-duplicate-likes pb) no-duplicate-likes)
                  (uniq-cons pid newest-first pid∉newest no-duplicate-posts)

add-post-replies-keep :
  ∀ {f : PostId → Maybe Post} {pid : PostId} {ppost ppost′ : Post} →
  f pid ≡ just ppost →
  Post.replies ppost′ ≡ Post.replies ppost →
  Post.parent ppost′ ≡ Post.parent ppost →
  (∀ {parent-pid parent-post child-pid} →
      child-pid ∈ Post.replies parent-post →
      f parent-pid ≡ just parent-post →
      ∃[ child-post ] f child-pid ≡ just child-post
                      ∧ Post.parent child-post ≡ just parent-pid
                      ∧ child-pid ≢ parent-pid) →
  ∀ {parent-pid parent-post child-pid} →
  child-pid ∈ Post.replies parent-post →
  add-post f pid ppost′ parent-pid ≡ just parent-post →
  ∃[ child-post ] add-post f pid ppost′ child-pid ≡ just child-post
                  ∧ Post.parent child-post ≡ just parent-pid
                  ∧ child-pid ≢ parent-pid
add-post-replies-keep {f = f} {pid = pid} {ppost = ppost} {ppost′ = ppost′}
                      fppid reeq par′eq Fold
  {parent-pid} {parent-post} {child-pid} child∈ peq =
  Dec-elim (pid ≟ₚ parent-pid)
    (λ e →
      let pe : parent-post ≡ ppost′
          pe = just-injective
                (trans (sym (subst (λ z → add-post f pid ppost′ z ≡ just parent-post)
                                   (sym e) peq))
                       (add-post-same {v = ppost′}))
          ce∈ : child-pid ∈ Post.replies ppost
          ce∈ = subst (λ rl → child-pid ∈ rl) reeq
                (subst (λ pp → child-pid ∈ Post.replies pp) pe child∈)
          fpp : f parent-pid ≡ just ppost
          fpp = subst (λ z → f z ≡ just ppost) e fppid
          c , ceq , cpar , cne = Fold ce∈ fpp
          ne-pid : pid ≢ child-pid
          ne-pid eqz = cne (trans (sym eqz) e)
        in c , trans (add-post-no ne-pid) ceq , cpar , cne)
    (λ ne →
      let fpar : f parent-pid ≡ just parent-post
          fpar = trans (sym (add-post-no ne)) peq
          c , ceq , cpar , cne = Fold child∈ fpar
        in Dec-elim (child-pid ≟ₚ pid)
          (λ e2 →
            let c≡ : c ≡ ppost
                c≡ = just-injective
                      (trans (sym ceq)
                             (subst (λ z → f z ≡ just ppost) (sym e2) fppid))
            in ppost′ , add-post-at (sym e2) ,
               trans par′eq
                 (subst (λ cc → Post.parent cc ≡ just parent-pid) c≡ cpar) , cne)
          (λ ne2 → c , trans (add-post-no (λ eqz → ne2 (sym eqz))) ceq , cpar , cne))

add-session-valid-add :
  ∀ {s : SessionId → SessionStatus} {sid : SessionId} {username : String}
    {user : Account} {account-at : String → Maybe Account} →
  s sid ≡ unused →
  account-at username ≡ just user →
  (∀ {sid′ u} → s sid′ ≡ active u → ∃[ acc ] account-at u ≡ just acc) →
  ∀ {sid′ u} → add-session-at s sid (active username) sid′ ≡ active u →
  ∃[ acc ] account-at u ≡ just acc
add-session-valid-add
  {s = s} {sid = sid} {username = username} {user = user} {account-at = account-at}
  unused-s acct Old
  {sid′} {u} eq =
  Dec-elim (sid ≟ₛᵢ sid′)
    (λ e → user , (subst (λ z → account-at z ≡ just user)
                         (active-injective
                          ∘ trans (sym
                                  ∘ subst
                                    (λ z → add-session-at s sid (active username) z
                                           ≡ active username) e
                                  $ add-session-same)
                          $ eq)
                         acct))
    (λ ne → Old ∘ trans (sym ∘ add-session-no $ ne) $ eq)

add-session-valid-revoke :
  ∀ {s : SessionId → SessionStatus} {sid : SessionId}
    {account-at : String → Maybe Account} →
  (∀ {sid′ u} → s sid′ ≡ active u → ∃[ acc ] account-at u ≡ just acc) →
  ∀ {sid′ u} → add-session-at s sid revoked sid′ ≡ active u →
  ∃[ acc ] account-at u ≡ just acc
add-session-valid-revoke {s = s} {sid = sid} {account-at = account-at} Old {sid′} {u} eq =
  Dec-elim (sid ≟ₛᵢ sid′)
    (λ e → ⊥-elim
           ∘ revoked≢active
           ∘ sym
           ∘ trans (sym eq)
           ∘ subst (λ z → add-session-at s sid revoked z ≡ revoked) e
           $ add-session-same)
    (λ ne → Old (trans (sym (add-session-no ne)) eq))

add-account-valid :
  ∀ {session-at : SessionId → SessionStatus} {acc-at : String → Maybe Account}
    {username : String} (new-acc : Account) →
  acc-at username ≡ nothing →
  (∀ {s u} → session-at s ≡ active u → ∃[ acc ] acc-at u ≡ just acc) →
  ∀ {s u} → session-at s ≡ active u →
  ∃[ acc ] add-account-at acc-at username new-acc u ≡ just acc
add-account-valid {acc-at = acc-at} {username = username} new-acc absent Old {s} {u} act =
  Dec-elim (username ≟ u)
    (λ e →
      let acc , eq = Old act
      in ⊥-elim
         ∘ nothing≢just
         ∘ trans (sym absent)
         ∘ subst (λ z → acc-at z ≡ just acc) (sym e)
         $ eq)
    (λ ne → let acc , eq = Old act in acc , trans (add-account-no ne) eq)

revoke-all : (SessionId → SessionStatus) → SessionId → SessionStatus
revoke-all s sid with s sid
... | active _ = revoked
... | unused   = unused
... | revoked  = revoked

revoke-all-active : ∀ {s : SessionId → SessionStatus} {sid : SessionId} {user} →
  s sid ≡ active user → revoke-all s sid ≡ revoked
revoke-all-active {s = s} {sid = sid} eq with s sid
... | active _ = refl
... | unused   = ⊥-elim (unused≢active eq)
... | revoked  = ⊥-elim (revoked≢active eq)

revoke-all-used : ∀ {us : List SessionId} {s : SessionId → SessionStatus} →
  (∀ {z} → (z ∈ us → s z ≢ unused) ∧ (z ∉ us → s z ≡ unused)) →
  (∀ {z} → (z ∈ us → revoke-all s z ≢ unused) ∧ (z ∉ us → revoke-all s z ≡ unused))
revoke-all-used {us = us} {s = s} fs {z} = go (fs {z})
  where
    go : ((z ∈ us → s z ≢ unused) ∧ (z ∉ us → s z ≡ unused)) →
         (z ∈ us → revoke-all s z ≢ unused) ∧ (z ∉ us → revoke-all s z ≡ unused)
    go fz with s z
    ... | active user =
        (λ _ → revoked≢unused) , (⊥-elim ∘ active≢unused ∘ snd fz)
    ... | unused      =
        fst fz , (const refl)
    ... | revoked     =
        (λ _ → revoked≢unused) , (⊥-elim ∘ revoked≢unused ∘ snd fz)

revoke-all-valid :
  ∀ {s : SessionId → SessionStatus} {account-at : String → Maybe Account} →
  (∀ {sid u} → s sid ≡ active u → ∃[ acc ] account-at u ≡ just acc) →
  ∀ {sid u} → revoke-all s sid ≡ active u → ∃[ acc ] account-at u ≡ just acc
revoke-all-valid {s = s} Old {sid} {u} eq with s sid
... | active _ = ⊥-elim (revoked≢active eq)
... | unused   = ⊥-elim (unused≢active eq)
... | revoked  = ⊥-elim (revoked≢active eq)

post-at-step :
  ∀ {w : World} {pid : PostId} →
  (ppost p′ : Post) →
  World.post-at w pid ≡ just ppost →
  Post.replies p′ ≡ Post.replies ppost →
  Post.parent p′ ≡ Post.parent ppost →
  uniq (Post.likes p′) →
  World
post-at-step {w@(world account-at session-at post-at follows newest-first
                       used-post-ids used-session-ids only-used-pids only-used-sids
                       only-valid-sessions only-valid-posts only-valid-replies
                       no-duplicate-replies no-duplicate-likes no-duplicate-posts)}
             {pid}
             ppost p′ pp≡ rp pp u =
  world account-at
    session-at
    (add-post post-at pid p′)
    follows
    newest-first
    used-post-ids
    used-session-ids
    (add-post-used-keep {f = post-at} {k = pid} {v₀ = ppost} p′ pp≡ only-used-pids)
    only-used-sids
    only-valid-sessions
    (add-post-present only-valid-posts)
    (add-post-replies-keep {f = post-at} {pid = pid} {ppost = ppost} {ppost′ = p′}
        pp≡ rp pp only-valid-replies)
    (add-post-prop p′ {P = λ w → uniq (Post.replies w)}
        (subst (λ r → uniq r) (sym rp) (no-duplicate-replies pp≡)) no-duplicate-replies)
    (add-post-prop p′ {P = λ w → uniq (Post.likes w)} u no-duplicate-likes)
    no-duplicate-posts

unlike-valid :
  ∀ {w : World} {sid : SessionId} {pid : PostId} →
  (pp : Maybe Post) →
  World.post-at w pid ≡ pp →
  (∃[ acc ] ∃[ user ] ValidSession w sid acc user) →
  ∃[ after ] ∃[ result ] Step w (unlike sid pid) after result
unlike-valid
  {w@(world account-at session-at post-at follows newest-first
            used-post-ids used-session-ids only-used-pids only-used-sids
            only-valid-sessions only-valid-posts only-valid-replies
            no-duplicate-replies no-duplicate-likes no-duplicate-posts)}
  {sid} {pid} pp pp≡ (acc , user , vs)
  with pp
     | can-read-post w sid pid
... | nothing                           | yes (post-is-public vs₁ eq₁ _ _) =
    ⊥-elim (nothing≢just (trans (sym pp≡) eq₁))
... | nothing                           | yes (post-is-private vs₁ eq₁ _ _ _) =
    ⊥-elim (nothing≢just (trans (sym pp≡) eq₁))
... | nothing                           | no ¬cp = w , denied , failed-unlike-post vs ¬cp
... | just (post pa pt pv ps pl pr pp₁) | no ¬cp = w , denied , failed-unlike-post vs ¬cp
... | just (post pa pt pv ps pl pr pp₁) | yes cp
  with ∈-decidable user pl
... | yes user∈ =
        let p′ : Post
            p′ = post pa pt pv ps (remove-like user pl user∈) pr pp₁

            after : World
            after = post-at-step {w} {pid} (post pa pt pv ps pl pr pp₁) p′ pp≡ refl refl
                      (remove-uniq user∈ (no-duplicate-likes pp≡))
        in after , success , unlike-post vs cp pp≡ (add-post-same {v = p′})
                 (remove-loses user∈ (no-duplicate-likes pp≡))
                 refl refl refl refl refl refl
                 remove-transport
                 (λ {other-pids} ne → sym (add-post-no ne) , refl , refl , refl , refl)
...   | no user∉ =
        w , _ , unlike-post vs cp pp≡ pp≡ user∉
                refl refl refl refl refl refl
                (λ {user′} ne → (λ m∈ → m∈) , (λ m∉ → m∉))
                (λ {other-pids} ne → refl , refl , refl , refl , refl)

delete-valid :
  ∀ {w : World} {sid : SessionId} {pid : PostId} →
  (pp : Maybe Post) →
  World.post-at w pid ≡ pp →
  (∃[ acc ] ∃[ user ] ValidSession w sid acc user) →
  ∃[ after ] ∃[ result ] Step w (delete sid pid) after result
delete-valid
  {w@(world account-at session-at post-at follows newest-first
            used-post-ids used-session-ids only-used-pids only-used-sids
            only-valid-sessions only-valid-posts only-valid-replies
            no-duplicate-replies no-duplicate-likes no-duplicate-posts)}
  {sid} {pid} pp pp≡ (acc , user , vs)
  with pp
... | nothing = w , denied , failed-delete-non-existant-post vs pp≡
... | just (post pa pt pv ps pl pr pp₁)
  with pa ≟ user
... | no pa≢user = w , denied , failed-delete-not-author vs pp≡ pa≢user
... | yes refl =
    let dp : Post
        dp = post pa pt pv deleted pl pr pp₁

        after : World
        after = post-at-step {w} {pid} (post pa pt pv ps pl pr pp₁) dp pp≡ refl refl
                  (no-duplicate-likes pp≡)
    in after , success , delete-post vs pp≡ (add-post-same {v = dp}) refl
         refl refl refl refl refl
         (λ {other-pid} {u1} {u2} {s} ne → sym (add-post-no ne) , refl , refl , refl)

read-post-valid :
  ∀ {w : World} {sid : SessionId} {pid : PostId} →
  (pp : Maybe Post) →
  World.post-at w pid ≡ pp →
  (∃[ acc ] ∃[ user ] ValidSession w sid acc user) →
  ∃[ after ] ∃[ result ] Step w (read-post (just sid) pid) after result
read-post-valid {w} {sid} {pid} pp pp≡ (acc , user , vs) with pp
... | nothing = w , denied , cant-read-post-public vs pp≡
... | just (post pa pt pv deleted pl pr pp₁) =
    w , denied , cant-read-post-private-deleted vs pp≡ refl
... | just (post pa pt pv live pl pr pp₁) with pv
... | everyone =
    w , _ , read-post-logged-in (post-is-public vs pp≡ refl refl)
      pp≡ refl refl refl refl
... | followers-only
  with World.follows w user pa in fq
... | true =
    w , _ , read-post-logged-in (post-is-private vs pp≡ refl refl fq)
      pp≡ refl refl refl refl
... | false = w , denied , cant-read-post-private vs pp≡ refl refl fq

--------------------------------------------------------------------------------
--                                   PROOFS                                   --
--------------------------------------------------------------------------------

post-doesnt-exist-before-posting : PostDoesntExistBeforePosting
post-doesnt-exist-before-posting {before}
    (successful-post _ (post-is-new wa _) _ _) =
  nothing≢just ∘ trans (sym wa) ∘ snd ∘ World.only-valid-posts before , wa
post-doesnt-exist-before-posting {before}
    (successful-reply _ (post-is-new wa _) _ _ _ _ _ _ _ _) =
  nothing≢just ∘ trans (sym wa) ∘ snd ∘ World.only-valid-posts before , wa

cant-reply-to-deleted-tweet : CantReplyToDeletedTweet
cant-reply-to-deleted-tweet pa st
    (successful-reply _ _ _ _ pe _ pb _ _ _)
  = deleted≢live
  ∘ trans (sym st)
  ∘ trans (cong Post.status ∘ just-injective ∘ trans (sym pa) $ pb)
  ∘ cong Post.status
  $ pe

cant-reply-to-tweet-you-cant-read : CantReplyToTweetYouCantRead
cant-reply-to-tweet-you-cant-read ¬cr
    (successful-reply _ _ _ cr _ _ _ _ _ _) = ¬cr cr

cant-make-public-reply-to-private-parent : CantMakePublicReplyToPrivateParent
cant-make-public-reply-to-private-parent h1 h2 h3 h4
    (successful-reply _ (post-is-new _ ip) _ _ _ _ pb _ _ _)
  = everyone≢followers-only
  ∘ trans (sym h4)
  ∘ trans (cong Post.visibility ∘ just-injective ∘ trans (sym h2) $ ip)
  ∘ new-reply-private
  ∘ trans (sym ∘ cong Post.visibility ∘ just-injective ∘ trans (sym h1) $ pb)
  $ h3

cant-delete-others-tweets : CantDeleteOthersTweets
cant-delete-others-tweets h1 h2 ne
    (delete-post vs pb _ au _ _ _ _ _ _) =
  ne (trans (trans (cong Post.author (just-injective (trans (sym h2) pb))) au)
             (active-injective (trans (sym (ValidSession.session-unchanged vs)) h1)))

cant-like-for-other-account : CantLikeForOtherAccount
cant-like-for-other-account {user = user} {other-user = other-user}
    vs u≢ou _ pb ∉before pa ∈after
    (like-post vs' _ pb' pa' _ _ _ _ _ _ _ inj _) =
  let
    eq-user  = active-injective
                ∘ trans (sym ∘ ValidSession.session-unchanged $ vs')
                ∘ ValidSession.session-unchanged $ vs
    u≢ou'    = u≢ou ∘ trans (sym eq-user)
    eq-post  = just-injective ∘ trans (sym pb') $ pb
    eq-post' = just-injective ∘ trans (sym pa') $ pa
    (eq∈ , eq∉) = inj {user' = other-user} u≢ou'
    ∉before' = subst ((other-user ∉_) ∘ Post.likes) (sym eq-post) ∉before
    ∈after'  = subst ((other-user ∈_) ∘ Post.likes) (sym eq-post') ∈after
  in eq∉ ∉before' ∈after'

failed-delete-does-nothing : FailedDeleteDoesNothing
failed-delete-does-nothing (delete-post _ _ _ _ _ _ _ _ _ _) h = ⊥-elim (h refl)
failed-delete-does-nothing (failed-access _) _ = refl
failed-delete-does-nothing (failed-delete-non-existant-post _ _) _ = refl
failed-delete-does-nothing (failed-delete-not-author _ _ _) _ = refl

failed-post-does-nothing : FailedPostDoesNothing
failed-post-does-nothing
    (successful-post _ _ _ _) h
  = ⊥-elim (h (_ , refl))
failed-post-does-nothing
    (successful-reply _ _ _ _ _ _ _ _ _ _) h
  = ⊥-elim (h (_ , refl))
failed-post-does-nothing (failed-access _) _ = refl
failed-post-does-nothing (failed-reply _ _) _ = refl

failed-like-does-nothing : FailedLikeDoesNothing
failed-like-does-nothing (like-post _ _ _ _ _ _ _ _ _ _ _ _ _) h
  = ⊥-elim (h refl)
failed-like-does-nothing (failed-like-post _ _) _ = refl
failed-like-does-nothing (failed-access _) _ = refl

failed-unlike-does-nothing : FailedUnlikeDoesNothing
failed-unlike-does-nothing (unlike-post _ _ _ _ _ _ _ _ _ _ _ _ _) h
  = ⊥-elim (h refl)
failed-unlike-does-nothing (failed-unlike-post _ _) _ = refl
failed-unlike-does-nothing (failed-access _) _ = refl

failed-follow-does-nothing : FailedFollowDoesNothing
failed-follow-does-nothing (follow-user _ _ _ _ _ _) h
  = ⊥-elim (h refl)
failed-follow-does-nothing (failed-access _) _ = refl

failed-unfollow-does-nothing : FailedUnfollowDoesNothing
failed-unfollow-does-nothing (unfollow-user _ _ _ _ _ _) h
  = ⊥-elim (h refl)
failed-unfollow-does-nothing (failed-access _) _ = refl

failed-register-does-nothing : FailedRegisterDoesNothing
failed-register-does-nothing (failed-access _) _ = refl
failed-register-does-nothing (create-account _ _ _) h
  = ⊥-elim (h refl)
failed-register-does-nothing (failed-create-account _) _ = refl

failed-login-does-nothing : FailedLoginDoesNothing
failed-login-does-nothing (failed-access _) _ = refl
failed-login-does-nothing (login _ _ _ _ _ _) h
  = ⊥-elim (h (_ , refl))
failed-login-does-nothing (failed-login-1 _) _ = refl
failed-login-does-nothing (failed-login-2 _ _) _ = refl

reply-exists :
  ∀ {w : World} {sid user txt acc pa pt pv ps pl pr pp₁ parent} →
  (crp : CanReadPost w sid parent) →
  (pb : World.post-at w parent ≡ just (post pa pt pv ps pl pr pp₁)) →
  (st : Post.status (post pa pt pv ps pl pr pp₁) ≡ live) →
  (vs : ValidSession w sid acc user) →
  ∃[ after ] ∃[ result ] Step w (publish sid txt (just parent)) after result
reply-exists {w} {sid} {user} {txt} {acc} {pa} {pt} {pv} {ps} {pl} {pr} {pp₁} {parent}
             crp pb st vs =
  let (_ , pid) , not-used-before , _ , _ = new-pid (World.used-post-ids w)
      p = new-reply user txt acc parent (post pa pt pv ps pl pr pp₁)
      absent = snd (World.only-used-pids w) not-used-before
      after , pin = make-new-reply {pid = pid} {parent} w user txt acc
                      (post pa pt pv ps pl pr pp₁) pb not-used-before
      pid≢parent : pid ≢ parent
      pid≢parent e =
        nothing≢just
          (trans (sym absent)
                 (subst (λ z → World.post-at w z ≡ just (post pa pt pv ps pl pr pp₁))
                        (sym e) pb))
      rt-eq : reply-to (post pa pt pv ps pl pr pp₁) pid ≡
                post pa pt pv live pl (pid ∷ pr) pp₁
      rt-eq = trans refl (post-status-live st)
  in after , created-post pid ,
     successful-reply {before = w} {after = after} {sid = sid} {txt = txt}
       vs pin refl crp (post-status-live st) refl pb
       (trans (add-post-same {f = add-post (World.post-at w) pid p} {k = parent}
           {v = reply-to (post pa pt pv ps pl pr pp₁) pid})
         (cong just rt-eq))
       pid≢parent
       (λ {o} {u1} {u2} {s} ne₁ ne₂ →
         sym (trans (add-post-no {f = add-post (World.post-at w) pid p} {k = parent}
                     {v = reply-to (post pa pt pv ps pl pr pp₁) pid} ne₂)
              (add-post-no {f = World.post-at w} {k = pid} {v = p} ne₁)) ,
          refl , refl , refl)

publish-exists :
  ∀ {sid txt mparent} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (publish sid txt mparent) after result
publish-exists {sid} {txt} {mparent} w
  with can-have-valid-session w sid
... | no ¬vs =
      w , expired , expired-access refl ¬vs
... | yes (acc , user , vs) with mparent
... | nothing =
      let (_ , pid) , not-used-before , _ , _ = new-pid (World.used-post-ids w)
          after , pin = make-new-post {pid = pid} w user txt acc not-used-before
      in after , created-post pid ,
         successful-post {before = w} {after = after} {sid = sid} {txt = txt}
           {username = user} {user = acc} {pid = pid} {acc = acc}
           vs pin refl
           (λ {o} {u1} {u2} {s} ne →
             sym (add-post-no ne) , refl , refl , refl)
... | just parent
  with can-read-post w sid parent
... | no ¬crp = w , denied , failed-reply vs ¬crp
... | yes crp@(post-is-private
          {post = post pa pt pv ps pl pr pp₁} _ pb vis st _) =
      reply-exists crp pb st vs
... | yes crp@(post-is-public
          {post = post pa pt pv ps pl pr pp₁} _ pb _ st) =
      reply-exists crp pb st vs

delete-exists :
  ∀ {sid pid} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (delete sid pid) after result
delete-exists {sid} {pid} w with can-have-valid-session w sid
... | no ¬vs =
    w , expired , expired-access refl ¬vs
... | yes vs∃ = delete-valid (World.post-at w pid) refl vs∃

read-post-exists :
  ∀ {msid pid} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (read-post msid pid) after result
read-post-exists {nothing} {pid} w with is-post-public w pid
... | yes (p , eq , vis , st) = w , _ , read-post-anonymously eq vis st
... | no ¬pub = w , expired , failed-access λ {eq → ⊥-elim (nothing≢just eq)}
read-post-exists {just sid} {pid} w with can-have-valid-session w sid
... | no ¬vs =
    w , expired , expired-access refl ¬vs
... | yes vs∃ = read-post-valid (World.post-at w pid) refl vs∃

like-valid :
  ∀ {w : World} {sid : SessionId} {pid : PostId} →
  (pp : Maybe Post) →
  World.post-at w pid ≡ pp →
  (∃[ acc ] ∃[ user ] ValidSession w sid acc user) →
  ∃[ after ] ∃[ result ] Step w (like sid pid) after result
like-valid
  {w@(world account-at session-at post-at follows newest-first
           used-post-ids used-session-ids only-used-pids only-used-sids
           only-valid-sessions only-valid-posts only-valid-replies
           no-duplicate-replies no-duplicate-likes no-duplicate-posts)}
  {sid} {pid} pp pp≡ (acc , user , vs) with pp | can-read-post w sid pid
... | nothing | yes (post-is-public vs₁ eq₁ _ _) =
    ⊥-elim (nothing≢just (trans (sym pp≡) eq₁))
... | nothing | yes (post-is-private vs₁ eq₁ _ _ _) =
    ⊥-elim (nothing≢just (trans (sym pp≡) eq₁))
... | nothing | no ¬cp = w , denied , failed-like-post vs ¬cp
... | just (post pa pt pv ps pl pr pp₁) | no ¬cp = w , denied , failed-like-post vs ¬cp
... | just (post pa pt pv ps pl pr pp₁) | yes cp with ∈-decidable user pl
...   | yes user∈ =
        w , _ , like-post vs cp pp≡ pp≡ user∈
                refl refl refl refl refl refl
                (λ {user′} ne → (λ m∈ → m∈) , (λ m∉ → m∉))
                (λ {other-pids} ne → refl , refl , refl , refl , refl)
...   | no user∉ =
        let p′ : Post
            p′ = post pa pt pv ps (user ∷ pl) pr pp₁

            after : World
            after = post-at-step {w} {pid} (post pa pt pv ps pl pr pp₁) p′ pp≡ refl refl
                  (uniq-cons user pl user∉ (no-duplicate-likes pp≡))
        in after , success , like-post vs cp pp≡ (add-post-same {v = p′}) here
                refl refl refl refl refl refl
                (λ {user′} ne → (λ m∈ → there m∈) , ∉-prepend (λ eq → ne (sym eq)))
                (λ {other-pids} ne → refl , refl , sym (add-post-no ne) , refl , refl)

like-exists :
  ∀ {sid pid} →
  (before : World) →
  ∃[ after ] ∃[ result ] Step before (like sid pid) after result
like-exists {sid} {pid} w with can-have-valid-session w sid
... | no ¬vs =
        w , expired , expired-access refl ¬vs
... | yes vs∃ = like-valid (World.post-at w pid) refl vs∃

unlike-exists :
  ∀ {sid pid} →
  (before : World) →
  ∃[ after ] ∃[ result ] Step before (unlike sid pid) after result
unlike-exists {sid} {pid} w with can-have-valid-session w sid
... | no ¬vs =
        w , expired , expired-access refl ¬vs
... | yes vs∃ = unlike-valid (World.post-at w pid) refl vs∃

read-personal-timeline-exists :
  ∀ {sid n} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (read-personal-timeline sid n) after result
read-personal-timeline-exists {sid} {n} w with can-have-valid-session w sid
... | no ¬vs =
    w , expired , expired-access refl ¬vs
... | yes (_ , user , vs) = w , _ , get-personal-timeline vs

read-global-timeline-exists :
  ∀ {msid n} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (read-global-timeline msid n) after result
read-global-timeline-exists {nothing} {n} w = w , _ , get-public-global-timeline
read-global-timeline-exists {just sid} {n} w with can-have-valid-session w sid
... | no ¬vs =
    w , expired , expired-access refl ¬vs
... | yes (_ , user , vs) = w , _ , get-private-global-timeline vs

authenticate-exists :
  ∀ {username passwd} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (authenticate username passwd) after result
authenticate-exists {username} {passwd}
  w@(world account-at session-at post-at follows newest-first
           used-post-ids used-session-ids only-used-pids only-used-sids
           only-valid-sessions only-valid-posts only-valid-replies
           no-duplicate-replies no-duplicate-likes no-duplicate-posts)
  with account-at username in acnt
... | nothing = w , login-failed , failed-login-1 acnt
... | just user with Account.password user ≟ passwd
... | no p≢passwd = w , login-failed , failed-login-2 acnt p≢passwd
... | yes refl =
    let (used-session-ids′ , sid) , sid∉ , sid∈ , _ = new-sid used-session-ids
        after : World
        after = world account-at
                      (add-session-at session-at sid (active username))
                      post-at
                      follows
                      newest-first
                      used-post-ids
                      (sid ∷ used-session-ids)
                      only-used-pids
                      (add-session-used (active username) active≢unused sid∉
                        only-used-sids)
                      (add-session-valid-add {username = username}
                        (snd only-used-sids sid∉) acnt
                        only-valid-sessions)
                      only-valid-posts
                      only-valid-replies
                      no-duplicate-replies
                      no-duplicate-likes
                      no-duplicate-posts
    in after , issued-session sid , login
         (snd only-used-sids sid∉) (add-session-same {f = session-at} {k = sid}
           {v = active username}) acnt refl
         (λ {other-sid} {pid} {u1} {u2} ne →
           sym (add-session-no {f = session-at} {k = sid} {v = active username} ne)
             , refl , refl , refl , refl)
         (valid-session {world = after} {sid = sid} {acc = user} {user = username}
                        add-session-same acnt)
revoke-token-exists :
  ∀ {sid} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (revoke-token sid) after result
revoke-token-exists {sid}
  w@(world account-at session-at post-at follows newest-first
           used-post-ids used-session-ids only-used-pids only-used-sids
           only-valid-sessions only-valid-posts only-valid-replies
           no-duplicate-replies no-duplicate-likes no-duplicate-posts)
  with can-have-valid-session w sid
... | no ¬vs =
    w , expired , expired-access refl ¬vs
... | yes (acc , user , vs) =
    let after : World
        after = world account-at
                      (add-session-at session-at sid revoked)
                      post-at
                      follows
                      newest-first
                      used-post-ids
                      used-session-ids
                      only-used-pids
                      (add-session-used-keep revoked
                        (ValidSession.session-unchanged vs) active≢unused revoked≢unused
                        only-used-sids)
                      (add-session-valid-revoke only-valid-sessions)
                      only-valid-posts
                      only-valid-replies
                      no-duplicate-replies
                      no-duplicate-likes
                      no-duplicate-posts
    in after , success , logout (ValidSession.session-unchanged vs)
         (add-session-same {f = session-at} {k = sid} {v = revoked})
       (λ {other-sid} ne →
          sym (add-session-no {f = session-at} {k = sid} {v = revoked} ne)
            , refl , refl , refl , refl)

register-exists :
  ∀ {username passwd} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (register username passwd) after result
register-exists {username} {passwd}
  w@(world account-at session-at post-at follows newest-first
           used-post-ids used-session-ids only-used-pids only-used-sids
           only-valid-sessions only-valid-posts only-valid-replies
           no-duplicate-replies no-duplicate-likes no-duplicate-posts)
  with World.account-at w username in acnt
... | nothing =
    after , success , create-account acnt
      (add-account-same {f = account-at} {k = username}
      {v = account passwd everyone})
      (λ {sid} {pid} {u1} {u2} ne₁ ne₂ →
        sym (add-account-no ne₁) , refl , refl , refl , refl)
  where
    after : World
    after = world (add-account-at account-at username (account passwd everyone))
                  session-at
                  post-at
                  follows
                  newest-first
                  used-post-ids
                  used-session-ids
                  only-used-pids
                  only-used-sids
                  (add-account-valid {session-at = session-at} {acc-at = account-at}
                                     {username = username} (account passwd everyone) acnt
                                     only-valid-sessions)
                  only-valid-posts
                  only-valid-replies
                  no-duplicate-replies
                  no-duplicate-likes
                  no-duplicate-posts
... | just (account passwd₁ vis₁) =
    w , signup-failed , failed-create-account λ {ne → nothing≢just (trans (sym ne) acnt)}

follow-exists :
  ∀ {sid followee} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (follow sid followee) after result
follow-exists {sid} {followee}
  w@(world account-at session-at post-at follows newest-first
           used-post-ids used-session-ids only-used-pids only-used-sids
           only-valid-sessions only-valid-posts only-valid-replies
           no-duplicate-replies no-duplicate-likes no-duplicate-posts)
  with can-have-valid-session w sid
... | no ¬vs =
    w , expired , expired-access refl ¬vs
... | yes (acc , user , vs) =
    let after : World
        after = world account-at
                      session-at
                      post-at
                      (add-follower follows user followee)
                      newest-first
                      used-post-ids
                      used-session-ids
                      only-used-pids
                      only-used-sids
                      only-valid-sessions
                      only-valid-posts
                      only-valid-replies
                      no-duplicate-replies
                      no-duplicate-likes
                      no-duplicate-posts
    in after , success , follow-user vs refl refl refl refl refl

unfollow-exists :
  ∀ {sid followee} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (unfollow sid followee) after result
unfollow-exists {sid} {followee}
  w@(world account-at session-at post-at follows newest-first
           used-post-ids used-session-ids only-used-pids only-used-sids
           only-valid-sessions only-valid-posts only-valid-replies
           no-duplicate-replies no-duplicate-likes no-duplicate-posts)
  with can-have-valid-session w sid
... | no ¬vs =
    w , expired , expired-access refl ¬vs
... | yes (acc , user , vs) =
    let after : World
        after = world account-at
                      session-at
                      post-at
                      (remove-follower follows user followee)
                      newest-first
                      used-post-ids
                      used-session-ids
                      only-used-pids
                      only-used-sids
                      only-valid-sessions
                      only-valid-posts
                      only-valid-replies
                      no-duplicate-replies
                      no-duplicate-likes
                      no-duplicate-posts
    in after , success , unfollow-user vs refl refl refl refl refl

time-passes-exists :
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before time-passes after result
time-passes-exists
  w@(world account-at session-at post-at follows newest-first
           used-post-ids used-session-ids only-used-pids only-used-sids
           only-valid-sessions only-valid-posts only-valid-replies
           no-duplicate-replies no-duplicate-likes no-duplicate-posts) =
  after , success , session-timeout (revoke-all-active {s = session-at})
    (λ {sid} eq₁ eq₂ eq₃ eq₄ → refl)
  where
    after : World
    after = world account-at
                  (revoke-all session-at)
                  post-at
                  follows
                  newest-first
                  used-post-ids
                  used-session-ids
                  only-used-pids
                  (revoke-all-used only-used-sids)
                  (revoke-all-valid {s = session-at} only-valid-sessions)
                  only-valid-posts
                  only-valid-replies
                  no-duplicate-replies
                  no-duplicate-likes
                  no-duplicate-posts

step-exists : StepExists
step-exists w (publish _ _ _)              = publish-exists w
step-exists w (delete _ _)                 = delete-exists w
step-exists w (read-post _ _)              = read-post-exists w
step-exists w (read-personal-timeline _ _) = read-personal-timeline-exists w
step-exists w (read-global-timeline _ _)   = read-global-timeline-exists w
step-exists w (authenticate _ _)           = authenticate-exists w
step-exists w (revoke-token _)             = revoke-token-exists w
step-exists w (register _ _)               = register-exists w
step-exists w (follow _ _)                 = follow-exists w
step-exists w (unfollow _ _)               = unfollow-exists w
step-exists w (like _ _)                   = like-exists w
step-exists w (unlike _ _)                 = unlike-exists w
step-exists w time-passes                  = time-passes-exists w
