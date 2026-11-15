open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Data.Empty                            using (⊥-elim)
open import Data.List                             using (take; filter; filterᵇ)
open import Data.Product                          using (∃-syntax)
open import Data.String                           using (_≟_)
open import Data.Unit                             using (tt)
open import Function                              using (_∘_; _$_)
open import Relation.Binary.Definitions           using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
                                                         sym; trans; subst)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Relation.Nullary.Negation.Core        using (¬_)

open import Helpers

module Proofs
  (SessionId PostId : Set)
  (new-sid : CreateNew SessionId)
  (new-pid : CreateNew PostId)
  (_≟ₚ_ : DecidableEquality PostId)
  (_≟ₛᵢ_ : DecidableEquality SessionId)
  where
open import Twitter SessionId PostId new-sid new-pid _≟ₚ_ _≟ₛᵢ_

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

nothing≢just : {x : a} → nothing ≢ just x
nothing≢just ()

deleted≢live : deleted ≢ live
deleted≢live ()

everyone≢followers-only : everyone ≢ followers-only
everyone≢followers-only ()

new-reply-private :
  ∀ {username txt user parent-id ppost} →
  Post.visibility ppost ≡ followers-only →
  Post.visibility (new-reply username txt user parent-id ppost) ≡ followers-only
new-reply-private {ppost = record { visibility = everyone }} ()
new-reply-private {ppost = record { visibility = followers-only }} refl = refl

update-vs : ∀{w s s₁ a u} → ValidSession w s₁ a u → s ≡ s₁ → ValidSession w s a u
update-vs vs refl = vs

add-post : (PostId → Maybe Post) → PostId → Post → PostId → Maybe Post
add-post f pid p pid' with pid ≟ₚ pid'
... | yes _ = just p
... | no _  = f pid'

add-post-same : ∀ {f : PostId → Maybe Post} {pid : PostId} {p : Post} →
  add-post f pid p pid ≡ just p
add-post-same {pid = pid} with pid ≟ₚ pid
... | yes _  = refl
... | no neq = ⊥-elim (neq refl)

add-post-at : ∀ {f : PostId → Maybe Post} {pid : PostId} {p : Post} {x : PostId} →
  pid ≡ x → add-post f pid p x ≡ just p
add-post-at {f = f} {pid = pid} {p = p} {x = x} eq =
  subst (λ z → add-post f pid p z ≡ just p) eq add-post-same

add-post-no : ∀ {f : PostId → Maybe Post} {pid : PostId} {p : Post} {x : PostId} →
  pid ≢ x → add-post f pid p x ≡ f x
add-post-no {pid = pid} {x = x} ne with pid ≟ₚ x
... | yes eq = ⊥-elim (ne eq)
... | no _   = refl

Dec-elim : ∀ {a b} {A : Set a} {B : Set b} →
  Dec A → (A → B) → (¬ A → B) → B
Dec-elim (yes p) f g = f p
Dec-elim (no ¬p) f g = g ¬p

add-post-inj : ∀ {f : PostId → Maybe Post} {pid x : PostId} {p post' : Post} →
  add-post f pid p x ≡ just post' → pid ≡ x → post' ≡ p
add-post-inj {pid = pid} {x = x} eq refl = just-injective (trans (sym eq) add-post-same)

∉-distinct : ∀ {xs : List PostId} {f : PostId → Maybe Post} {pid : PostId} →
  f pid ≡ nothing →
  (∀ {z} → z ∈ xs → ∃[ post ] f z ≡ just post) →
  ∀ {pid'} → pid' ∈ xs → pid ≢ pid'
∉-distinct {f = f} {pid = pid} absent F m e =
  let post' , eq = F m
  in nothing≢just (trans (sym absent) (subst (λ z → f z ≡ just post') (sym e) eq))

∉-witnessed : ∀ {xs : List PostId} {f : PostId → Maybe Post} {pid : PostId} →
  f pid ≡ nothing →
  (∀ {z} → z ∈ xs → ∃[ post ] f z ≡ just post) →
  pid ∉ xs
∉-witnessed absent F m = ∉-distinct absent F m refl

add-post-used : ∀ {xs : List PostId} {f : PostId → Maybe Post} {pid : PostId} {p : Post} →
  pid ∉ xs →
  (∀ {z} → (z ∈ xs → f z ≢ nothing)
           ∧ (z ∉ xs → f z ≡ nothing)) →
  ∀ {pid'} →
  (pid' ∈ pid ∷ xs → add-post f pid p pid' ≢ nothing) ∧
  (pid' ∉ pid ∷ xs → add-post f pid p pid' ≡ nothing)
add-post-used {xs = xs} {f = f} {pid = pid} {p = p} ∉w fs {pid'} = F′ , S′
  where
    ne-tail : pid' ∈ xs → pid ≢ pid'
    ne-tail m e = ∉w (∈-sym e m)

    F′ : pid' ∈ pid ∷ xs → add-post f pid p pid' ≢ nothing
    F′ here      = λ eq → nothing≢just (trans (sym eq) add-post-same)
    F′ (there m) = λ eq → fst (fs {pid'}) m (trans (sym (add-post-no (ne-tail m))) eq)

    S′ : pid' ∉ pid ∷ xs → add-post f pid p pid' ≡ nothing
    S′ nm = trans (add-post-no (∉-head nm ∘ sym)) (snd (fs {pid'}) (∉-tail nm))

add-post-posts : ∀ {xs : List PostId} {f : PostId → Maybe Post} {pid : PostId} {p : Post} →
  (∀ {z} → z ∈ xs → ∃[ post ] f z ≡ just post) →
  (∀ {pid'} → pid' ∈ xs → pid ≢ pid') →
  ∀ {pid'} → pid' ∈ pid ∷ xs → ∃[ post ] add-post f pid p pid' ≡ just post
add-post-posts {pid = pid} {p = p} F N here = p , add-post-same
add-post-posts {pid = pid} F N {pid'} (there m) =
  let post' , eq = F m
  in post' , trans (add-post-no (N m)) eq

add-post-prop : ∀ {ℓ} {f : PostId → Maybe Post} {pid : PostId} (p : Post) {P : Post → Set ℓ} →
  P p →
  (∀ {z post'} → f z ≡ just post' → P post') →
  ∀ {pid'} {post' : Post} → add-post f pid p pid' ≡ just post' → P post'
add-post-prop {f = f} {pid = pid} p {P = P} Pp Fold {pid'} {post'} eq =
  Dec-elim (pid ≟ₚ pid')
    (λ e → subst (λ pp → P pp)
      (just-injective (trans (sym (add-post-at e)) eq)) Pp)
    (λ ne → Fold (trans (sym (add-post-no ne)) eq))

add-post-replies : ∀ {f : PostId → Maybe Post} {pid : PostId} {p : Post} →
  f pid ≡ nothing →
  Post.replies p ≡ [] →
  (∀ {ppid ppost cpid} → cpid ∈ Post.replies ppost → f ppid ≡ just ppost →
    ∃[ cpost ] f cpid ≡ just cpost ∧ Post.parent cpost ≡ just ppid
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
      in ⊥-elim (∈[] child-pid
        (subst (λ rs → child-pid ∈ rs) re-empty
          (subst (λ pp → child-pid ∈ Post.replies pp) parent-post≡p child∈))))
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
reply-to post' pid' =
  post (Post.author post') (Post.text post') (Post.visibility post')
       (Post.status post') (Post.likes post') (pid' ∷ Post.replies post')
       (Post.parent post')

parent-of-reply-to : ∀ {q : Post} {i : PostId} → Post.parent (reply-to q i) ≡ Post.parent q
parent-of-reply-to = refl

replies-of-reply-to : ∀ {q : Post} {i : PostId} → Post.replies (reply-to q i) ≡ i ∷ Post.replies q
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

∈-not-head : ∀ {x y : PostId} {xs : List PostId} → x ≢ y → x ∈ y ∷ xs → x ∈ xs
∈-not-head ne here = ⊥-elim (ne refl)
∈-not-head ne (there m) = m

post-status-live :
  ∀ {a t v s l r pa'} → s ≡ live → post a t v s l r pa' ≡ post a t v live l r pa'
post-status-live {s = s} refl = refl

add-post-witness :
  ∀ {xs : List PostId} {f : PostId → Maybe Post} {pid ppid : PostId} (pnew preply : Post) →
  (∀ {z} → z ∈ xs → ∃[ post ] add-post f pid pnew z ≡ just post) →
  ∀ {z} → z ∈ xs → ∃[ post ] add-post (add-post f pid pnew) ppid preply z ≡ just post
add-post-witness {xs} {f} {pid} {ppid} pnew preply F {z} m =
  Dec-elim (ppid ≟ₚ z)
    (λ e → preply , add-post-at e)
    (λ ne → let post' , eq = F m in post' , trans (add-post-no ne) eq)

add-post-used-keep :
  ∀ {us : List PostId} {f : PostId → Maybe Post} {ppid : PostId} {ppost : Post} (ppost' : Post) →
  f ppid ≡ just ppost →
  (∀ {z} → (z ∈ us → f z ≢ nothing) ∧ (z ∉ us → f z ≡ nothing)) →
  ∀ {pid'} →
  (pid' ∈ us → add-post f ppid ppost' pid' ≢ nothing) ∧
  (pid' ∉ us → add-post f ppid ppost' pid' ≡ nothing)
add-post-used-keep {us} {f} {ppid} {ppost} ppost' fppid fs {pid'} = F′ , S′
  where
    ne : pid' ∉ us → ppid ≢ pid'
    ne nm e =
      nothing≢just
        (trans (sym (snd (fs {ppid}) (subst (λ z → z ∉ us) (sym e) nm))) fppid)

    F′ : pid' ∈ us → add-post f ppid ppost' pid' ≢ nothing
    F′ m = Dec-elim (ppid ≟ₚ pid')
      (λ e → λ eq → nothing≢just (trans (sym eq) (add-post-at e)))
      (λ n₁ → λ eq → fst (fs {pid'}) m (trans (sym (add-post-no n₁)) eq))

    S′ : pid' ∉ us → add-post f ppid ppost' pid' ≡ nothing
    S′ nm = trans (add-post-no (ne nm)) (snd (fs {pid'}) nm)

add-post-prop² :
  ∀ {ℓ} {f : PostId → Maybe Post} {pid ppid : PostId} (pnew preply : Post) {P : Post → Set ℓ} →
  P pnew → P preply → (∀ {z post'} → f z ≡ just post' → P post') →
  ∀ {z post'} → add-post (add-post f pid pnew) ppid preply z ≡ just post' → P post'
add-post-prop² {f = f} {pid = pid} {ppid = ppid} pnew preply {P = P} Ppnew Ppreply Fold {z} {post'} eq =
  Dec-elim (ppid ≟ₚ z)
    (λ e → subst (λ pp → P pp)
      (just-injective (trans (sym (add-post-at e)) eq)) Ppreply)
    (λ ne → add-post-prop pnew Ppnew Fold {z} {post'} (trans (sym (add-post-no ne)) eq))

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
      let peq′ = trans (sym (add-post-at {f = f} {pid = ppid} {p = reply-to ppost pid}
                                           {parent-pid} e)) peq
          m′ = subst (λ pp → child-pid ∈ Post.replies pp) (sym (just-injective peq′)) child∈
      in Dec-elim (child-pid ≟ₚ pid)
        (λ e2 →
          p ,
          trans (add-post-no (λ ne → pid≢ppid (trans (sym e2) (sym ne))))
                (subst (λ z → f z ≡ just p) (sym e2) fp) ,
          trans prnt (cong just e) ,
          λ ne → pid≢ppid (trans (sym e2) (trans ne (sym e))))
        (λ ne2 →
          let cpost , ceq , cpar , cne = Fold (∈-not-head ne2 m′) fppid
          in cpost , trans (add-post-no (λ eₙ → cne (sym eₙ))) ceq , trans cpar (cong just e) ,
             λ ne → cne (trans ne (sym e))))
    (λ ne →
      let w-eq = trans (sym (add-post-no {f = f} {pid = ppid} {p = reply-to ppost pid}
                                          {parent-pid} ne)) peq
      in Dec-elim (child-pid ≟ₚ ppid)
        (λ e2 →
          let cpost , ceq , cpar , cne = Fold child∈ w-eq
              cpost≡ppost =
                just-injective
                  (trans (sym (subst (λ z → f z ≡ just cpost) e2 ceq)) fppid)
          in reply-to ppost pid ,
             add-post-at {f = f} {pid = ppid} {p = reply-to ppost pid} {child-pid} (sym e2) ,
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
                     (add-post-same {f = post-at} {pid = pid} {p = p})
                     (new-reply-parent {username = user} {txt = txt} {user = acc}
                                       {parent-id = ppid} {ppost = ppost})
                     F₁-replies)
                   (add-post-prop² p (reply-to ppost pid) uniq-of-new-reply uniq-of-reply-to no-duplicate-replies)
                   (add-post-prop² p (reply-to ppost pid) uniq-of-new-likes (no-duplicate-likes pb) no-duplicate-likes)
                   (uniq-cons pid newest-first pid∉newest no-duplicate-posts)

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
    eq-user  = active-injective ∘ trans (sym ∘ ValidSession.session-unchanged $ vs') ∘ ValidSession.session-unchanged $ vs
    u≢ou'    = u≢ou ∘ trans (sym eq-user)
    eq-post  = just-injective ∘ trans (sym pb') $ pb
    eq-post' = just-injective ∘ trans (sym pa') $ pa
    (eq∈ , eq∉) = inj {user' = other-user} u≢ou'
    ∉before' = subst ((other-user ∉_) ∘ Post.likes) (sym eq-post) ∉before
    ∈after'  = subst ((other-user ∈_) ∘ Post.likes) (sym eq-post') ∈after
  in subst id eq∉ ∉before' ∈after'

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

publish-exists :
  ∀ {sid txt mparent} →
  (before : World) →
  ∃[ after ] ∃[ result ]
  Step before (publish sid txt mparent) after result
publish-exists {sid} {txt} {mparent} w
  with can-have-valid-session w sid
... | no ¬vs =
      w , expired , failed-access (λ { msid-eq (acc , username , vs) →
                                    ¬vs (acc , username , update-vs vs (just-injective msid-eq))
                                  })
... | yes (acc , user , vs) with mparent
... | nothing =
      let (used-post-ids , pid) , not-used-before , used-now , all-kept = new-pid (World.used-post-ids w)
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
                {post = post pa pt pv ps pl pr pp₁} _ pb vis st fl) =
      let (used-post-ids , pid) , not-used-before , used-now , all-kept = new-pid (World.used-post-ids w)
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
           (trans (add-post-same {f = add-post (World.post-at w) pid p} {pid = parent}
                               {p = reply-to (post pa pt pv ps pl pr pp₁) pid})
                 (cong just rt-eq))
           pid≢parent
           (λ {o} {u1} {u2} {s} ne₁ ne₂ →
             sym (trans (add-post-no {f = add-post (World.post-at w) pid p} {pid = parent}
                                  {p = reply-to (post pa pt pv ps pl pr pp₁) pid} ne₂)
                         (add-post-no {f = World.post-at w} {pid = pid} {p = p} ne₁)) ,
                  refl , refl , refl)
... | yes crp@(post-is-public
                {post = post pa pt pv ps pl pr pp₁} _ pb vis st) =
      let (used-post-ids , pid) , not-used-before , used-now , all-kept = new-pid (World.used-post-ids w)
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
           (trans (add-post-same {f = add-post (World.post-at w) pid p} {pid = parent}
                               {p = reply-to (post pa pt pv ps pl pr pp₁) pid})
                 (cong just rt-eq))
           pid≢parent
           (λ {o} {u1} {u2} {s} ne₁ ne₂ →
             sym (trans (add-post-no {f = add-post (World.post-at w) pid p} {pid = parent}
                                  {p = reply-to (post pa pt pv ps pl pr pp₁) pid} ne₂)
                         (add-post-no {f = World.post-at w} {pid = pid} {p = p} ne₁)) ,
                  refl , refl , refl)

-- step-exists : StepExists
-- step-exists w (publish _ _ _) = publish-exists w
-- step-exists w _ = {!!}
