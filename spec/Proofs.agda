module Proofs (SessionId PostId : Set) where

open import Twitter SessionId PostId

open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Data.Empty                            using (⊥-elim)
open import Data.Product                          using (∃-syntax)
open import Function                              using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
                                                         sym; trans; subst)
open import Relation.Nullary.Negation.Core        using (¬_)

--------------------------------------------------------------------------------
--                               PROOF-HELPERS                                --
--------------------------------------------------------------------------------

private variable a b : Set

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
  ∀ (before : World) (cmd : Command) →
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

active-inj : {x y : String} → active x ≡ active y → x ≡ y
active-inj refl = refl

id : Set → Set
id x = x

--------------------------------------------------------------------------------
--                                   PROOFS                                   --
--------------------------------------------------------------------------------

post-doesnt-exist-before-posting : PostDoesntExistBeforePosting
post-doesnt-exist-before-posting {before}
    (successful-post _ (post-is-new wa _) _ _ _ _ _ _) =
  nothing≢just ∘ trans (sym wa) ∘ snd ∘ World.only-valid-posts before , wa
post-doesnt-exist-before-posting {before}
    (successful-reply _ (post-is-new wa _) _ _ _ _ _ _ _ _ _ _ _ _ _) =
  nothing≢just ∘ trans (sym wa) ∘ snd ∘ World.only-valid-posts before , wa

cant-reply-to-deleted-tweet : CantReplyToDeletedTweet
cant-reply-to-deleted-tweet pa st
    (successful-reply _ _ _ _ pe _ pb _ _ _ _ _ _ _ _)
  = deleted≢live
  ∘ trans (sym st)
  ∘ trans (cong Post.status ∘ just-injective ∘ trans (sym pa) $ pb)
  ∘ cong Post.status
  $ pe

cant-reply-to-tweet-you-cant-read : CantReplyToTweetYouCantRead
cant-reply-to-tweet-you-cant-read ¬cr
    (successful-reply _ _ _ cr _ _ _ _ _ _ _ _ _ _ _) = ¬cr cr

cant-make-public-reply-to-private-parent : CantMakePublicReplyToPrivateParent
cant-make-public-reply-to-private-parent h1 h2 h3 h4
    (successful-reply _ (post-is-new _ ip) _ _ _ _ pb _ _ _ _ _ _ _ _)
  = everyone≢followers-only
  ∘ trans (sym h4)
  ∘ trans (cong Post.visibility ∘ just-injective ∘ trans (sym h2) $ ip)
  ∘ new-reply-private
  ∘ trans (sym ∘ cong Post.visibility ∘ just-injective ∘ trans (sym h1) $ pb)
  $ h3

cant-delete-others-tweets : CantDeleteOthersTweets
cant-delete-others-tweets h1 h2 ne
    (delete-post vs pb _ au _ _ _ _ _ _ _ _ _ _) =
  ne (trans (trans (cong Post.author (just-injective (trans (sym h2) pb))) au)
             (active-inj (trans (sym (ValidSession.session-unchanged vs)) h1)))

cant-like-for-other-account : CantLikeForOtherAccount
cant-like-for-other-account {user = user} {other-user = other-user}
    vs u≢ou _ pb ∉before pa ∈after
    (like-post vs' _ pb' pa' _ _ _ _ _ _ _ inj _ _ _ _ _ _) =
  let
    eq-user  = active-inj ∘ trans (sym ∘ ValidSession.session-unchanged $ vs') ∘ ValidSession.session-unchanged $ vs
    u≢ou'    = u≢ou ∘ trans (sym eq-user)
    eq-post  = just-injective ∘ trans (sym pb') $ pb
    eq-post' = just-injective ∘ trans (sym pa') $ pa
    (eq∈ , eq∉) = inj {user' = other-user} u≢ou'
    ∉before' = subst ((other-user ∉_) ∘ Post.likes) (sym eq-post) ∉before
    ∈after'  = subst ((other-user ∈_) ∘ Post.likes) (sym eq-post') ∈after
  in subst id eq∉ ∉before' ∈after'

failed-delete-does-nothing : FailedDeleteDoesNothing
failed-delete-does-nothing (delete-post _ _ _ _ _ _ _ _ _ _ _ _ _ _) h = ⊥-elim (h refl)
failed-delete-does-nothing (failed-access _) _ = refl
failed-delete-does-nothing (failed-delete-non-existant-post _ _) _ = refl
failed-delete-does-nothing (failed-delete-not-author _ _ _) _ = refl

failed-post-does-nothing : FailedPostDoesNothing
failed-post-does-nothing
    (successful-post _ _ _ _ _ _ _ _) h
  = ⊥-elim (h (_ , refl))
failed-post-does-nothing
    (successful-reply _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) h
  = ⊥-elim (h (_ , refl))
failed-post-does-nothing (failed-access _) _ = refl

failed-like-does-nothing : FailedLikeDoesNothing
failed-like-does-nothing (like-post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) h
  = ⊥-elim (h refl)
failed-like-does-nothing (failed-like-post _ _) _ = refl
failed-like-does-nothing (failed-access _) _ = refl

failed-unlike-does-nothing : FailedUnlikeDoesNothing
failed-unlike-does-nothing (unlike-post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) h
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
failed-register-does-nothing (create-account _ _ _ _ _ _ _ _ _) h
  = ⊥-elim (h refl)
failed-register-does-nothing (failed-create-account _) _ = refl

failed-login-does-nothing : FailedLoginDoesNothing
failed-login-does-nothing (failed-access _) _ = refl
failed-login-does-nothing (login _ _ _ _ _ _ _ _ _ _ _) h
  = ⊥-elim (h (_ , refl))
failed-login-does-nothing (failed-login-1 _) _ = refl
failed-login-does-nothing (failed-login-2 _ _) _ = refl

step-exists : StepExists
step-exists = {!!}
