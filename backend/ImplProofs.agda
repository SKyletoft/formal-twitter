open import Agda.Builtin.Maybe
open import Data.Empty                                using (⊥; ⊥-elim)
open import Data.List                                 using (length; take; filter; filterᵇ; _∷_)
open import Data.Product                              using (∃-syntax; proj₁; proj₂; _×_; _,_; Σ)
open import Data.Sum                                  using (_⊎_; inj₁; inj₂)
open import Function                                  using (_∘_; _$_)
open import Relation.Binary.Definitions               using (DecidableEquality)
open import Relation.Binary.PropositionalEquality     using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary.Negation.Core            using (¬_)

open import Helpers

module ImplProofs
        (SessionId PostId : Set)
        (new-sid : CreateNew SessionId)
        (new-pid : CreateNew PostId)
        (_≟ₚ_ : DecidableEquality PostId)
        (_≟ₛᵢ_ : DecidableEquality SessionId)
        where

open import Twitter SessionId PostId new-sid new-pid _≟ₚ_ _≟ₛᵢ_

-- One proof per Rust #[test] in src/world.rs.
-- Step is a relation, so each theorem is an inversion over the Step evidence.
-- Note: implicit ∀-block fields of Step constructors are only in scope when
-- bound with braced patterns.

¬nothing≡just : ∀ {A : Set} {x : A} → nothing ≢ just x
¬nothing≡just ()

can-read-∃valid-session : (w : World) (sid : SessionId) (pid : PostId) →
                          CanReadPost w sid pid →
                          ∃[ acc ] ∃[ username ] ValidSession w sid acc username
can-read-∃valid-session w sid pid (post-is-private vs _ _ _ _) = ( _ , _ , vs)
can-read-∃valid-session w sid pid (post-is-public  vs _ _ _)   = ( _ , _ , vs)

--------------------------------------------------------------------------------
-- qc_publish_toplevel
--------------------------------------------------------------------------------

publish-created-elim :
  ∀ {before after sid txt pid} →
  Step before (publish sid txt nothing) after (created-post pid) →
  (∃[ acc ] ∃[ username ] ∃[ user ]
     (ValidSession before sid acc username
     ∧ PostIsNew before after pid (new-post username txt user)))
  ∧ (pid ∷ World.newest-first before ≡ World.newest-first after)
  ∧ (∀ {opy u1 u2 s} → pid ≢ opy →
       (World.post-at before opy ≡ World.post-at after opy)
     ∧ (World.account-at before u1 ≡ World.account-at after u1)
     ∧ (World.session-at before s  ≡ World.session-at after s)
     ∧ (World.follows before u1 u2 ≡ World.follows after u1 u2))
publish-created-elim
  (successful-post {_} {_} {_} {_} {username} {user} {_} {acc} vs new first others) =
  ((acc , username , user , (vs , new)) , first , others)

publish-expired-elim :
  ∀ {before after sid txt res} →
  ¬ (∃[ acc ] ∃[ username ] ValidSession before sid acc username) →
  Step before (publish sid txt nothing) after res →
  (res ≡ expired) ∧ (after ≡ before)
publish-expired-elim ¬vs
  (successful-post {_} {_} {_} {_} {username} {user} {_} {acc} vs new first others) =
  ⊥-elim (¬vs (acc , username , vs))
publish-expired-elim ¬vs (failed-access nv) = refl , refl

--------------------------------------------------------------------------------
-- qc_publish_reply
--------------------------------------------------------------------------------

publish-reply-created :
  ∀ {before after sid txt cmd-ppid pid} →
  Step before (publish sid txt (just cmd-ppid)) after (created-post pid) →
  ∃[ acc ] ∃[ username ] ∃[ user ] ∃[ ppost ] ∃[ ppid ]
    (ValidSession before sid acc username
    ∧ PostIsNew before after pid (new-reply username txt user ppid ppost)
    ∧ CanReadPost before sid cmd-ppid)
publish-reply-created
  (successful-reply {_} {_} {_} {_} {username} {user} {pid} {acc} {pparent} {ppost}
                    vs new first
                    {_} {_} {_} {_} {_} {_} {_} {_}
                    reply eq₁ eq₂ eq₃ eq₄ pid≢ others) =
  (acc , username , user , ppost , pparent , (vs , new , reply))

publish-reply-denied :
  ∀ {before after sid txt cmd-ppid res} →
  res ≡ denied →
  Step before (publish sid txt (just cmd-ppid)) after res →
  after ≡ before
publish-reply-denied ()
  (successful-reply {_} {_} {_} {_} {username} {user} {pid} {acc} {_} {ppost}
                    vs new first
                    {_} {_} {_} {_} {_} {_} {_} {_}
                    reply eq₁ eq₂ eq₃ eq₄ pid≢ others)
publish-reply-denied rs (failed-reply vs ¬c) = refl
publish-reply-denied rs (failed-access nv) = refl

publish-reply-expired :
  ∀ {before after sid txt cmd-ppid res} →
  ¬ (∃[ acc ] ∃[ username ] ValidSession before sid acc username) →
  Step before (publish sid txt (just cmd-ppid)) after res →
  (res ≡ expired) ∧ (after ≡ before)
publish-reply-expired ¬vs
  (successful-reply {_} {_} {_} {_} {username} {user} {pid} {acc} {_} {ppost}
                    vs new first
                    {_} {_} {_} {_} {_} {_} {_} {_}
                    reply eq₁ eq₂ eq₃ eq₄ pid≢ others) =
  ⊥-elim (¬vs (acc , username , vs))
publish-reply-expired ¬vs
  (failed-reply {_} {_} {_} {_} {acc} {user} vs ¬c) =
  ⊥-elim (¬vs (acc , user , vs))
publish-reply-expired ¬vs (failed-access nv) = refl , refl

--------------------------------------------------------------------------------
-- qc_delete
--------------------------------------------------------------------------------

delete-success-elim :
  ∀ {before after sid pid res} →
  res ≡ success →
  Step before (delete sid pid) after res →
  ∃[ post ] ∃[ post′ ] ∃[ acc ] ∃[ user ]
    (ValidSession before sid acc user
    ∧ World.post-at before pid ≡ just post
    ∧ World.post-at after  pid ≡ just post′
    ∧ Post.author post ≡ user
    ∧ Post.author post ≡ Post.author post′
    ∧ Post.text post ≡ Post.text post′
    ∧ Post.likes post ≡ Post.likes post′
    ∧ Post.replies post ≡ Post.replies post′
    ∧ Post.status post′ ≡ deleted)
delete-success-elim rs
  (delete-post {_} {_} {_} {_} {acc} {user} {pst} {pst′}
               vs pb pa au aeq teq leq req del others) =
  (pst , pst′ , acc , user ,
   (vs , (pb , (pa , (au , (aeq , (teq , (leq , (req , del)))))))))
delete-success-elim () (failed-delete-non-existant-post vs pb)
delete-success-elim () (failed-delete-not-author vs pb ne)
delete-success-elim () (failed-access nv)

delete-nonexist-denied :
  ∀ {before after sid pid res} →
  World.post-at before pid ≡ nothing →
  res ≡ denied →
  Step before (delete sid pid) after res →
  after ≡ before
delete-nonexist-denied e ()
  (delete-post {_} {_} {_} {_} {acc} {user} {pst} {pst′}
               vs pb pa au aeq teq leq req del others)
delete-nonexist-denied e rs (failed-delete-non-existant-post vs pb) = refl
delete-nonexist-denied e rs (failed-delete-not-author vs pb ne) =
  ⊥-elim (¬nothing≡just (trans (sym e) pb))
delete-nonexist-denied e rs (failed-access nv) = refl

delete-notauthor-class :
  ∀ {before after sid pid res} →
  Step before (delete sid pid) after res →
  (∃[ post ] ∃[ user ]
     (World.post-at before pid ≡ just post
     ∧ Post.author post ≡ user
     ∧ res ≡ success))
  ⊎ (res ≡ denied ∧ after ≡ before)
  ⊎ (res ≡ expired ∧ after ≡ before)
delete-notauthor-class
  (delete-post {_} {_} {_} {_} {acc} {user} {pst} {pst′}
               vs pb pa au aeq teq leq req del others) =
  inj₁ (pst , user , (pb , au , refl))
delete-notauthor-class
  (failed-delete-non-existant-post vs pb) = inj₂ (inj₁ (refl , refl))
delete-notauthor-class
  (failed-delete-not-author vs pb ne) = inj₂ (inj₁ (refl , refl))
delete-notauthor-class (failed-access nv) = inj₂ (inj₂ (refl , refl))

delete-expired :
  ∀ {before after sid pid res} →
  ¬ (∃[ acc ] ∃[ user ] ValidSession before sid acc user) →
  Step before (delete sid pid) after res →
  (res ≡ expired) ∧ (after ≡ before)
delete-expired ¬vs
  (delete-post {_} {_} {_} {_} {acc} {user} {pst} {pst′}
               vs pb pa au aeq teq leq req del others) =
  ⊥-elim (¬vs (acc , user , vs))
delete-expired ¬vs
  (failed-delete-non-existant-post vs pb) =
  ⊥-elim (¬vs (_ , _ , vs))
delete-expired ¬vs
  (failed-delete-not-author vs pb ne) =
  ⊥-elim (¬vs (_ , _ , vs))
delete-expired ¬vs (failed-access nv) = refl , refl

--------------------------------------------------------------------------------
-- qc_read_post
--------------------------------------------------------------------------------

read-logged-in-class :
  ∀ {before after sid pid res} →
  Step before (read-post (just sid) pid) after res →
  (∃[ post ] ∃[ author ] ∃[ txt ] ∃[ likes ] ∃[ replies ]
     (res ≡ returned-post author txt likes replies
      ∧ CanReadPost before sid pid
      ∧ World.post-at before pid ≡ just post))
  ⊎ (res ≡ denied ∧ after ≡ before)
  ⊎ (res ≡ expired ∧ after ≡ before)
read-logged-in-class
  (read-post-logged-in {_} {pid} {sid} {pst} {author} {txt} {likes} {replies}
                       c pb aeq teq ln rep) =
  inj₁ (pst , author , txt , likes , replies , (refl , c , pb))
read-logged-in-class (cant-read-post-public vs pb) = inj₂ (inj₁ (refl , refl))
read-logged-in-class (cant-read-post-private vs pb vis au fl) = inj₂ (inj₁ (refl , refl))
read-logged-in-class (cant-read-post-private-deleted vs pb st) = inj₂ (inj₁ (refl , refl))
read-logged-in-class (failed-access nv) = inj₂ (inj₂ (refl , refl))

read-anon-class :
  ∀ {before after pid res} →
  Step before (read-post nothing pid) after res →
  (∃[ p ] (World.post-at before pid ≡ just p
           ∧ Post.visibility p ≡ everyone
           ∧ Post.status p ≡ live
           ∧ res ≡ return-post p))
  ⊎ (res ≡ expired ∧ after ≡ before)
read-anon-class (read-post-anonymously {_} {pid} {p} pb vis st) =
  inj₁ (p , (pb , vis , st , refl))
read-anon-class (failed-access nv) = inj₂ (refl , refl)

--------------------------------------------------------------------------------
-- qc_personal_timeline
--------------------------------------------------------------------------------

personal-timeline-class :
  ∀ {before after sid n res} →
  Step before (read-personal-timeline sid n) after res →
  (∃[ acc ] ∃[ user ]
     (ValidSession before sid acc user
     ∧ after ≡ before
     ∧ res ≡ ((returned-timeline ∘ take n
              ∘ filterᵇ (follows-post-author before user)
              ∘ filter (can-read-post before sid)
              ∘ World.newest-first) $ before)))
  ⊎ (res ≡ expired ∧ after ≡ before)
personal-timeline-class
  (get-personal-timeline {_} {_} {sid} {acc} {user} vs) =
  inj₁ (acc , user , (vs , refl , refl))
personal-timeline-class (failed-access nv) = inj₂ (refl , refl)

--------------------------------------------------------------------------------
-- qc_global_timeline
--------------------------------------------------------------------------------

private-global-class :
  ∀ {before after sid n res} →
  Step before (read-global-timeline (just sid) n) after res →
  (∃[ acc ] ∃[ user ]
     (ValidSession before sid acc user
     ∧ after ≡ before
     ∧ res ≡ ((returned-timeline ∘ take n
              ∘ filter (can-read-post before sid)
              ∘ World.newest-first) $ before)))
  ⊎ (res ≡ expired ∧ after ≡ before)
private-global-class
  (get-private-global-timeline {_} {_} {sid} {acc} {user} vs) =
  inj₁ (acc , user , (vs , refl , refl))
private-global-class (failed-access nv) = inj₂ (refl , refl)

public-global-class :
  ∀ {before after n res} →
  Step before (read-global-timeline nothing n) after res →
  (after ≡ before
  ∧ res ≡ ((returned-timeline ∘ take n
           ∘ filter (is-post-public before)
           ∘ World.newest-first) $ before))
  ⊎ (after ≡ before ∧ res ≡ expired)
public-global-class (get-public-global-timeline) = inj₁ (refl , refl)
public-global-class (failed-access nv) = inj₂ (refl , refl)

--------------------------------------------------------------------------------
-- qc_authenticate / login_requires_account_and_password
--------------------------------------------------------------------------------

login-success-elim :
  ∀ {before after u pw sid} →
  Step before (authenticate u pw) after (issued-session sid) →
  ∃[ user ] ∃[ username ]
    (World.session-at before sid ≡ unused
    ∧ World.session-at after  sid ≡ active username
    ∧ World.account-at before username ≡ just user
    ∧ Account.password user ≡ pw
    ∧ ValidSession after  sid user username)
login-success-elim
  (login {_} {_} {username} {_} {_} {user} sb sa ac pweq others vs′) =
  (user , username , (sb , (sa , (ac , (pweq , vs′)))))

login-wrong-password :
  ∀ {before after u pw res} →
  (∃[ user ] (World.account-at before u ≡ just user
              ∧ Account.password user ≢ pw)) →
  res ≡ login-failed →
  Step before (authenticate u pw) after res →
  after ≡ before
login-wrong-password (huser , (hac , hne)) rs (failed-login-2 ac ne′) = refl
login-wrong-password (huser , (hac , hne)) rs (failed-login-1 pb) =
  ⊥-elim (¬nothing≡just (trans (sym pb) hac))
login-wrong-password ne ()
  (login {_} {_} {_} {_} {sid} {user} sb sa ac pweq others vs′)
login-wrong-password ne () (failed-access nv)

login-failed-elim :
  ∀ {before after u pw res} →
  World.account-at before u ≡ nothing →
  res ≡ login-failed →
  Step before (authenticate u pw) after res →
  after ≡ before
login-failed-elim e rs (failed-login-1 pb) = refl
login-failed-elim e rs (failed-login-2 ac ne) =
  ⊥-elim (¬nothing≡just (trans (sym e) ac))
login-failed-elim e ()
  (login {_} {_} {_} {_} {sid} {user} sb sa ac pweq others vs′)
login-failed-elim e () (failed-access nv)

--------------------------------------------------------------------------------
-- qc_register / register_then_login_then_publish
--------------------------------------------------------------------------------

register-success-elim :
  ∀ {before after u pw res} →
  res ≡ success →
  Step before (register u pw) after res →
  (World.account-at before u ≡ nothing)
  ∧ (World.account-at after  u ≡ just (account pw everyone))
register-success-elim rs (create-account pb pa others) = pb , pa
register-success-elim () (failed-create-account pb)
register-success-elim () (failed-access nv)

register-signup-failed-elim :
  ∀ {before after u pw res} →
  World.account-at before u ≢ nothing →
  res ≡ signup-failed →
  Step before (register u pw) after res →
  after ≡ before
register-signup-failed-elim ne () (create-account pb pa others)
register-signup-failed-elim ne rs (failed-create-account pb) = refl
register-signup-failed-elim ne rs (failed-access nv) = refl

--------------------------------------------------------------------------------
-- qc_revoke_token
--------------------------------------------------------------------------------

logout-success-elim :
  ∀ {before after sid res} →
  res ≡ success →
  Step before (revoke-token sid) after res →
  ∃[ user ] (World.session-at before sid ≡ active user
             ∧ World.session-at after  sid ≡ revoked)
logout-success-elim rs (logout {_} {_} {sid} {user} sb sa others) =
  (user , (sb , sa))
logout-success-elim () (failed-access nv)

logout-expired :
  ∀ {before after sid res} →
  res ≡ expired →
  Step before (revoke-token sid) after res →
  after ≡ before
logout-expired () (logout {_} {_} {sid} {user} sb sa others)
logout-expired rs (failed-access nv) = refl

--------------------------------------------------------------------------------
-- qc_follow_unfollow
--------------------------------------------------------------------------------

follow-success-elim :
  ∀ {before after sid fu res} →
  res ≡ success →
  Step before (follow sid fu) after res →
  ∃[ acc ] ∃[ follower ]
    (ValidSession before sid acc follower
    ∧ (World.follows after  ≡ add-follower (World.follows before) follower fu
       ∧ World.account-at before   ≡ World.account-at after
       ∧ World.session-at before   ≡ World.session-at after
       ∧ World.post-at before      ≡ World.post-at after
       ∧ World.newest-first before ≡ World.newest-first after))
follow-success-elim rs
  (follow-user {_} {_} {sid} {acc} {follower} vs feq ae se pe nf) =
  (acc , follower , (vs , (feq , (ae , (se , (pe , nf))))))
follow-success-elim () (failed-access nv)

unfollow-success-elim :
  ∀ {before after sid fu res} →
  res ≡ success →
  Step before (unfollow sid fu) after res →
  ∃[ acc ] ∃[ follower ]
    (ValidSession before sid acc follower
    ∧ (World.follows after  ≡ remove-follower (World.follows before) follower fu
       ∧ World.account-at before   ≡ World.account-at after
       ∧ World.session-at before   ≡ World.session-at after
       ∧ World.post-at before      ≡ World.post-at after
       ∧ World.newest-first before ≡ World.newest-first after))
unfollow-success-elim rs
  (unfollow-user {_} {_} {sid} {acc} {follower} vs feq ae se pe nf) =
  (acc , follower , (vs , (feq , (ae , (se , (pe , nf))))))
unfollow-success-elim () (failed-access nv)

--------------------------------------------------------------------------------
-- qc_like_unlike
--------------------------------------------------------------------------------

like-success-elim :
  ∀ {before after sid pid res} →
  res ≡ success →
  Step before (like sid pid) after res →
  ∃[ acc ] ∃[ user ] ∃[ post ] ∃[ post′ ]
    (ValidSession before sid acc user
    ∧ CanReadPost before sid pid
    ∧ World.post-at before pid ≡ just post
    ∧ World.post-at after  pid ≡ just post′
    ∧ user ∈ Post.likes post′)
like-success-elim rs
  (like-post {_} {_} {sid} {pid} {acc} {user} {pst} {pst′}
             vs c pb pa mem aeq teq vseq sseq req peq users others) =
  (acc , user , pst , pst′ , (vs , (c , (pb , (pa , mem)))))
like-success-elim () (failed-like-post vs ¬c)
like-success-elim () (failed-access nv)

like-denied :
  ∀ {before after sid pid acc user res} →
  ValidSession before sid acc user →
  ¬ CanReadPost before sid pid →
  Step before (like sid pid) after res →
  (res ≡ denied) ∧ (after ≡ before)
like-denied vs ¬c
  (like-post {_} {_} {sid} {pid} {acc} {user} {pst} {pst′}
             vs′ c pb pa mem aeq teq vseq sseq req peq users others) =
  ⊥-elim (¬c c)
like-denied vs ¬c (failed-like-post vs′ ¬c′) = refl , refl
like-denied vs ¬c (failed-access nv) =   ⊥-elim (nv refl (_ , _ , vs))

like-expired :
  ∀ {before after sid pid res} →
  ¬ (∃[ acc ] ∃[ user ] ValidSession before sid acc user) →
  Step before (like sid pid) after res →
  (res ≡ expired) ∧ (after ≡ before)
like-expired ¬vs
  (like-post {_} {_} {sid} {pid} {acc} {user} {pst} {pst′}
             vs c pb pa mem aeq teq vseq sseq req peq users others) =
  ⊥-elim (¬vs (acc , user , vs))
like-expired ¬vs (failed-like-post vs ¬c) = ⊥-elim (¬vs (_ , _ , vs))
like-expired ¬vs (failed-access nv) = refl , refl

unlike-success-elim :
  ∀ {before after sid pid res} →
  res ≡ success →
  Step before (unlike sid pid) after res →
  ∃[ acc ] ∃[ user ] ∃[ post ] ∃[ post′ ]
    (ValidSession before sid acc user
    ∧ CanReadPost before sid pid
    ∧ World.post-at before pid ≡ just post′
    ∧ World.post-at after  pid ≡ just post
    ∧ user ∉ Post.likes post)
unlike-success-elim rs
  (unlike-post {_} {_} {sid} {pid} {acc} {user} {pst} {pst′}
               vs c pb pa nub aeq teq vseq sseq req peq users others) =
  (acc , user , pst , pst′ , (vs , (c , (pb , (pa , nub)))))
unlike-success-elim () (failed-unlike-post vs ¬c)
unlike-success-elim () (failed-access nv)

unlike-denied :
  ∀ {before after sid pid acc user res} →
  ValidSession before sid acc user →
  ¬ CanReadPost before sid pid →
  Step before (unlike sid pid) after res →
  (res ≡ denied) ∧ (after ≡ before)
unlike-denied vs ¬c
  (unlike-post {_} {_} {sid} {pid} {acc} {user} {pst} {pst′}
               vs′ c pb pa nub aeq teq vseq sseq req peq users others) =
  ⊥-elim (¬c c)
unlike-denied vs ¬c (failed-unlike-post vs′ ¬c′) = refl , refl
unlike-denied vs ¬c (failed-access nv) =   ⊥-elim (nv refl (_ , _ , vs))

unlike-expired :
  ∀ {before after sid pid res} →
  ¬ (∃[ acc ] ∃[ user ] ValidSession before sid acc user) →
  Step before (unlike sid pid) after res →
  (res ≡ expired) ∧ (after ≡ before)
unlike-expired ¬vs
  (unlike-post {_} {_} {sid} {pid} {acc} {user} {pst} {pst′}
               vs c pb pa nub aeq teq vseq sseq req peq users others) =
  ⊥-elim (¬vs (acc , user , vs))
unlike-expired ¬vs (failed-unlike-post vs ¬c) = ⊥-elim (¬vs (_ , _ , vs))
unlike-expired ¬vs (failed-access nv) = refl , refl

--------------------------------------------------------------------------------
-- qc_time_passes
--------------------------------------------------------------------------------

time-passes-elim :
  ∀ {before after} →
  Step before time-passes after success →
  (∀ {sid user} → World.session-at before sid ≡ active user →
        World.session-at after  sid ≡ revoked)
  ∧ (∀ {sid} → World.session-at before sid ≡ World.session-at after sid →
        World.account-at before      ≡ World.account-at after →
        World.post-at before         ≡ World.post-at after →
        World.follows before         ≡ World.follows after →
        World.newest-first before    ≡ World.newest-first after)
time-passes-elim (session-timeout f others) = (f , others)
