module Proofs (SessionId PostId : Set) where

open import Twitter SessionId PostId

open import Agda.Builtin.String

post-doesnt-exist-before-posting :
  (sid : SessionId) (txt : String) (pid : PostId) (before after : World) →
  Step before (publish sid txt) after success →
  pid ∉ World.newest-first before
post-doesnt-exist-before-posting = {!!}
