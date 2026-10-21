module Interface where

open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe
open import Agda.Builtin.List
open import Agda.Builtin.String

record LoginToken : Set where
  constructor token
  field
    t : Nat

record TweetId : Set where
  constructor tweet-id
  field
    t : Nat

-- The public API after parsing. Entirely unvalidated on purpose.
data Action : Set where
  post-tweet     : LoginToken → String        → Action
  -- delete-tweet   : LoginToken → TweetId       → Action
  -- like           : LoginToken → TweetId       → Action
  -- unlike         : LoginToken → TweetId       → Action
  get-tweet      : Maybe LoginToken → TweetId → Action
  timeline       : Maybe LoginToken → Nat     → Action
  -- search         : Maybe LoginToken → String  → Action
  login          : String → String            → Action
  -- logout         : LoginToken                 → Action
  signup         : String → String            → Action
  -- delete-account : LoginToken                 → Action

-- Possible responses from the public API
data Response : Set where
  ok                   : Response
  permission-error     : Response
  outdated-login-token : Response
  tweet-id             : TweetId → Response
  timeline             : List TweetId → Response
  session-token        : LoginToken → Response
  login-error          : Response
  signup-error         : Response
  tweet
    : String       -- Poster
    → String       -- Body
    → Nat          -- Likes
    → List TweetId -- Replies
    → Response
