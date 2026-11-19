-- ImplParse.agda (task RV2e): a STANDALONE, stdlib-only model of the byte-level
-- decisions of backend/src/wire.rs:parse_action, pinned by refl on EXACTLY the
-- concrete request bytes of the wire.rs test mod: endpoint_shapes (:332),
-- anonymous_and_tokened (:395), separator_variants (:470), malformed (:479),
-- qc_post_round_trip (:535).  ImplWire.agda pins from-input at the SPEC level;
-- these pins fix parse_action itself: split_lines (:80-108) CRLF/LF/CR splitting
-- with exactly one trailing empty line dropped, parse_u64 (:59-69) ASCII digits
-- only plus the u64 bound, the arity helpers count_err (:111) token_text (:130)
-- two_texts (:141) one_num (:149) reply (:160) opt_num (:171), and the 13-route
-- path table (:187-206).  Request bytes are modelled as List Char (the bodies in
-- the tests are ASCII, so line_text of :72 is the identity here); every decision
-- is a Bool/Maybe computation and every theorem below is refl.  No postulates.

module ImplParse where

open import Data.Nat                               using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties                    using (_<?_)
open import Relation.Nullary.Decidable.Core         using (yes; no)
open import Data.List                               using (List; []; _∷_; _++_; reverse)
open import Agda.Builtin.Char                       using (Char)
open import Agda.Builtin.Maybe                      using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality   using (_≡_; refl)

-- ---- the byte model -------------------------------------------------------

cr : Char
cr = '\r'

lf : Char
lf = '\n'

-- split_lines of wire.rs: one line ends at CRLF, LF or bare CR; the accumulator
-- holds the current line reversed, and exactly one trailing empty line is dropped.

split-lines : List Char → List (List Char)
split-lines cs = drop-last (go [] cs)
  where
    go : List Char → List Char → List (List Char)
    go cur []                 = reverse cur ∷ []
    go cur ('\r' ∷ '\n' ∷ cs) = reverse cur ∷ go [] cs
    go cur ('\r' ∷ cs)        = reverse cur ∷ go [] cs
    go cur ('\n' ∷ cs)        = reverse cur ∷ go [] cs
    go cur (c ∷ cs)           = go (c ∷ cur) cs

    drop-last : List (List Char) → List (List Char)
    drop-last []           = []
    drop-last (l ∷ [])     with l
    ...   | []             = []
    ...   | (_ ∷ _)        = l ∷ []
    drop-last (l ∷ l' ∷ ls) = l ∷ drop-last (l' ∷ ls)

-- parse_u64 of wire.rs: non-empty ASCII digits only, and the value must fit a u64.

digit-value : Char → Maybe ℕ
digit-value '0' = just 0
digit-value '1' = just 1
digit-value '2' = just 2
digit-value '3' = just 3
digit-value '4' = just 4
digit-value '5' = just 5
digit-value '6' = just 6
digit-value '7' = just 7
digit-value '8' = just 8
digit-value '9' = just 9
digit-value _   = nothing

nat-of : List Char → ℕ → Maybe ℕ
nat-of [] acc = just acc
nat-of (c ∷ cs) acc with digit-value c
... | nothing = nothing
... | just d  = nat-of cs (acc * 10 + d)

u64-bound : ℕ
u64-bound = 18446744073709551616

within-u64 : Maybe ℕ → Maybe ℕ
within-u64 nothing = nothing
within-u64 (just n) with n <? u64-bound
... | yes _ = just n
... | no  _ = nothing

parse-num : List Char → Maybe ℕ
parse-num [] = nothing
parse-num (c ∷ cs) = within-u64 (nat-of (c ∷ cs) 0)

-- len/count_err of wire.rs (:111-116): short bodies are MissingLine, long ones
-- UnexpectedLine.

len-lines : List (List Char) → ℕ
len-lines [] = 0
len-lines (_ ∷ xs) = suc (len-lines xs)

-- ---- the result shape of parse_action (:185) --------------------------------
-- the 13 WireAction constructors (wire.rs :20-34) and the 4 WireError ones (:11-16)

data Res : Set where
  ok-post-tweet                             : ℕ → List Char → Res
  ok-post-reply                             : ℕ → List Char → ℕ → Res
  ok-delete-tweet ok-like ok-unlike ok-private-timeline
                                            : ℕ → ℕ → Res
  ok-follow ok-unfollow                     : ℕ → List Char → Res
  ok-get-tweet ok-global-timeline           : Maybe ℕ → ℕ → Res
  ok-login ok-signup                        : List Char → List Char → Res
  ok-logout                                 : ℕ → Res
  bad-number missing-line unexpected-line unknown-endpoint : Res

data Endp : Set where
  e-post-tweet : Endp
  e-post-reply : Endp
  e-delete-tweet : Endp
  e-like-tweet : Endp
  e-unlike-tweet : Endp
  e-follow-user : Endp
  e-unfollow-user : Endp
  e-get-tweet : Endp
  e-global-timeline : Endp
  e-private-timeline : Endp
  e-logout : Endp
  e-login : Endp
  e-signup : Endp

-- the body-shape helpers, generic in the constructor they build (token_text :130,
-- two_nums :119, two_texts :141, one_num :149, reply :160, opt_num :171).

count-err : List (List Char) → ℕ → Res
count-err ls want with len-lines ls <? want
... | yes _ = missing-line
... | no  _ = unexpected-line

mk-text : (ℕ → List Char → Res) → List (List Char) → Res
mk-text f (a ∷ b ∷ []) with parse-num a
... | just tk  = f tk b
... | nothing  = bad-number
mk-text f ls = count-err ls 2

mk-pair : (ℕ → ℕ → Res) → List (List Char) → Res
mk-pair f (a ∷ b ∷ []) with parse-num a | parse-num b
... | just x | just y = f x y
... | _      | _      = bad-number
mk-pair f ls = count-err ls 2

mk-texts : (List Char → List Char → Res) → List (List Char) → Res
mk-texts f (a ∷ b ∷ []) = f a b
mk-texts f ls = count-err ls 2

mk-one : (ℕ → Res) → List (List Char) → Res
mk-one f (a ∷ []) with parse-num a
... | just n  = f n
... | nothing = bad-number
mk-one f ls = count-err ls 1

mk-triple : (ℕ → List Char → ℕ → Res) → List (List Char) → Res
mk-triple f (a ∷ b ∷ c ∷ []) with parse-num a | parse-num c
... | just x | just z = f x b z
... | _      | _      = bad-number
mk-triple f ls = count-err ls 3

mk-opt : (Maybe ℕ → ℕ → Res) → List (List Char) → Res
mk-opt f (a ∷ []) with parse-num a
... | just n    = f nothing n
... | nothing   = bad-number
mk-opt f (a ∷ b ∷ []) with parse-num a | parse-num b
... | just x | just y = f (just x) y
... | _      | _      = bad-number
mk-opt f ls = count-err ls 2

body-parse : Endp → List (List Char) → Res
body-parse e-post-tweet ls = mk-text ok-post-tweet ls
body-parse e-post-reply ls = mk-triple ok-post-reply ls
body-parse e-delete-tweet ls = mk-pair ok-delete-tweet ls
body-parse e-like-tweet ls = mk-pair ok-like ls
body-parse e-unlike-tweet ls = mk-pair ok-unlike ls
body-parse e-follow-user ls = mk-text ok-follow ls
body-parse e-unfollow-user ls = mk-text ok-unfollow ls
body-parse e-get-tweet ls = mk-opt ok-get-tweet ls
body-parse e-global-timeline ls = mk-opt ok-global-timeline ls
body-parse e-private-timeline ls = mk-pair ok-private-timeline ls
body-parse e-logout ls = mk-one ok-logout ls
body-parse e-login ls = mk-texts ok-login ls
body-parse e-signup ls = mk-texts ok-signup ls

-- ---- the path table of parse_action (:187-206) ------------------------------
-- each pattern is one /api/<name> literal, byte for byte.

endp : List Char → Maybe Endp
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'p' ∷ 'o' ∷ 's' ∷ 't' ∷ '-' ∷ 't' ∷ 'w' ∷ 'e' ∷ 'e' ∷ 't' ∷ []) = just e-post-tweet
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'p' ∷ 'o' ∷ 's' ∷ 't' ∷ '-' ∷ 'r' ∷ 'e' ∷ 'p' ∷ 'l' ∷ 'y' ∷ []) = just e-post-reply
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'd' ∷ 'e' ∷ 'l' ∷ 'e' ∷ 't' ∷ 'e' ∷ '-' ∷ 't' ∷ 'w' ∷ 'e' ∷ 'e' ∷ 't' ∷ []) = just e-delete-tweet
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'l' ∷ 'i' ∷ 'k' ∷ 'e' ∷ '-' ∷ 't' ∷ 'w' ∷ 'e' ∷ 'e' ∷ 't' ∷ []) = just e-like-tweet
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'u' ∷ 'n' ∷ 'l' ∷ 'i' ∷ 'k' ∷ 'e' ∷ '-' ∷ 't' ∷ 'w' ∷ 'e' ∷ 'e' ∷ 't' ∷ []) = just e-unlike-tweet
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'f' ∷ 'o' ∷ 'l' ∷ 'l' ∷ 'o' ∷ 'w' ∷ '-' ∷ 'u' ∷ 's' ∷ 'e' ∷ 'r' ∷ []) = just e-follow-user
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'u' ∷ 'n' ∷ 'f' ∷ 'o' ∷ 'l' ∷ 'l' ∷ 'o' ∷ 'w' ∷ '-' ∷ 'u' ∷ 's' ∷ 'e' ∷ 'r' ∷ []) = just e-unfollow-user
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'g' ∷ 'e' ∷ 't' ∷ '-' ∷ 't' ∷ 'w' ∷ 'e' ∷ 'e' ∷ 't' ∷ []) = just e-get-tweet
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'g' ∷ 'l' ∷ 'o' ∷ 'b' ∷ 'a' ∷ 'l' ∷ '-' ∷ 't' ∷ 'i' ∷ 'm' ∷ 'e' ∷ 'l' ∷ 'i' ∷ 'n' ∷ 'e' ∷ []) = just e-global-timeline
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'p' ∷ 'r' ∷ 'i' ∷ 'v' ∷ 'a' ∷ 't' ∷ 'e' ∷ '-' ∷ 't' ∷ 'i' ∷ 'm' ∷ 'e' ∷ 'l' ∷ 'i' ∷ 'n' ∷ 'e' ∷ []) = just e-private-timeline
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'l' ∷ 'o' ∷ 'g' ∷ 'o' ∷ 'u' ∷ 't' ∷ []) = just e-logout
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 'l' ∷ 'o' ∷ 'g' ∷ 'i' ∷ 'n' ∷ []) = just e-login
endp ('/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ 's' ∷ 'i' ∷ 'g' ∷ 'n' ∷ 'u' ∷ 'p' ∷ []) = just e-signup
endp _ = nothing

api : List Char → List Char
api p = '/' ∷ 'a' ∷ 'p' ∷ 'i' ∷ '/' ∷ p

parse-action : List Char → List Char → Res
parse-action p cs with endp p
... | nothing  = unknown-endpoint
... | just e   = body-parse e (split-lines cs)

-- ---- the test constants, copied from wire.rs's test mod ---------------------

nm-post-tweet = 'p' ∷ 'o' ∷ 's' ∷ 't' ∷ '-' ∷ 't' ∷ 'w' ∷ 'e' ∷ 'e' ∷ 't' ∷ []
nm-post-reply = 'p' ∷ 'o' ∷ 's' ∷ 't' ∷ '-' ∷ 'r' ∷ 'e' ∷ 'p' ∷ 'l' ∷ 'y' ∷ []
nm-delete-tweet = 'd' ∷ 'e' ∷ 'l' ∷ 'e' ∷ 't' ∷ 'e' ∷ '-' ∷ 't' ∷ 'w' ∷ 'e' ∷ 'e' ∷ 't' ∷ []
nm-like-tweet = 'l' ∷ 'i' ∷ 'k' ∷ 'e' ∷ '-' ∷ 't' ∷ 'w' ∷ 'e' ∷ 'e' ∷ 't' ∷ []
nm-unlike-tweet = 'u' ∷ 'n' ∷ 'l' ∷ 'i' ∷ 'k' ∷ 'e' ∷ '-' ∷ 't' ∷ 'w' ∷ 'e' ∷ 'e' ∷ 't' ∷ []
nm-follow-user = 'f' ∷ 'o' ∷ 'l' ∷ 'l' ∷ 'o' ∷ 'w' ∷ '-' ∷ 'u' ∷ 's' ∷ 'e' ∷ 'r' ∷ []
nm-unfollow-user = 'u' ∷ 'n' ∷ 'f' ∷ 'o' ∷ 'l' ∷ 'l' ∷ 'o' ∷ 'w' ∷ '-' ∷ 'u' ∷ 's' ∷ 'e' ∷ 'r' ∷ []
nm-get-tweet = 'g' ∷ 'e' ∷ 't' ∷ '-' ∷ 't' ∷ 'w' ∷ 'e' ∷ 'e' ∷ 't' ∷ []
nm-global-timeline = 'g' ∷ 'l' ∷ 'o' ∷ 'b' ∷ 'a' ∷ 'l' ∷ '-' ∷ 't' ∷ 'i' ∷ 'm' ∷ 'e' ∷ 'l' ∷ 'i' ∷ 'n' ∷ 'e' ∷ []
nm-private-timeline = 'p' ∷ 'r' ∷ 'i' ∷ 'v' ∷ 'a' ∷ 't' ∷ 'e' ∷ '-' ∷ 't' ∷ 'i' ∷ 'm' ∷ 'e' ∷ 'l' ∷ 'i' ∷ 'n' ∷ 'e' ∷ []
nm-logout = 'l' ∷ 'o' ∷ 'g' ∷ 'o' ∷ 'u' ∷ 't' ∷ []
nm-login = 'l' ∷ 'o' ∷ 'g' ∷ 'i' ∷ 'n' ∷ []
nm-signup = 's' ∷ 'i' ∷ 'g' ∷ 'n' ∷ 'u' ∷ 'p' ∷ []

nm-nope = 'n' ∷ 'o' ∷ 'p' ∷ 'e' ∷ []

l-7 = '7' ∷ []
l-8 = '8' ∷ []
l-3 = '3' ∷ []
l-42 = '4' ∷ '2' ∷ []
l-x = 'x' ∷ []
l-hi = 'h' ∷ 'i' ∷ []
l-bob = 'b' ∷ 'o' ∷ 'b' ∷ []
l-pw = 'p' ∷ 'w' ∷ []
l-not-a-num = 'n' ∷ 'o' ∷ 't' ∷ '-' ∷ 'a' ∷ '-' ∷ 'n' ∷ 'u' ∷ 'm' ∷ []

lfm : List Char
lfm = '\n' ∷ []

crlf : List Char
crlf = '\r' ∷ '\n' ∷ []

n-9s-7 = '9' ∷ '9' ∷ '9' ∷ '9' ∷ '9' ∷ '9' ∷ '9' ∷ []
l-overflow = n-9s-7 ++ n-9s-7 ++ n-9s-7 ++ ('9' ∷ '9' ∷ [])

-- the three bodies of separator_variants (:472-474) and the lines they must give.

b-crlf = l-7 ++ crlf ++ l-hi ++ crlf ++ l-42 ++ crlf
b-lf = l-7 ++ lfm ++ l-hi ++ lfm ++ l-42 ++ lfm
b-cr = l-7 ++ (('\r' ∷ [])) ++ l-hi ++ (('\r' ∷ [])) ++ l-42

lines-7-hi-42 : List (List Char)
lines-7-hi-42 = l-7 ∷ l-hi ∷ l-42 ∷ []


-- ---- pins: parse-num decisions (backs malformed :480-487) ------------------

th-num-7 : parse-num l-7 ≡ just 7
th-num-7 = refl

th-num-42 : parse-num l-42 ≡ just 42
th-num-42 = refl

th-num-x : parse-num l-x ≡ nothing
th-num-x = refl

th-num-empty : parse-num [] ≡ nothing
th-num-empty = refl

th-num-overflow : parse-num l-overflow ≡ nothing
th-num-overflow = refl

-- ---- pins: the 13 routes of the path table + one unknown path --------------

th-endp-post-tweet : endp (api nm-post-tweet) ≡ just e-post-tweet
th-endp-post-tweet = refl

th-endp-post-reply : endp (api nm-post-reply) ≡ just e-post-reply
th-endp-post-reply = refl

th-endp-delete-tweet : endp (api nm-delete-tweet) ≡ just e-delete-tweet
th-endp-delete-tweet = refl

th-endp-like-tweet : endp (api nm-like-tweet) ≡ just e-like-tweet
th-endp-like-tweet = refl

th-endp-unlike-tweet : endp (api nm-unlike-tweet) ≡ just e-unlike-tweet
th-endp-unlike-tweet = refl

th-endp-follow-user : endp (api nm-follow-user) ≡ just e-follow-user
th-endp-follow-user = refl

th-endp-unfollow-user : endp (api nm-unfollow-user) ≡ just e-unfollow-user
th-endp-unfollow-user = refl

th-endp-get-tweet : endp (api nm-get-tweet) ≡ just e-get-tweet
th-endp-get-tweet = refl

th-endp-global-timeline : endp (api nm-global-timeline) ≡ just e-global-timeline
th-endp-global-timeline = refl

th-endp-private-timeline : endp (api nm-private-timeline) ≡ just e-private-timeline
th-endp-private-timeline = refl

th-endp-logout : endp (api nm-logout) ≡ just e-logout
th-endp-logout = refl

th-endp-login : endp (api nm-login) ≡ just e-login
th-endp-login = refl

th-endp-signup : endp (api nm-signup) ≡ just e-signup
th-endp-signup = refl

th-endp-unknown : endp (api nm-nope) ≡ nothing
th-endp-unknown = refl

-- ---- pins: split_lines is separator-insensitive (backs separator_variants) -

th-split-crlf : split-lines b-crlf ≡ lines-7-hi-42
th-split-crlf = refl

th-split-lf : split-lines b-lf ≡ lines-7-hi-42
th-split-lf = refl

th-split-cr : split-lines b-cr ≡ lines-7-hi-42
th-split-cr = refl

-- ---- pins: endpoint_shapes (:333-390), every body shape parses to its action

th-shape-post-tweet : parse-action (api nm-post-tweet) (l-7 ++ crlf ++ l-hi) ≡ ok-post-tweet 7 l-hi
th-shape-post-tweet = refl

th-shape-post-reply : parse-action (api nm-post-reply) (l-7 ++ crlf ++ l-hi ++ crlf ++ l-42) ≡ ok-post-reply 7 l-hi 42
th-shape-post-reply = refl

th-shape-delete-tweet : parse-action (api nm-delete-tweet) (l-7 ++ crlf ++ l-42) ≡ ok-delete-tweet 7 42
th-shape-delete-tweet = refl

th-shape-like-tweet : parse-action (api nm-like-tweet) (l-7 ++ crlf ++ l-42) ≡ ok-like 7 42
th-shape-like-tweet = refl

th-shape-unlike-tweet : parse-action (api nm-unlike-tweet) (l-7 ++ crlf ++ l-42) ≡ ok-unlike 7 42
th-shape-unlike-tweet = refl

th-shape-follow-user : parse-action (api nm-follow-user) (l-7 ++ crlf ++ l-bob) ≡ ok-follow 7 l-bob
th-shape-follow-user = refl

th-shape-unfollow-user : parse-action (api nm-unfollow-user) (l-7 ++ crlf ++ l-bob) ≡ ok-unfollow 7 l-bob
th-shape-unfollow-user = refl

th-shape-get-tweet : parse-action (api nm-get-tweet) (l-7 ++ crlf ++ l-42) ≡ ok-get-tweet (just 7) 42
th-shape-get-tweet = refl

th-shape-global-timeline : parse-action (api nm-global-timeline) (l-7 ++ crlf ++ l-3) ≡ ok-global-timeline (just 7) 3
th-shape-global-timeline = refl

th-shape-private-timeline : parse-action (api nm-private-timeline) (l-7 ++ crlf ++ l-3) ≡ ok-private-timeline 7 3
th-shape-private-timeline = refl

th-shape-logout : parse-action (api nm-logout) (l-7) ≡ ok-logout 7
th-shape-logout = refl

th-shape-login : parse-action (api nm-login) (l-bob ++ crlf ++ l-pw) ≡ ok-login l-bob l-pw
th-shape-login = refl

th-shape-signup : parse-action (api nm-signup) (l-bob ++ crlf ++ l-pw) ≡ ok-signup l-bob l-pw
th-shape-signup = refl

-- ---- pins: anonymous_and_tokened (:396-410) - arity decides anon vs token ---

th-arity-get-anon : parse-action (api nm-get-tweet) (l-42) ≡ ok-get-tweet nothing 42
th-arity-get-anon = refl

th-arity-get-token : parse-action (api nm-get-tweet) (l-7 ++ crlf ++ l-42) ≡ ok-get-tweet (just 7) 42
th-arity-get-token = refl

th-arity-global-anon : parse-action (api nm-global-timeline) (l-3) ≡ ok-global-timeline nothing 3
th-arity-global-anon = refl

th-arity-global-token : parse-action (api nm-global-timeline) (l-7 ++ crlf ++ l-3) ≡ ok-global-timeline (just 7) 3
th-arity-global-token = refl

th-opt-anon : mk-opt ok-get-tweet (l-42 ∷ []) ≡ ok-get-tweet nothing 42
th-opt-anon = refl

th-opt-token : mk-opt ok-get-tweet (l-7 ∷ l-42 ∷ []) ≡ ok-get-tweet (just 7) 42
th-opt-token = refl

-- ---- pins: separator_variants (:471-475), CRLF/LF/bare-CR agree -------------

th-sv-crlf : parse-action (api nm-post-reply) b-crlf ≡ ok-post-reply 7 l-hi 42
th-sv-crlf = refl

th-sv-lf : parse-action (api nm-post-reply) b-lf ≡ ok-post-reply 7 l-hi 42
th-sv-lf = refl

th-sv-cr : parse-action (api nm-post-reply) b-cr ≡ ok-post-reply 7 l-hi 42
th-sv-cr = refl

-- ---- pins: malformed (:480-491), each classification is the right error tag -

th-mf-like-bad-number : parse-action (api nm-like-tweet) (l-x ++ lfm ++ l-42) ≡ bad-number
th-mf-like-bad-number = refl

th-mf-get-bad-number : parse-action (api nm-get-tweet) (l-not-a-num) ≡ bad-number
th-mf-get-bad-number = refl

th-mf-logout-overflow : parse-action (api nm-logout) (l-overflow) ≡ bad-number
th-mf-logout-overflow = refl

th-mf-logout-missing-line : parse-action (api nm-logout) ([]) ≡ missing-line
th-mf-logout-missing-line = refl

th-mf-logout-unexpected-line : parse-action (api nm-logout) (l-7 ++ lfm ++ l-8) ≡ unexpected-line
th-mf-logout-unexpected-line = refl

th-mf-unknown-endpoint : parse-action (api nm-nope) (l-7) ≡ unknown-endpoint
th-mf-unknown-endpoint = refl

-- ---- pins: qc_post_round_trip (:533-539) with the test's own constants: the
-- body tk-line ++ CRLF ++ txt-line (++ one trailing separator) parses to the
-- SAME components the Rust QuickCheck asserts, token 7 and text "hi". ---------

th-round-trip : parse-action (api nm-post-tweet) (l-7 ++ crlf ++ l-hi ++ crlf) ≡ ok-post-tweet 7 l-hi
th-round-trip = refl

th-round-trip-lf : parse-action (api nm-post-tweet) (l-7 ++ crlf ++ l-hi ++ lfm) ≡ ok-post-tweet 7 l-hi
th-round-trip-lf = refl
