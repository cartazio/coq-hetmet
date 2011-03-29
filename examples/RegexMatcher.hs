{-# OPTIONS_GHC -XModalTypes -XMultiParamTypeClasses -ddump-types #-}
module RegexMatcher
where
import GHC.HetMet.CodeTypes hiding ((-))

--------------------------------------------------------------------------------
--
-- A one-level Regular Expression matcher, adapted from
-- Nanevski+Pfenning's _Staged computation with names and necessity_,
-- Figure 5
--

data Regex
 = Empty
 | Plus  Regex Regex 
 | Times Regex Regex
 | Star  Regex
 | Const Char

class Stream a where
  s_empty :: a -> Bool
  s_head  :: a -> Char
  s_tail  :: a -> a

-- A continuation-passing-style matcher.  If the "b" argument is false
-- the expression must match at least one character before passing
-- control to the continuation (this avoids the equality test in the
-- Nanevski+Pfenning code)

accept :: Stream s =>
        Regex ->
        Bool ->           -- may only match the empty string if this is True
        (s -> Bool) ->
        s ->
        Bool

accept Empty False k s     =
  False

accept Empty True k s    =
  k s

accept (Plus e1 e2) emptyOk k s   =
 (accept e1 emptyOk k s) || (accept e2 emptyOk k s)

accept (Times e1 e2) True k s  =
 (accept e1 True (accept e2 True k)) s

accept (Times e1 e2) False k s  =
 (accept e1 False (accept e2 True  k)) s ||
 (accept e1 True  (accept e2 False k)) s

accept (Star e) emptyOk k s     =
 (emptyOk && (k s)) ||
 (accept e emptyOk (\s' -> accept (Star e) False k s') s)

accept (Const c) emptyOk k s      =
 if s_empty s 
 then False
 else (s_head s) == c && k (s_tail s)



--------------------------------------------------------------------------------
--
-- A two-level Regular Expression matcher, adapted from
-- Nanevski+Pfenning's _Staged computation with names and necessity_,
-- Figure 6
--

class GuestStream g a where
  <[ gs_empty ]> :: <[ a -> Bool ]>@g
  <[ gs_head  ]> :: <[ a -> Char ]>@g
  <[ gs_tail  ]> :: <[ a -> a    ]>@g

class GuestEqChar g where
  <[ (==) ]> :: <[ Char -> Char -> Bool ]>@g

staged_accept ::
    Regex
    -> Bool
    -> forall c s.
         GuestStream c s =>
         GuestCharLiteral c =>
         GuestLanguageBool c =>
         GuestEqChar c =>
         <[ s -> Bool ]>@c
      -> <[ s -> Bool ]>@c

staged_accept Empty False k      =
   <[ \s -> false ]>

staged_accept Empty True  k      =
   <[ \s -> gs_empty s ]>

staged_accept (Plus e1 e2) emptyOk k     =
   <[ \s -> let k' = ~~k
            in (~~(staged_accept e1 emptyOk <[k']>) s) ||
               (~~(staged_accept e2 emptyOk <[k']>) s)
            ]>

staged_accept (Times e1 e2) True k    =
   <[ \s -> ~~(staged_accept e1 True (staged_accept e2 True k)) s ]>

staged_accept (Times e1 e2) emptyOk k    =
   <[ \s -> ~~(staged_accept e1 True  (staged_accept e2 False k)) s ||
            ~~(staged_accept e1 False (staged_accept e2 True  k)) s
            ]>

staged_accept (Star e) emptyOk' k  =
   loop emptyOk'
    where
    -- loop :: Bool -> <[s -> Bool]>@g
     loop emptyOk = if emptyOk
                    then <[ \s -> ~~k s || ~~(staged_accept e True  (loop False)) s ]>
                    else <[ \s ->          ~~(staged_accept e False (loop False)) s ]>
    -- note that loop is not (forall c s. <[s -> Bool]>@c)
    -- because "k" is free in loop; it is analogous to the free
    -- environment variable in Nanevski's example

staged_accept (Const c) emptyOk k  =
    <[ \s -> if gs_empty s 
             then false
             else (gs_head s) == ~~(guestCharLiteral c) && ~~k (gs_tail s) ]>

--
-- Take particular note of the "Plus" case above: note that (following
-- Nanevski+Pfenning) the code for "k" is not duplicated -- it is
-- escapified into the constructed term only once, and a tiny scrap of
-- code containing nothing more than the variable name k' is passed
-- to the recursive call.  This is in contrast with the naive implementation
-- shown below:
--
-- staged_accept (Plus e1 e2) emptyOk k     =
--    <[ \s -> (~~(staged_accept e1 emptyOk k) s) ||
--             (~~(staged_accept e2 emptyOk k) s)
--             ]>
--

--
-- The following commented-out type is "too polymorphic" -- try
-- uncommenting it to see what happens.  It's a great example of the
-- kind of thing that environment classifiers guard against: the
-- continuation code and the result code get their classifiers
-- unified.
--
{-
staged_accept ::
    Regex
    -> Bool
    -> (forall c s.
        GuestStream c s =>
        GuestCharLiteral c =>
        GuestLanguageBool c =>
        GuestEqChar c =>
        <[s -> Bool]>@c)
   -> (forall c s.
        GuestStream c s =>
        GuestCharLiteral c =>
        GuestLanguageBool c =>
        GuestEqChar c =>
        <[s -> Bool]>@c)
-}
