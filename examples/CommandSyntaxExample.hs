{-# OPTIONS_GHC -XModalTypes -XMultiParamTypeClasses -ddump-types -XNoMonoPatBinds  #-}
module CommandSyntaxExample
where

--
-- Please ignore this; I never got around to implementing it.
--

{-
The example may seem a little contrived, but its purpose is to
illustrate the be- haviour when the argument of mapC refers both to
its parameter and a free vari- able (n).

\begin{verbatim}
-- we can use mapA rather than mapC (from page 100)

mapA f = proc xs -> case xs of
[] -> returnA -< [] x:xs’ -> do y <- f -< x
ys’ <- mapA f -< xs’ returnA -< y:ys

example2 =
   <[ \(n,xs) -> 
       ~(mapA <[ \x-> (~(delay 0) n, x) ]> )
        xs
    ]>

<[ example2 (n,xs) =
   ~(mapA <[ \x-> (~(delay 0) n, x) ]> ) xs ]>
\end{verbatim}


-- from Hughes' "programming with Arrows"

mapC :: ArrowChoice arr => arr (env,a) b -> arr (env,[a]) [b] mapC c = proc (env,xs) ->
case xs of [] -> returnA -< [] x:xs’ -> do y <- c -< (env,x)
ys <- mapC c -< (env,xs’) returnA -< y:ys

example2 = proc (n,xs) -> (| mapC (\x-> do delay 0 -< n
&&& do returnA -< x) |) xs
-}
