

sample1 =
  ga_copy          >>>
  ga_swap          >>>
  ga_first ga_drop >>>
  ga_cancell

-- from the paper
sample2 =
  ga_uncancelr                >>>
  ga_first ga_copy            >>>
  ga_swap                     >>>
  ga_second (ga_first ga_drop >>>
             ga_cancell)      >>>
  ga_cancell

