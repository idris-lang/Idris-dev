data Tag : String -> List String -> Type where
  TZ : Tag l (l :: e)
  TS : Tag l e -> Tag l (l' :: e)

SPi :  (e : List String)
    -> ((l : String) -> Tag l e -> Type)
    -> Type
SPi []       _    = ()
SPi (l :: e) prop = (prop l TZ, SPi e $ \l' => \t => prop l' $ TS t)

switch :  (e : List String)
       -> (prop : (l : String) -> (t : Tag l e) -> Type)
       -> SPi e prop
       -> (l' : String) -> (t' : Tag l' e) -> prop l' t'
switch (l' :: e) prop ((propz, props)) l' TZ      = propz
switch (l  :: e) prop ((propz, props)) l' (TS t') =
  switch e (\l => \t => prop l (TS t)) props l' t'
