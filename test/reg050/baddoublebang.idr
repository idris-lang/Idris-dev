module baddoublebang

-- Check that two bang bindings running together don't work

doubleBang : Maybe (Maybe Nat) -> Maybe Nat
doubleBang mmn = do pure !!mmn

