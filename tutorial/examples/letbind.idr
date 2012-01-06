module letbind;

mirror : List a -> List a;
mirror xs = let xs' = rev xs in
                app xs xs';

data Person = MkPerson String Int;

showPerson : Person -> String;
showPerson p = let MkPerson name age = p in
                   name ++ " is " ++ show age ++ " years old";

