module DefaultArgUnknownName

-- FIXME: What is the expected behaviour here? Should the type declaration
-- not compile?
funWithBadDefArg : { default sadgjhsag arg : () } -> ()
funWithBadDefArg = ()

test : ()
test = funWithBadDefArg

