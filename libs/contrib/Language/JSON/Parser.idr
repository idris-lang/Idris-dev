module Language.JSON.Parser

import Language.JSON.Data
import Text.Parser
import Text.Token

import public Language.JSON.Tokens

%access private
%default total

punct : Punctuation -> Grammar JSONToken True ()
punct p = match $ JTPunct p

rawString : Grammar JSONToken True String
rawString = do mstr <- match JTString
               the (Grammar _ False _) $
                   case mstr of
                        Just str => pure str
                        Nothing => fail "invalid string"

mutual
  json : Grammar JSONToken True JSON
  json = object
     <|> array
     <|> string
     <|> boolean
     <|> number
     <|> null

  object : Grammar JSONToken True JSON
  object = do punct $ Curly Open
              commit
              props <- properties
              punct $ Curly Close
              pure $ JObject props
    where
      properties : Grammar JSONToken False (List (String, JSON))
      properties = sepBy (punct Comma) $
                         do key <- rawString
                            punct Colon
                            value <- json
                            pure (key, value)

  array : Grammar JSONToken True JSON
  array = do punct (Square Open)
             commit
             vals <- values
             punct (Square Close)
             pure (JArray vals)
    where
      values : Grammar JSONToken False (List JSON)
      values = sepBy (punct Comma) json

  string : Grammar JSONToken True JSON
  string = map JString rawString

  boolean : Grammar JSONToken True JSON
  boolean = map JBoolean $ match JTBoolean

  number : Grammar JSONToken True JSON
  number = map JNumber $ match JTNumber

  null : Grammar JSONToken True JSON
  null = map (const JNull) $ match JTNull

export
parseJSON : List JSONToken -> Maybe JSON
parseJSON toks = case parse json $ filter (not . ignored) toks of
                      Right (j, []) => Just j
                      _ => Nothing
