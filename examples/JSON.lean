import Soda.Grape
import Soda.Grape.Text

open Grape
open Function

inductive JSON where
  | arr : List JSON → JSON
  | num : Nat → JSON
  | str : String → JSON
  | obj : List (String × JSON) → JSON
  deriving Inhabited

def JSON.token : Grape α → Grape α := Text.trailing

def JSON.pool : Grape Bool :=
      ((const Unit true) <$> string "true")
  <|> ((const Unit false) <$> string "false")

def JSON.pString : Grape String :=
  string "\"" *> Text.takeToStr (· != 34) <* string "\""

def JSON.number : Grape Nat :=
  Text.number

partial def JSON.expr : Grape JSON := token $
        (str <$> label pString "string")
    <|> (num <$> label number "number")
    <|> (arr <$> (string "[" *> sepBy expr (token $ string ",") <* (token $ string "]")))
    <|> (obj <$> (string "{" *> sepBy pair (token $ string ",") <* (token $ string "}")))
  where
    pair := Prod.mk <$> (JSON.pString <* (token $ string ":")) <*> expr
