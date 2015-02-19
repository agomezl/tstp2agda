{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Parser
-- Author : Alejandro Gómez Londoño
-- Date   : Wed Feb 11 00:25:33 2015
-- Description : TSTP parsec parser
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------


module TSTP.Parser where

import Control.Applicative ((*>), (<$>), (<*), (<*>))
import Data.TSTP
import Text.Parsec ((<|>), alphaNum, char, digit, lower, space,
                    many, noneOf, oneOf, string, parseTest)
import qualified Text.Parsec as P (spaces)
import Text.Parsec.ByteString (Parser)
import Data.ByteString.Char8 (pack)
import Text.Parsec (choice)
import Text.Parsec (upper)
import Text.Parsec (try)
import Text.Parsec (sepBy1)


tptpInput ∷ Parser F
tptpInput = fofAnnotated <|> cnfAnnotated

infixr 5 ▪,▸,▸▪,▪◂,▸▪◂

(▸) ∷ Parser String → Parser String → Parser String
a ▸ b = (++) <$> a <*> b

(▪) ∷ Parser String → Parser String → Parser String
a ▪ b = a ▸ spaces ▸ b

(▸▪) ∷ Parser String → Parser String → Parser String
a ▸▪ b = spaces ▸ a ▪ b

(▪◂) ∷ Parser String → Parser String → Parser String
a ▪◂ b = a ▪ b ▸ spaces

(▸▪◂) ∷ Parser String → Parser String → Parser String
a ▸▪◂ b = a ▸▪ spaces ▪◂ b ▸ spaces

spaces ∷ Parser String
spaces = (space >> many space >> return " ") <|> return ""

runTest :: String -> IO ()
runTest = parseTest formulaName . pack

-----------------
-- FOF formulae
-----------------
fofAnnotated ∷ Parser F
fofAnnotated = do
  _ ← string "fof" >> char '('
  F Fof <$> formulaName <* char ','
        <*> formulaRole <* char ','
        <*> fofFormula
        <*> formulaAnnotation

formulaName  ∷ Parser String
formulaName = _word <|> _integer

_word         = _lowerWord <|> _singleQuoted
_integer      = (:) <$> oneOf "123456789" <*> many digit
_lowerWord    = (:) <$> lower <*> many (alphaNum <|> char '_')
_singleQuoted = char '\'' *> many (noneOf "'\\") <* char '\''
_doubleQuoted = char '"' *> many (noneOf "'\\") <* char '"'
variable      = (:) <$> upper <*> many (alphaNum <|> char '_')


formulaRole ∷ Parser Role
formulaRole = spaces >> roles
  where roles = (try string "axiom" >> Axiom) <|>
                (try string "hypothesis" >> Hypothesis) <|>
                (try string "definition" >> Definition) <|>
                (try string "assumption" >> Assumption) <|>
                (try string "lemma" >> Lemma) <|>
                (try string "theorem" >> Theorem) <|>
                (try string "conjecture" >> Conjecture) <|>
                (try string "negated_conjecture" >> NegatedConjecture) <|>
                (try string "plain" >> Plain) <|>
                (try string "fi_domain" >> FiDomain) <|>
                (try string "fi_functors" >> FiFunctors) <|>
                (try string "fi_predicates" >> FiPredicates) <|>
                (try string "type" >> Type)


--fofFormula = undefined

fofFormula ∷ Parser String
fofFormula = fof_logic_formula <|> fof_sequent
  where
    fof_sequent         = undefined
    fof_logic_formula   = fof_binary_formula  <|> fof_unitary_formula
    fof_binary_formula  = fof_binary_nonassoc <|> fof_binary_assoc
    fof_binary_nonassoc = fof_unitary_formula ▸▪ binary_connective ▪◂ fof_unitary_formula
    fof_binary_assoc    = fof_or_formula <|> fof_and_formula
    fof_or_formula      = fof_unitary_formula ▸▪ string "|" ▪◂ fof_unitary_formula <|>
                          fof_or_formula      ▸▪ string "|" ▪◂ fof_unitary_formula
    fof_and_formula     = fof_unitary_formula ▸▪ string "&" ▪◂  fof_unitary_formula <|>
                          fof_and_formula     ▸▪ string "&" ▪◂ fof_unitary_formula
    fof_unitary_formula = fof_quantified_formula <|>  fof_unary_formula <|>
                          atomic_formula <|>
                          string "(" ▸▪ fof_logic_formula ▪◂ string ")"
    fof_quantified_formula = fol_quantifier ▸▪
                             string "[" ▪ fof_variable_list ▪ string "]" ▪
                             string ":" ▪◂ fof_unitary_formula
    fol_quantifier     = string "!" <|> string "?"
    fof_variable_list  = variable <|> variable ▸▪ string "," ▪◂ fof_variable_list
    fof_unary_formula  = (string "~"  ▸▪◂ fof_unitary_formula) -- <|> fol_infix_unary
    binary_connective  = choice $ map string ["<=>","=>","<=","<~>","~|" "~&"]
    constant           = _word
    functor            = _word

    atomic_formula     = plain_atomic_formula <|> defined_atomic_formula <|>
                         system_atomic_formula
    plain_atomic_formula = constant <|>
                           functor ▸ string "(" ▪ arguments string ▪◂ string ")"
    arguments = term <|> term ▸▪ string "," ▪◂ arguments
    term     = function_term <|> variable
    function_term = plain_atomic_formula

formulaAnnotation ∷ Parser String
formulaAnnotation = string "," ▪ source ▪ optional_info <|> return ""
  where
    source = sepBy1 general_data (char ':') <|> general_list
    general_terms = sepBy1 source (char ',')
    general_data = _word <|>
                   _word ▸▪ string "(" general_terms ▪◂ string ")" <|>
                   variable <|>
                   _integer <|> --TODO: Add all the possible numeric values
                   string "$fof(" ▪ fofFormula ▪◂ string ")"
    general_list = try string "[]" <|> string "[" ▸▪ general_terms ▪◂ string "]"


cnfAnnotated ∷ Parser F
cnfAnnotated = undefined
