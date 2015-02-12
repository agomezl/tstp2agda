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
import Text.Parsec ((<|>), alphaNum, char, digit, lower,
                    many, noneOf, oneOf, string, parseTest)
import Text.Parsec.ByteString (Parser)
import Data.ByteString.Char8 (pack)


tptpInput ∷ Parser F
tptpInput = fofAnnotated <|> cnfAnnotated


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
  where
    _word         = _lowerWord <|> _singleQuoted
    _integer      = (:) <$> oneOf "123456789" <*> many digit
    _lowerWord    = (:) <$> lower <*> many (alphaNum <|> char '_')
    _singleQuoted = char '\'' *> many (noneOf "'\\") <* char '\''

formulaRole ∷ Parser Role
formulaRole = undefined
-- formulaRole = fof_logic_formula <|> fof_sequent
--   where
--     fof_sequent         = undefined
--     fof_logic_formula   = fof_binary_formula  <|> fof_unitary_formula
--     fof_binary_formula  = fof_binary_nonassoc <|> fof_binary_assoc
--     fof_binary_nonassoc = (++) <$> fof_unitary_formula
--                           <*> (++) <$> binary_connective <*> fof_unitary_formula
--     fof_binary_assoc    = fof_or_formula <|> fof_and_formula
--     fof_or_formula      = fof_unitary_formula vline fof_unitary_formula |
--       fof_or_formula vline fof_unitary_formula
--     fof_and_formula    = fof_unitary_formula & fof_unitary_formula |
--       fof_and_formula & fof_unitary_formula
--     fof_unitary_formula = fof_quantified_formula | fof_unary_formula |
--                          atomic_formula | (fof_logic_formula)fof_quantified_formula ::= fol_quantifier [fof_variable_list] :
--                          fof_unitary_formula
--     fof_variable_list  = variable | variable,fof_variable_list
--     fof_unary_formula  = unary_connective fof_unitary_formula |
--                          fol_infix_unary

fofFormula ∷ Parser String
fofFormula = undefined

formulaAnnotation ∷ Parser String
formulaAnnotation = undefined

cnfAnnotated ∷ Parser F
cnfAnnotated = undefined
