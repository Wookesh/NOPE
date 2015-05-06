module Preprocess where

getString  (s, _) = s

preprocessInput :: String -> String
preprocessInput s = preprocessLines $ lines s

appendNewline :: String -> String
appendNewline s = s ++ " NEWLINE "

preprocessLines (s:xs) | xs /= [] = (preprocessLine s (countIndent s) (countIndent (head xs))) ++ (preprocessLines xs)
							  | otherwise = preprocessLine' s (countIndent s) 0

preprocessLine :: String -> Integer -> Integer -> String
preprocessLine "" _ _ = ""
preprocessLine s currIndent nextIndent | nextIndent == currIndent = appendNewline (removeIndent s)
														| nextIndent > currIndent = (appendNewline (removeIndent s)) ++ " INDENT "
														| nextIndent < currIndent = appendNewline (addDedent (removeIndent s) (currIndent - nextIndent))

preprocessLine' :: String -> Integer -> Integer -> String
preprocessLine' s currIndent nextIndent | nextIndent == currIndent = removeIndent s
														| nextIndent > currIndent = (removeIndent s) ++ " INDENT "
														| nextIndent < currIndent = addDedent (removeIndent s) (currIndent - nextIndent)

addDedent :: String -> Integer -> String
addDedent s i | i == 0 = s
				  | otherwise = (addDedent s (i - 1)) ++ " DEDENT"

removeIndent :: String -> String
removeIndent [] = []
removeIndent (x:xs) | x == '\t' = removeIndent xs
						  | otherwise = x:xs

countIndent :: String -> Integer
countIndent [] = 0
countIndent (x:xs) | x == '\t' = (countIndent xs) + 1
						 | otherwise = 0