module Pretty.Utils
    ( (<+?>), intercalate
    ) where

import Text.PrettyPrint (Doc, text, punctuate, hcat, fcat, (<>))

infixr 2 <+?>
(<+?>) :: Doc -> Doc -> Doc
x <+?> y = fcat [x, text " " <> y]

intercalate :: Doc -> [Doc] -> Doc
intercalate sep = hcat . punctuate sep
