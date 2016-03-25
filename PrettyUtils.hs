module PrettyUtils
    ( (<+?>)
    ) where

import Text.PrettyPrint (Doc, text, fcat, (<>))

infixr 2 <+?>
(<+?>) :: Doc -> Doc -> Doc
x <+?> y = fcat [x, text " " <> y]
