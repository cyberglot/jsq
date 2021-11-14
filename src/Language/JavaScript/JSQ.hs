{- |
Module      :  Language.JavaScript.JSQ
Copyright   :  (c) April Gonçalves, 2021. Gershom Bazerman, 2010.
License     :  BSD 3 Clause
Maintainer  :  @cyberglot
Stability   :  experimental

Simple DSL for lightweight (untyped) programmatic generation of JavaScript.

A number of examples are available in the source of "Language.JavaScript.JSQ.Prelude".

usage:

> renderJs [jsq|fun id x -> x|]

The above produces the id function at the top level.

> renderJs [jsq|var id = \x -> x;|]

So does the above here. However, as id is brought into scope by the keyword var, you do not get a variable named id in the generated javascript, but a variable with an arbitrary unique identifier.

> renderJs [jsq|var !id = \x -> x;|]

The above, by using the bang special form in a var declaration, produces a variable that really is named id.

> renderJs [jsq|function id(x) {return x;}|]

The above is also id.

> renderJs [jsq|function !id(x) {return x;}|]

As is the above (with the correct name).

> renderJs [jsq|fun id x {return x;}|]

As is the above.

> renderJs [jsqE|foo(x,y)|]

The above is an expression representing the application of foo to x and y.

> renderJs [jsqE|foo x y|]]

As is the above.

> renderJs [jsqE|foo (x,y)|]

While the above is an error. (i.e. standard javascript function application cannot seperate the leading parenthesis of the argument from the function being applied)

> \x -> [jsqE|foo `(x)`|]

The above is a haskell expression that provides a function that takes an x, and yields an expression representing the application of foo to the value of x as transformed to a JavaScript expression.

> [jsqE|\x ->`(foo x)`|]

Meanwhile, the above lambda is in JavaScript, and brings the variable into scope both in javascript and in the enclosed antiquotes. The expression is a JavaScript function that takes an x, and yields an expression produced by the application of the Haskell function foo as applied to the identifier x (which is of type JExpr -- i.e. a JavaScript expression).

Other than that, the language is essentially JavaScript (1.5). Note however that one must use semicolons in a principled fashion -- i.e. to end statements consistently. Otherwise, the parser will mistake the whitespace for a whitespace application, and odd things will occur. A further gotcha exists in regex literals, whicch cannot begin with a space. @x / 5 / 4@ parses as ((x / 5) / 4). However, @x /5 / 4@ will parse as x(/5 /, 4). Such are the perils of operators used as delimeters in the presence of whitespace application.

Additional features in jsq include an infix application operator, and an enhanced destructuring bind.

Additional datatypes can be marshalled to JavaScript by proper instance declarations for the ToJExpr class.

-}

module Language.JavaScript.JSQ
  ( module Language.JavaScript.JSQ.QQ
  , module Language.JavaScript.JSQ.Base
  , module Language.JavaScript.JSQ.Prelude
  , module Language.JavaScript.JSQ.Types
  )
where

import Language.JavaScript.JSQ.Base
    ( ToStat(..),
      ToJExpr(..),
      JsToDoc(..),
      Compos(..),
      JSQGadt(..),
      JSQ(..),
      Ident(..),
      SaneDouble(..),
      JVal(..),
      JExpr(..),
      JsLabel,
      JStat(..),
      IdentSupply(..),
      composOp,
      composOpM,
      composOpM_,
      composOpFold,
      jsSaturate,
      withHygiene,
      scopify,
      renderJs,
      renderPrefixJs,
      jLam,
      jVar,
      jVarTy,
      jForIn,
      jForEachIn,
      jTryCatchFinally,
      jsv,
      jFor,
      jhEmpty,
      jhSingle,
      jhAdd,
      jhFromList,
      jtFromList,
      nullStat )
import Language.JavaScript.JSQ.QQ
    ( jsq, jsqE, parseJSQ, parseJSQE )
import Language.JavaScript.JSQ.Prelude ( jsqPrelude )
import Language.JavaScript.JSQ.Types (JType(..))
