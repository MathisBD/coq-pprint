# What is coq-pprint ?

PPrint is a Coq pretty-printing library in the style of Wadler's "A prettier printer". The combinators are partly based on François Pottier's Pprint library : https://github.com/fpottier/pprint, but the rendering engine is different.

It has the following features :
- well documented : every function has at least a sentence explaining its behaviour.
- handles utf-8 strings properly
- based on primitive strings
- _annotated_ text : the user can box pieces of text in an annotation of any type. Examples of annotations include colors or typographical emphasis (bold, italic, underline, etc). It is up to the user to choose the type of annotations, depending on their needs. Annotations have no effect on text layout : to print to plain text we can simply ignore all annotations.
- multiple backends : the rendering engine is not limited to outputting plain strings. It is parameterized by a pretty-printing monad, which handles the output details as well as annotations. This makes it possible to render documents to e.g. markdown or HTML.

# Getting started
 
Read the [quick-start](https://github.com/MathisBD/coq-pprint/blob/master/tutorials/QuickStart.v) if you are in a hury, and the [tutorial](https://github.com/MathisBD/coq-pprint/blob/master/tutorials/Tutorial.v) if you have more time.

# Installation 

This package is available on [OPAM](https://opam.ocaml.org/). Activate the Coq repository : 
```
opam repo add coq-released https://coq.inria.fr/opam/released
```
And install the package : 
```
opam install coq-pprint
```

# Code structure

- Documents.v : exposes the document type `doc A` and document combinators.
- Rendering.v : implements the rendering algorithm, which works with respect to a pretty-printing monad `MonadPPrint A`.
- Monad.v : a tiny monad library. Eventually we should use a proper monad library.
- Utils.v : utility functions, which are not exported in the library's API.