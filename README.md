`plugin-constraint` is a GHC source plugin which demonstates two common tasks
which need to be achieved when writing a source plugin.

1. How to interact with the constraint solver.
2. How to generate `HsExpr GhcTc`.

Both of these are not obvious!

We also demonstrate four different ways in order to build an `HsExpr GhcTc`.

1. `mkNewExprTc` - Directly constructing an `HsExpr GhcTc`.
2. `mkNewExprRn` - Building from `HsExpr GhcRn`
3. `mkNewExprPs` - Building from `HsExpr GhcPs`
4. `mkNewExprTh` - Using a template haskell quasiquote

These methods are ordered from the least convient to the most convenient
but different approaches might work better for different tasks.

All the plugin actually does is insert a single new binding.

```
myBinding = print ()
```

We first find the `Show` instance for `()`. This is done
by the `generateDictionary` function which returns the variable which the dictionary
will be bound to and the dictionary itself.
We then demonstrate in `mkNewExprTc` how to *directly* use this dictionary by using it to create
the new binding. A type checked term uses `HsWrap` constructors to apply type
arguments, dictionaries and to bind dictionaries. Thus, we insert an `HsWrap`
constructor around the `print` function which instantiates the type variable
`a` to `()`, passes the dictionary variable and then wraps the function with the evidence.

By using `mkNewExprRn`, it isn't necessary to directly apply the `HsWrap` ourselves
as it is something the compiler inserts during type checking. In this function
it is necessary to lookup the name you want to use by using
functions from `RnEnv`. Performing actions usually performed by the renamer.

In `mkNewExprPs`, we make code as would be produced by the parser. It's necessary
to be careful when making `OccName`s so that they have the right namespace.

In `mkNewExprTh`, we use a TH quote in order to generate a `HsExpr GhcPs`. This
is very convenient because you can write actual Haskell source code



