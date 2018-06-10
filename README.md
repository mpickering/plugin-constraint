`plugin-constraint` is a GHC source plugin which demonstates two common taks
which need to be achieved when writing a source plugin.

1. How to interact with the constraint solver.
2. How to generate `HsExpr GhcTc`.

Both of these are not obvious!

All the plugin actually does is insert a single new binding.

```
myBinding = print ()
```

In order to do this, we first find the `Show` instance for `()`. This is done
by the `generateDictionry` function which returns the variable which the dictionary
will be bound to and the dictionary itself.

We then demonstrate in `mkNewBinding` how to *directly* use this dictionary by using it to create
the new binding. A type checked term uses `HsWrap` constructors to apply type
arguments, dictionaries and to bind dictionaries. Thus, we insert an `HsWrap`
constructor around the `print` function which instantiates the type variable
`a` to `()`, passes the dictionary variable and then wraps the function with the evidence.



