# Introduction

Sessiontypes is a Haskell library that provides a deep embedded domain-specific language for writing session typed programs.
A session typed program is a program annotated with session types. A session type describes a communication protocol at the type-level.
The motivation for using session types is that it gives you a static guarantee that a program correctly implements a protocol. It may even guarantee
that deadlocking cannot occur in a client-server setting.

# Install

Add `sessiontypes` as a dependency in your `.cabal` file.

# Tutorial

For this tutorial we'll start by defining a trivial session typed program and explain it, then we gradually add extensions and explain those as well.

A fairly trivial session typed program can be defined as follows:

```haskell
{-# LANGUAGE RebindableSyntax #-}
import SessionTypes
import SessionTypes.Indexed

prog :: STTerm m s s Int
prog = return 0
```

For even a basic program we need to do a couple things before we can write it and have it type check.
1. First we have to import the `SessionTypes` module that exports the most essential for writing any session typed program.
2. Then we also import `SessionTypes.Indexed` which is a custom prelude for indexed type classes.
3. The `SessionTypes.Indexed` module is meant to replace `Prelude`. For example, the function `return` belongs to the `IxMonad` type class that can be found in `SessionTypes.Indexed`. Of course this will result in ambiguous function errors, so we add the `RebindableSyntax` pragma.

Option 3 is actually optional. You may also do a qualified import on `SessionTypes.Indexed`.

Now that we have the right imports and set the language pragma can we begin to write a session typed program.
A session typed program is defined in terms of `STTerm`. This is a GADT that is parameterised with a `Monad`, two capabilities (session types) and a `Type`.
`STTerm` is indexed on the two capabilities and hence is also an indexed monad. The first capability is the pre-state and the second capability is the post-state of 
any `STTerm` computation.
For every indexed function that we will use there is a constructor in `STTerm`. For `return` this is `Ret` that simply takes an argument of kind `Type`.
In the above example we define a simple program named `prog` that simply returns the value `0`. Since a `return` is not considered a session typed action, we have
that the indexes of `prog` remain the same.

When we do a session typed action the indexes will be different. For example:

```haskell
prog :: STTerm m ('Cap '[] (Int :!> r)) ('Cap '[] r) Int
prog = send 5 >> return 0
```

Now `prog` first completes a send using the `send` primitive before it once again returns. This is also describes in the session type as `Int :!> r` (we ignore the entire capability for now). This session type says to send a value of type `Int` followed by some undetermined session type. If you were to remove `send 5`, but leave the type as it is, then a type error will be generated. Similarly, if you were to remove `Int :!>` in the session type but left the `send` in the definition of `prog`. This means that a program typed with a send session type will really do a send.
The send function is essentially a wrapper over the `Send` constructor and it has the following type: `a -> STTerm m ('Cap '[] (a :!> r)) ('Cap '[] r) ()`. However, the `Send` constructor has type `a -> STTerm m ('Cap '[] r) r' -> STTerm m ('Cap '[] (a :!> r)) r' ()`. So it actually takes another `STTerm` as an argument. This is the case for all constructors of `STTerm`, except for `Ret`. When we write a session typed program like `prog`, we actually end up writing an abstract syntax tree consisting of the constructors of `STTerm`. That means we are still to apply any semantics to `prog`.


Next we will include a receive and also offer a way to end a protocol:

```haskell
prog :: STTerm m ('Cap '[] (Int :!> Bool :?> Eps)) ('Cap '[] Eps) Bool
prog = send 5 >> recv >>= eps
```

We have added two more session types: `:?>` denoting a receive and `Eps` denoting the end of a session type. By composing the primitives the session types are also composed.
So doing a receive after a send will generate a session type of the form `a :!> b :?> r`. It should be noted that the constructor `Recv` takes a continuation. This is necessary to have `recv` return a value that we will only later be able to define.

You can now write a basic session typed program, but we can't yet apply any meaning to it. For that purpose we defined several interpreters. Here I will only explain the interactive evaluator, but you may find documentation on how to use the other interpreters in their respective modules.

The interactive evaluator lets you run a session, two session typed programs implementing a protocol, where one actor in the session is defined by a session typed program and the other is the user. The interpreter is defined as follows:

```haskell
interactive :: (MonadIO m, HasConstraints '[Read, Show, Typeable] s, Show a) => STTerm m s r a -> m a
interactive (Send _ r) = interactive r
interactive r@(Recv c) = do
    liftIO $ putStr $ "Enter value of type " ++ typeShow r ++ ": "
    ma <- liftIO $ fmap readMaybe getLine
    case ma of
      Nothing -> interactive r
      Just a  -> interactive $ c a
  where typeShow :: forall m ctx a r k b. Typeable a => STTerm m ('Cap ctx (a :?> r)) k b -> String
        typeShow _ = show $ typeRep (Proxy :: Proxy a)
interactive (Ret a)  = return a
```

The interpreter evaluates a program of type `STTerm m s r a` to a program of type `m a`. For the `Send` constructor we do not really need to do anything, since we're not interested in the value that is sent. So we simply do a recursive call on its second argument. For `Recv` we must do a lot more. For a `Recv` we must pass an argument to its continuation to access the rest of the AST. For this interpreter we do so by asking the user to supply a value that we then read, pass to the continuation of `Recv` and then recursively evaluate the result. For `Ret` we simply return the value it contains.

We can now apply this interpreter to `prog` and run it:

```haskell
main = interactive prog

>>> main
> Enter value of type Bool: True
True
```

The above should give the reader of this tutorial a basic idea of how to write a session typed program and subsequently evaluate it using an interpreter. For the next part we will more briefly discuss other session typed primitives and interpreters. More documentation can be found in the modules themselves.

## Branching

Sometimes we want to make a choice which type of value to send depending on some other calculated value. For example:

```haskell
prog = do
  x <- recv
  case x of
    0 -> send True
    n -> send "False"
```

This program will result in a type error, because the types of the branches of the case expression do not unify.
To resolve this we can allow branching in the session types. We have two types of branching:
```haskell
Sel [ST] -- Selection
Off [ST] -- Offering
``` 

Both selection and offering take a list of session types as an argument. A selection selects a single branch to implement, while an offering offers to implement all branches.
```haskell
prog :: STTerm m ('Cap '[] (Int :?> Sel '[Int :!> r, String :!> r])) ('Cap '[] r) ()
prog = do
  x <- recv
  case x of
    0 -> sel1 >> send True
    n -> sel2 >> sel1 >> send "False"
``` 
For selection there are two constructors. The first constructor `Sel1` selects the head of the list of session types to implement. That means that after using a `sel1`, the chosen branch should be implemented. The second constructor `Sel2` skips the head of the list of session types. It does not select a branch, but allows other branches to be selected.

```haskell
progDual :: STTerm m ('Cap '[] (Int :!> Off '[Int :?> r, String :?> r])) ('Cap '[] r) ()
progDual = do
  send 0
  offS recv (offZ recv)
```

An offering must implement all branches as it is leaving the choice to implement a specific branch up to someone else. How this is implemented depends on the interpreter of course. For the interactive interpreter, the user would choose the branch.
For an offering there are also two constructors `OffS` and `OffZ`. `OffS` contains a branch and another offering and `OffZ` contains the very last branch in an offering.

## Recursion

Also recursion requires extra typing. If we were to write a program like this:

```haskell
sendChar = send 'c' >> sendChar
```

Then an infinite type occurrence type error will be generated. 
We add three new session types:

```haskell
R ST -- delimits scope
Wk ST -- weakens scope
V -- recursion variable
```

The `R` session type delimits the scope of recursion. Essentially that means that after an `R` we may recurse at some point. The `Wk` session type is necessary if we have nested recursion and the `V` session type denotes the actual point of recursion.
Now before I further explain how these session types should be used, I'll first define the scope of recursion. The scope of recursion is simply a list of session types that we must also index on. We also refer to the scope of recursion as the context. This is why we define capabilities and have `STTerm` index on these.

```haskell
data Cap = Cap [ST] ST
```
The capability takes the scope of recursion and the session type as an argument.

Now when we say that `R` delimits the scope of recursion, we mean that it adds its session type argument to the top of the context. And the `Wk` session type removes the top of the context. We do this adding and removing, because the `Var` constructor that is annotated by `V` looks at the top of the context and uses that session type as the pre-state of its `STTerm` argument. This means that whatever comes after the `Var` must implement the session type that was at the top of the context.

```haskell
sendChar :: STTerm m ('Cap '[] (R (Char :!> Off '[V, Wk Eps]))) ('Cap '[] Eps) ()
sendChar = recurse go
  where
    go = do
      send 'c'
      offS (var0 >> sendChar) (offZ $ weaken0 >> eps0)
```
In this example we make use of almost all session types. We first delimit the scope of recursion, do a send and then offer to either recurse or leave the recursion followed by ending the protocol. Strictly speaking it isn't necessary to use a weaken here, but without it the context in the post-state would be non-empty. Usually you would want to use a weaken to have the `V` session type recurse back to a different `R`.