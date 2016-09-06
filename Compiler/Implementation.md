This file is an overview of the implementation, and aims at explaining different choices.

Our compiler assumes that the Solidity code given as an input is correct. It is implemented in OCaml, and relies on ocamllex for the lexical analysis, and Menhir for the parsing phase. We only support a subset of the Solidity language, whose grammar is presented in solidity-grammar-subset.

### Global state
We define the *global state* of the contract as the collection of its state variables. A property on the contract is a property on the state variables. We group them in a Coq `Record`, which is a structure in another languages. This global state changes during the execution of functions. To model this, we give a global state as an input, and get one as an output for each Solidity function.

The global state also consists of a map called `ether`, which models the current ether balances of all Ethereum accounts, and the current amount of gas available. Our gas model is currently very simple, as explained below. Gas and ether are also an input and an output of each function.

### Message and Send function
A function call by an user corresponds to a message in the Ethereum Virtual Machine. We are only interested on the identity of the sender, the amount of ether sent, and the current amount of gas. We decided to separate gas from the message in our model, and group the sender and the quantity of ether in a Record `Message`. The message is given as an input for each function.

We also model the Solidity send function. Given that the gas limit in Solidity only allows the send function to log an event, which does not change anything in our global state, we consider that the send function can only have two behaviours: The sender does not have enough ether, and false is returned without changing anything, or ether is sent, the ether balances change and true is returned. We do not model `call.value` yet, and thus do not model possible reentrancy.

### Gas consumption
Coq does not allow general recursion, one has to ensure that each recursive program terminates. Solidity ensures that programs always terminate using gas. A finite amount of gas is given by a user when calling a function. This amount decreases at each executed instruction. If a program runs out of gas, an exception is raised, and the Ethereum Virtual Machine rolls back to the previous state.

We currently have a simple gas model: We decrease by one the amount of gas at each function called. It is complementary to the Solidity compiler, and allows to detect possible recursion issues leading to out of gas exceptions. We let the user check that non-recursive function do not consume too much gas using the official Solidity compiler.

### Modifiers
To avoid control flow issues, we only allow modifiers as decorators, that is, of the following form.
```
modifier :=
statements;
_
```
When a modifier is associated with a function, we add the statements before the code generation.

### Loops
We model loops as auxiliary recursive functions. When we reach a loop in a function, we collect all variables currently in scope, and pass them in a Record to the auxiliary function with the global state, ether balances and current gas. This auxiliary function is modeled as an usual function, and thus decreases the amount of gas normally. We finally return all the variables in context in a Record and update them in the initial function, as well as the global state, gas and ether balances.

### Mappings
We use Map in Coq to model mappings. A mapping in Solidity returns an object with a 0-byte representation if the key is not initialized, while Coq returns an option. We thus generate accessors and mutators for mappings to translate options to objects and the contrary.
