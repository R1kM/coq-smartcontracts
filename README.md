# coq-smartcontracts

The goal of this project is to use Coq to model smart contracts written in [Solidity](https://www.ethereum.org/token), developped by the [Ethereum fondation](https://www.ethereum.org).

A compiler from Solidity to Coq can be found in the Compiler folder. It requires OCaml and Menhir.
To install it, run 'make'.
Then, run 'solidity-coq' on any solidity file with a .sol extension.

A Docker image is also provided, with this compiler already installed. Just run sh launch\_docker.sh, and type 'cd /home/Compiler'

This compiler assumes that the Solidity program given as an input is a valid Solidity program.

The grammar supported is defined in solidity-grammar-subset. 
The main Solidity features which are not supported are the following :
* Several contracts, and inheritance
* Enums structures

Several solidity programs can be found in the Compiler/tests folder, extracted from [Etherscrape](http://etherscrape.com/solidity/download). Programs correct according to Solidity are in the success folder, programs failing solidity compilation are in the fail folder.


It is possible to add annotations in Solidity contracts to automatically generate lemmas and theoremes to ensure these properties. At the moment, we only support annotations expressing preservation properties.
To express that a state variable `v` is preservered throughout any execution of the contract, one has to write the annotation
`@preservation(v)`
It is also possible to express that the sum of an evaluation function on all pairs (key, value) in a mapping is preserved. For instance, if we have a mapping `balance` containing the amount of money each user owns, we can write the annotation `@preservation(balance, fun(key, value) = value)` to express that the sum of all values stored in the mapping, i.e. the total amount of money remains constant.

Examples of the compilation from Coq to Solidity can be found in the Ballot, Auction and MyToken folders.
