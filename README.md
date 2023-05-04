> **Warning**
> I feel it goes without saying but, although it may prove useful to others as a pedagogical ressource, **this project is very much a toy, has not received any security audit, and should under no circumstances be used as the basis of anything serious**.

# BrainPlonk

BrainPlonk is a zero-knowledge BrainFuck VM, designed as a custom, STARK-inspired version of PlonkUp. I have written it for learning purposes only, out of a desire to gain a deeper, detailed understanding of Plonk and VM arithmetization.

## The protocol

The protocol is based on PlonkUp, modified to represent a computation as the time evolution of registers state, rather than as a static arithmetic circuit. The design is inspired by STARK arithmetization, and in particular by BrainSTARK [5]: https://aszepieniec.github.io/stark-brainfuck/, but it is still absolutely Plonkish.  

### Validating register state across instructions execution

The evolution of the registers of the virtual machine is constrained according to which instruction is being executed. The only difficulty (apart from ensuring that the evolution is not underconstrained) is in the latter part: switching on the instruction being executed. This is done in BrainPlonk by populating pseudo-selectors $q_{inst} \in \{0, 1\}$, and ensuring via a lookup argument that at all times, the current instruction and all the pseudo-selectors are coherent (with only one pseudo-selector being non-zero, corresponding to the current instruction). This solution has the disadvantage of making the witness larger, but unlike the alternative used in [5] for instance, namely deselector polynomials, it has the advantage of keeping the constraint polynomial degree low, which is very important performance-wise.

### Validating memory consistency

Apart from the registers, we of course also have to deal with memory. The main problem consists in verifying that memory behaves consistently (essentially meaning that at any point the value read is the last to have been written) and has been initialized correctly. Following [5], this is done by lexicographically ordering the list of memory manipulations according to the memory adress and clock cycle. The tricky part then lies in properly enforcing this ordering. Here we depart again from the solution adopted in [5], where dummy cycles have to be inserted everywhere so that the clock can always be constrainted to only stay constant or grow by one, and we instead allow the clock to grow by any amount via a lookup argument.

### Validating program text and IO

Finally, we have to enforce that the expected program has been executed on the correct inputs, and has indeed produced to claimed outputs. The program text verification can be seen as a lookup argument, but the IO validation is less amenable to it. We therefore follow [5] and use a very similar technique than Plonk's Grand Product argument, but instead using a summation over distinct monomials in a challenge scalar. This allows to check that the inputs seen by the program are the inputs given in the (public) input table, in the right order (and similarly for the outputs).

## References

I have found the following ressources extremely useful to understand plonkish protocols, and zkVM arithmetization:  
[1]. "Notes on Plonk Prover’s and Verifier’s Algorithm": https://hackmd.io/@aztec-network/ByiUK_Plt  
[2]. "From AIRs to RAPs - how PLONK-style arithmetization works": https://hackmd.io/@aztec-network/plonk-arithmetiization-air  
[3]. "Multiset checks in PLONK and Plookup": https://hackmd.io/@arielg/ByFgSDA7D  
[4]. "HVZK Fix in Plonk Prover": https://hackmd.io/@aztec-network/rkvxEyd9q  
[5]. The BrainSTARK tutorial: https://aszepieniec.github.io/stark-brainfuck/  
[6]. And of course the PlonkUp paper (although beware, there are quite a few typos in there): https://eprint.iacr.org/2022/086