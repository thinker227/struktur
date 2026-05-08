# Roadmap

> [o] indicates that the feature was implemented in the old compiler but is yet to be implemented in the new one.

## Tooling

- [o] Compiler CLI
- [ ] REPL
- [x] VSCode extension/TextMate grammar
- [ ] Language server
- [ ] Debugger

## Compiler

### Frontend

- [x] Parser
- [o] Symbol resolution
  - [o] Top-level binding reference graph
- [ ] Module system
- [ ] Main function
- [ ] Operators
- [ ] Algebraic data types
- [o] Type-checking + inference
  - [o] Bidirectional inference
  - [ ] Constraint-based inference

### Backend

- [o] Decision trees
- [o] CPS conversion
- [o] JS codegen
- [ ] Bytecode VM

### Type system

- [ ] Rank-2 types
- [ ] Higher-kinded types
- [ ] Typeclasses
- [ ] Effect system
- [ ] Lazy type
