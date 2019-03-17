# Mini-C Compiler

Compiler for a simplified version version of C (called Mini-C), developed in OCaml.

It was developed as a project for a Compilers course (INF564) at École Polytechnique.

## Compile

To generate the compiler, do:
```
$ make
```
This will generate a ``mini-c`` file

## Run

To compile and run a ``.c`` file with the Mini-C Compiler, using the ERTL Interpreter, do:

```
$ ./mini-c test.c
$ gcc test.s -o test -no-pie
$ ./test
```

## Tests

To run the tests with the ERTL Interpreter, do:
```
$ cd tests
$ ./run -i "../mini-c --interp-ertl"
```


### *Developed by:*

*[Eduardo Caldas](https://github.com/eduucaldas)*

*[Gabriel Oliveira](https://github.com/gabrieloliveiragom)*
