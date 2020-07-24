#  Frama-C-MPI-V

This is the *MPI-V (Message Passing Interface Verifier)* plug-in of *Frama-C*.

## Message Passing Interface

TODO : Short introduction on MPI.

## Verification

TODO : Short presentation on the performed verification

## Installation

* MPI-V v0.0.0* requires [Frama-C v21.1+dev (Scandium)](https://frama-c.com/download.html). For more information see [Frama-C](http://frama-c.com).

For installation, run following commands in the *RPP* directory:

        make
        make install

## Usage

- For command ligne interface:

            frama-c -mpi-v file.c

- For graphic user interface (call from terminal):

            frama-c-gui -mpi-v file.c
