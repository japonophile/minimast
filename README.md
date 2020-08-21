# minimast

A faster metamath parser written in Rust.

## Goal

Parse & verify set.mm faster than the C metamath parser.

How: focus on speed and resource utilization.

## Result

Found there is a big difference between debug mode and release mode.

Here is the result in debug mode:

    $ cargo run mm/set.mm
    Reading source file "mm/set.mm"... 35167786 bytes
    35167786 bytes were read into the source buffer.
    The source has 147428 statements; 2325 are $a and 33601 are $p.
     . Program parsed in 23.308374187s
    OK
    Verifying 33601 proofs...
     . Proofs verified in 117 seconds.
    Done

Not really fast.

But when running in release mode... tadaaam:

    $ cargo run --release mm/set.mm
    Reading source file "mm/set.mm"... 35167786 bytes
    35167786 bytes were read into the source buffer.
    The source has 147428 statements; 2325 are $a and 33601 are $p.
     . Program parsed in 1.715832611s
    OK
    Verifying 33601 proofs...
     . Proofs verified in 21 seconds.
    Done

For reference, the original metamath program (written in C) reads, parses and checks the file in 1 sec.  And it verifies all proofs in less than 10 seconds.

    $ ./metamath set.mm
    Metamath - Version 0.179 29-Nov-2019          Type HELP for help, EXIT to exit.
    MM> READ "set.mm"
    Reading source file "set.mm"... 35167786 bytes
    35167786 bytes were read into the source buffer.
    The source has 164615 statements; 2325 are $a and 33601 are $p.
    No errors were found.  However, proofs were not checked.  Type VERIFY PROOF *
    if you want to check them.
    MM> VERIFY PROOF *
    0 10%  20%  30%  40%  50%  60%  70%  80%  90% 100%
    ..................................................
    All proofs in the database were verified in 9.83 s.
    MM>

