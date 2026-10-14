# Batch 065 exclusive-log failure and repair readback

Rust integration lane, 14 October 2026 UTC. Read-only review; no compiler, test, capture mutation, repair or launch by this reviewer.

The actual guard `401fa941b79362f254e03f51bfd5e2c14dceae32e74c16833157bbeca75e8c8a` records exit 1, no resource stop, 7.507 seconds and 32,182,272 peak child RSS bytes. Both guard log hashes match. Capture `5ef0c5c24f41c7615ecaf16aff8ed66fbab2cc91605ec3dd47a27e7cac86c998` binds that guard and its prebatch inventory, with no completed or changed eventless invocation records.

The retained traceback reports `FileExistsError` opening `3036.stdout` exclusively. The unchanged shared helper `d47f2d50afd4648374d7ca1630dce71f3aa09422fe740d356b2d0d9c8ce8ca28` opens stdout/stderr at line 52; its compiler `Popen` occurs at line 53. This authenticates failure before the compiler launch in this attempted invocation. No mathematical failure or successful module is inferred.

Repair record `63cff91c6e0e59ac5cf39e533113236cdfeee03a1fd0282b827ad3e3e47fe78d` records moving only the two empty logs retained from interrupted batch064 to `preserved-interrupted-3036-before-066`, after making public evidence copies. Both archived files and both public copies match length zero and SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. The original occupied paths are absent at this readback. No3036 module receipt or any of its five object-family files exists.

Original batch064 guard `34cd5cb3e3b015701391e57d25acfed61f1035af4d4bb4163642552f9314eb18` remains byte-exact, with its actual wall-limit interruption unchanged. This scoped repair clears the exclusive-output-name obstruction while preserving evidence; it changes no source, compiler or resource limit and does not itself verify a new compilation. Any separately named continuation belongs to the compiler owner.
