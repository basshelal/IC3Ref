# IC3Ref

Taken from: https://github.com/arbrad/IC3ref

## Building

Tested only on GNU/Linux (Arch Linux) but should work on any Unix-like system

### Requirements

* `bash` (to run scripts)
* `git` (to clone)
* `make` (to make project)
* `g++` or a compatible C++ compiler such as `clang` (for `make` to use to compile source files)

### Instructions

Clone this repository:
```bash
git clone https://github.com/basshelal/IC3Ref.git
cd IC3Ref/
```

Run the convenience build script:
```bash
./build.sh
```

There should now be a binary named `ic3`, you can check that it is valid using:
```bash
readelf -h ./ic3
```
which should print some information about the binary.

Run the program using:
```bash
./run.sh <FILE>
```
where `<FILE>` is the path to the aiger file to run ic3 on, this can be in either .aag or .aig 
format and can be using the aiger format version 1.9. 

You can clean the project (for a fresh build) using the convenience script:
```bash
./clean.sh
```