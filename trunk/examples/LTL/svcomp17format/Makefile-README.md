# SV-COMP C Benchmark Makefile build system

The C Benchmarks come with a Makefile build system designed to make it
easy to check that sources can be compiled.

The build system currently support Clang and GCC compilers.

# Useful Makefile variables

There are a few Makefile variables that can be set from the command line
that are worth knowing about

* ``CC`` - The C compiler to use
* ``EMIT_LLVM`` - **Clang only** If ``1`` emit LLVM bitcode files. If
                  ``0`` emit native object files. This is useful if a
                  verification tool takes LLVM bitcode as input.
* ``PREFER_I_FILES`` - When two source files exist with the same name
                       (e.g. ``foo.c`` and ``foo.i``) decide which to
                       use. If ``1`` the ``*.i`` file will be used. If
                       ``0`` the ``*.c`` file will be used.
* ``REPORT_CC_FILE`` - If ``1`` report the file being compiled on
                       standard output. If ``0`` do not report.
                       If ``2`` report compilation in a way that keeps
                       output small which is useful for the TravisCI build
                       which sets a limit of the log size.
* ``SET_FILES`` - See "Set files mode" section.
* ``SUPPRESS_WARNINGS`` - If ``1`` suppress all compiler warnings. If
                          ``0`` do not suppress compiler warnings and
                          pass warning flags as set in ``Makefile.config``.
* ``SYNTAX_ONLY`` - If ``1`` the compiler will only do a syntax check
                    and will not create real object files. If ``0``
                    the compiler will create real object files. This
                    option is ignored if ``EMIT_LLVM`` is enabled.
* ``VERBOSE`` - If ``1`` be more verbose, if ``0`` do not.
e.g.

```
$ make CC=clang VERBOSE=1
```
See ``Makefile.config`` for the default values.

# Building the benchmarks

Benchmarks are built "out of source" in a directory called ``bin/`` in
the top level directory. The contents of ``bin/`` mirrors the structure of
the sources.

## All benchmarks

From the top level directory (i.e. the directory containing ``Makefile.config``)
run

```
$ make
```

Remember to pass ``-j<N>`` to build multiple benchmarks in parallel (where
``<N>`` is the number of jobs).

## All benchmarks in a directory

To build all benchmarks in particular directory (and in its children)

```
$ cd <DIR>
$ make
```

where ``<DIR>`` is the directory you wish to build

## A single benchmark

To build a particular benchmark run

```
$ cd <DIR>
$ make <NAME>.<OBJ_SUFFIX>
```

where ``<DIR>`` is the directory containing the benchmark, ``<NAME>``
is the name of benchmark without a suffix and ``<OBJ_SUFFIX>`` is
``oc`` if you wish to build from ``<NAME>.c`` or ``oi`` if you wish to
build from ``<NAME>.i``. Tab completion is your friend here.

Here's some concrete examples:

This uses ``standard_copy5_true-unreach-call_ground.i`` as the source
file.

```
$ cd array-examples/
$ make standard_copy5_true-unreach-call_ground.oi
```


This uses ``standard_copy5_true-unreach-call_ground.c`` as the source
file.

```
$ cd array-examples/
$ make standard_copy5_true-unreach-call_ground.oc
```

## Cleaning

To remove build files run

```
$ make clean
```

If run from the top-level directory this will clean all build files. If run
from a sub directory it will only clean all build files relevant to that directory
and its child directories.

# Adding a new benchmark

Simply add the benchmark (``*.c`` or ``*.i`` file) to a directory of your
choice and the build system will detect it automatically.

# Adding a new benchmark directory

In these instructions replace ``<DIR>`` with the directory name you wish to add

1. Create the new directory
   ```
   $ mkdir <DIR>
   ```
2. Add a ``Makefile`` in ``<DIR>``. The most basic ``Makefile`` is
   ```
   LEVEL := <REL_PATH>
   include $(LEVEL)/Makefile.config
   ```

   Where ``<REL_PATH>`` is the prefix required to access the ``Makefile.config``
   file from ``<DIR>``. E.g. ``../``

# The contents of a ``Makefile``

A ``Makefile`` in each directory will automatically add targets for all C
source files (``*.c`` and ``*.i``) implicitly unless ``SKIP_LEVEL`` is defined.
If a file exists with the same prefix (e.g. ``foo.c`` and ``foo.i``) the file
used for compilation is determined by the value of ``PREFER_I_FILES``.  The
decision to make declaring source files implicit is a practical decision
because it would be very cumbersome to specify all the benchmarks given the
large number in the repository. It also means that no modifications to the
build system are required when addng a new source file.

If for some reason some sources need to be ignored you should add them to the
``IGNORE_SRCS`` variable.

```
IGNORE_SRCS := file1.c file2.c file3.c file4.i
```

A `Makefile` will also implicitly traverse sub directories relative to
the `Makefile` when processing the `all` target (the default target).
If for some reason some directories need be ignored you should add them
to the `IGNORE_DIRS` variable.

```
# Ignores directories `foo/` and `bar/`
IGNORE_DIRS := ./foo/ ./bar/
```

If you need to modify the flags passed to the compiler you can do so here.
For example

```
CC.Flags := -g
```

Will add the ``-g`` flag to the compilations flags. **Note: Sub directories
will inherit the values of ``CC.Flags`` when makefile recursion happens so you
need to be very careful when setting this variable.**

Every ``Makefile`` must declare ``LEVEL`` which is a relative path prefix
to access the top-level directory.

Every ``Makefile`` must end with the line

```
include $(LEVEL)/Makefile.config
```

# Disable warnings for some directory

By default all compiler warnings trigger an error.
To disable this behavior for some warning, add one of the following lines
to the `Makefile` in the respective directory,
depending on which compiler issues the warning:

```
COMMON_WARNINGS := -Wno-error=<warning>
GCC_WARNINGS := -Wno-error=<warning>
CLANG_WARNINGS := -Wno-error=<warning>
```

To silence the warning completely such that it is not shown,
use `-Wno-<warning>` instead of `-Wno-error=<warning>`.
This may be necessary to reduce the amount of output to a reasonable level.

To disable and silence all warnings completely in a directory,
add the following line to its `Makefile`:

```
SUPPRESS_WARNINGS := 1
```

Please do so only as a last resort if disabling individual warnings is not possible.

To disable a specific warning for the whole repository,
add an appropriate line to the definition of `DEFAULT_(COMMON|GCC|CLANG)_WARNINGS` in `Makefile.config`.


# ``Makefile.config``

This file contains the configuration to use when building.
If you want to change the flags used for building **globally** then
this is the place to do it.

# ``Makefile.rules``

This file contains the makefile rules to perform the build. If you wish
to add a new target and change how compilation is done then this is the
place to do it.

# Set files mode

The build system normally builds every source that it finds in a directory
where the explored directories are those implicitly found.

The build system has an alternative mode called "Set files mode" mode where the build
system will

* Only build benchmarks listed in a particular set of ``*.set`` files (i.e. the
  behaviour of building every source file in a directory is overriden).

This mode is useful if you only need to build a particular set of benchmarks. There
are three ways to use this mode, all of which basically set the ``SET_FILES``
makefile variable to a list of set files.

* Edit ``Makefile.config`` and set the ``SET_FILES`` variable to a space separated
  list of ``*.set`` files in the top level directory (e.g. ``Floats.set``).

  ```
  SET_FILES := BusyBox.set Floats.set
  ```

* Set the ``SET_FILES`` variable on the command line. This is a bit more cumbersome
  but can be useful for quick testing.

  ```
  $ make SET_FILES="BusyBox.set Floats.set"
  ```

* Set ``SET_FILES`` as environment variable. Be very careful doing it this way. It's
  easy to forget that this environment variable is set and consequently think that
  all the benchmarks are being built!

  ```
  $ export SET_FILES="BusyBox.set Floats.set"
  $ make
  ```

This mode is not on by default because all sources that live in the repository
**SHOULD BE POSSIBLE TO COMPILE ALL SOURCES IN THE REPOSITORY**.

Please also note that set files may contain wildcards but in filenames **ONLY**.
Wildcards may not be used for directory names.
