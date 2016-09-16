# tstp2agda [![Build Status](https://travis-ci.org/agomezl/tstp2agda.svg)](https://travis-ci.org/agomezl/tstp2agda)

A proof reconstruction tool for Agda

## Installation

```bash
$ git clone https://github.com/agomezl/tstp2agda.git
$ cd tstp2agda
$ cabal install
```

## Usage

```
Usage: tstp2agda [OPTIONS]
  -f File  --file=File, --File=File  TSTP input file     (def: STDIN)
  -o File  --output=File             output to file      (def: STDOUT)
  -p Name  --proof-name=Name         main proof name     (def: proof)
  -m Name  --module-name=Name        module name         (def: Main)
  -h, -?   --help                    prints help message
```

## Links

* [Agda wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php)
* [TSTP](http://www.cs.miami.edu/~tptp/TSTP/)
