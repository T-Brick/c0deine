# this makes it easier to interface with compilers autograder for testing
default: lab4

lab%: # don't really care about the lab numbers so we just throw that out
	lake exe cache get && lake build

clean:
	lake clean && testing/clean.sh && rm -r toolchains
