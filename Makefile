# this makes it easier to interface with compilers autograder for testing
default: lab4
lab*: # don't really care about the lab numbers so we just throw that out
	lake build

clean:
	lake clean
