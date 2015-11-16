
import os, sys

resulsReader = open(sys.argv[1], "r")

previous = ""
for line in resulsReader:
        tokens = line.split()
        if previous == tokens[0]:
                print tokens[0]

        else:
                previous= tokens[0]
