CC=gcc
CFLAGS=-std=c++20 -Wall -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -g
CXX=g++

INCLUDE=-Iminisat -Iminisat/minisat/core -Iminisat/minisat/mtl -Iminisat/minisat/simp -Iaiger/

all:	ic3

ic3:	minisat/build/dynamic/lib/libminisat.so aiger/aiger.o Model.o IC3.o main.o
	$(CXX) $(CFLAGS) $(INCLUDE) -o ic3 \
		aiger/aiger.o Model.o IC3.o main.o \
		minisat/build/release/lib/libminisat.a

.c.o:
	$(CC) -g -Og $(INCLUDE) $< -c

.cpp.o:
	$(CXX) $(CFLAGS) $(INCLUDE) $< -c

clean:
	rm -f *.o ic3

dist:
	cd ..; tar cf ic3ref/IC3ref.tar ic3ref/*.h ic3ref/*.cpp ic3ref/Makefile ic3ref/LICENSE ic3ref/README; gzip ic3ref/IC3ref.tar
