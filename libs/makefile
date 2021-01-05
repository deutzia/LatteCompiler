all: calls.o runtime.o

calls.o: calls.asm
	nasm -g -f elf64 calls.asm

runtime.o: runtime.c
	gcc runtime.c -g -c

clean:
	rm -f *.o
