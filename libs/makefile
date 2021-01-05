all: calls.o runtime.o

calls.o:
	nasm -g -f elf64 calls.asm

runtime.o:
	gcc runtime.c -g -c

clean:
	rm -f *.o
