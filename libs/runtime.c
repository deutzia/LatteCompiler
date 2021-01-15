#include <stdio.h>
#include <string.h>
#include <stdlib.h>

char* __stradd(char* a, char* b)
{
    int lenA = strlen(a), lenB = strlen(b);
    char* res = calloc(lenA + lenB + 1, sizeof(char));
    strcpy(res, a);
    strcpy(res + lenA, b);
    return res;
}

int64_t __strcmp(char* a, char* b)
{
    return strcmp(a, b) == 0;
}

int64_t __strncmp(char* a, char* b)
{
    return strcmp(a, b) != 0;
}

void _printInt(int64_t a)
{
    printf("%ld\n", a);
}

void _printString(char* c)
{
    printf("%s\n", c);
}

void error()
{
    printf("runtime error");
    exit(-1);
}

int64_t _readInt()
{
    int x;
    scanf("%d\n", &x);
    return x;
}

char* _readString()
{
    char* res = NULL;
    size_t len = 0;
    getline(&res, &len, stdin);
    len = strlen(res);
    res[len - 1] = 0;
    return res;
}

void* _allocate(size_t size)
{
    return calloc(size, 1);
}
