// Inspired by SV-comp:
// https://sv-comp.sosy-lab.org/2023/results/sv-benchmarks/c/Juliet_Test/CWE190_Integer_Overflow__int64_t_fscanf_add_01_good.i

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

void printLine(const char * line);
void printLongLine(long longNumber);
void printLongLongLine(int64_t longLongIntNumber);

static void goodG2B()
{
    int64_t data;
    data = 0LL;
    data = 2;
    {
        int64_t result = data + 1;
        printLongLongLine(result);
    }
}
static void goodB2G()
{
    int64_t data;
    data = 0LL;
    fscanf (stdin, "%" "l" "d", &data);
    if (data < 0x7fffffffffffffffLL)
    {
        int64_t result = data + 1;
        printLongLongLine(result);
    }
    else
    {
        printLine("data value is too large to perform arithmetic safely.");
    }
}
void CWE190_Integer_Overflow__int64_t_fscanf_add_01_good()
{
    goodG2B();
    goodB2G();
}
int main(int argc, char * argv[])
{
    srand( (unsigned)time(((void *)0)) );
    printLine("Calling good()...");
    CWE190_Integer_Overflow__int64_t_fscanf_add_01_good();
    printLine("Finished good()");
    return 0;
}
