// Inspired by SV-comp:
// https://sv-comp.sosy-lab.org/2023/results/sv-benchmarks/c/Juliet_Test/CWE190_Integer_Overflow__int64_t_fscanf_add_01_bad.i

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

void printLine(const char * line);
void printLongLine(long longNumber);

void CWE190_Integer_Overflow__int64_t_fscanf_add_01_bad()
{
    int64_t data;
    data = 0LL;
    fscanf (stdin, "%" "l" "d", &data);
    {
        int64_t result = data + 1;
        printLongLongLine(result);
    }
}
int main(int argc, char * argv[])
{
    srand( (unsigned)time(((void *)0)) );
    printLine("Calling bad()...");
    CWE190_Integer_Overflow__int64_t_fscanf_add_01_bad();
    printLine("Finished bad()");
    return 0;
}
