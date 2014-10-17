void printf(char *format);
void assert_fail(void);

int main() {
        int a, b, c;
        int *pa, *pb, *pc = &c;

	//__CPROVER_assume(pa!=0);
        if (pc == 0 ||
               pa == pb && *pa != *pb) {
                printf("ERROR\n");
                assert_fail();
                assert(0);
        }

        *pc = 60;
        if (c != 60) {
                printf("ERROR\n");
                assert_fail();
                assert(0);
        }

        return 0;
}
