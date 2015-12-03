void printf(char *format);
void assert_fail(void);

void equal(int *a, int *b) {
        if (*a != *b) {
                printf("ERROR\n");
                assert_fail();
                assert(0);
        }
        return;

        ERROR:
        return;
}

int a, b;
int *pa, *pb;

int main() {
        pa = &a;
        pb = &b;

        a = 0;
        b = 1;

        *pa = *pb;

        equal(&a, &b);
        return 0;
}
