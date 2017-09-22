#include <stdlib.h>

struct item {
    struct item *null;
    struct item *next;
    struct item *data;
};

struct item* alloc_or_die(void)
{
    struct item *pi = malloc(sizeof(*pi));
    if (!pi)
        abort();

    pi->null = NULL;
    pi->data = malloc(sizeof(struct item));
#if 1
    if (!pi->data)
        abort();
#endif
    return pi;
}

struct item* create_sll(void)
{
    struct item *sll = alloc_or_die();
    struct item *now = sll;

    // NOTE: running this on bare metal may cause the machine to swap a bit
    do {
        now->next = alloc_or_die();
        now->next->next = NULL;
        now = now->next;
    } while (__VERIFIER_nondet_int());

    return sll;
}

int main()
{
    struct item *sll = create_sll();

    assert(sll);
    assert(sll->next);

    return 0;
}

