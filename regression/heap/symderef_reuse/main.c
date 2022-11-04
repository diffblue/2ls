#include <stdlib.h>

struct node {
    int data;
    struct node *next;
};

int main()
{
    struct node *first = malloc(sizeof(*first));
    struct node *second = malloc(sizeof(*first));
    first->data = 0;
    second->data = 1;
    first->next = second;
    second->next = NULL;

    for (int i = 0; i < 2; i++)
    {
        struct node *n = first;
        for (int j = i; j > 0; j--)
            n = n->next;
        int data = n->data;
        assert(data == i);
    }
}
