typedef struct data {
    struct data *next;
    int content;
} Data;

void main() {
    Data x1 = {0,};
    Data x2 = {&x1,};
    Data x3 = {&x2,};
    Data *curr = &x3;
    while (curr) {
        assert(curr->content == 0);
        curr = curr->next;
    }
}
