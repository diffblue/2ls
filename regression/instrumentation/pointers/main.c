struct data {
    struct data *next;
    int content;
};

void main() {
    struct data x1 = {0,};
    struct data x2 = {&x1,};
    struct data x3 = {&x2,};
    struct data *curr = &x3;
    while (curr) {
        assert(curr->content == 0);
        curr = curr->next;
    }
}
