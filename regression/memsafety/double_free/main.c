void *my_malloc(unsigned int size) {
    return malloc(size);
}

int main() {
    void *a = my_malloc(sizeof(int));
    free(a);
    free(a);
}
