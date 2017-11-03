int main(void)
{
    int i = 1, j = 2, k = 3;
    while (i!=j && j!=k)
    {
        j = k - i;
        k = j + i;
        i = k - j;
        while (i!=k && j!=k)
        {
            j = k - i;
            k = j + i;
            i = k - j;
            while (i!=j && j!=k)
            {
                j = k - i;
                k = j + i;
                i = k - j;
             }

        }        
    }
}
