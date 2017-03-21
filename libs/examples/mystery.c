#include <stdio.h>

main(argc, argv)
int	argc;
char	**argv;
{
    int	n, i;

    n = atoi(argv[1]);

    for (i = 1; i <= n; i++)
	printf("%d\n", i * i);

    return 0;
}
