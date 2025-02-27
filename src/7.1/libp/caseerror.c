#include "pascalio.h"

void caseerror(page, line, name, namelength)
    register int page;
    register int line;
    register unsigned char *name;
    register unsigned namelength;
{
    register unsigned char *n = malloc(namelength+1);
    memcpy(n, name, namelength);
    n[namelength] = '\0';
    fprintf(stderr,
      "No case matches value in case statement on page %d line %d file %s.\n",
      page, line, n);
}

void assert_err(name, namelength)
    register unsigned char *name;
    register unsigned namelength;
{
    register unsigned char *n = malloc(namelength+1);
    memcpy(n, name, namelength);
    n[namelength] = '\0';
    fprintf(stderr, "assertion failed %s \n", n);
    fflush(stderr);
}