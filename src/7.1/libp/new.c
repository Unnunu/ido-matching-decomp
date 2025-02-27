#include "pascalio.h"

unsigned char *
new (size, zero)
     unsigned size;
     unsigned zero;
{
    register unsigned char *p = xmalloc(size);
    if (zero && p != NULL) memset(p, 0, size);
    return (p);
}

void
dispose (p, size)
     unsigned char * p;
     unsigned size;
{
    xfree (p);
}