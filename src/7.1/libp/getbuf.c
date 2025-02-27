#include "pascalio.h"

/* Create a new buffer of size rsize for use with file iop */
void
_getbuf (iop, rsize)
     register FILE *iop;
     register unsigned rsize;
{
    int size, type;
    unsigned char* vbuf;

    size = calc_size(iop, rsize);
    type = (iop==stdout && isatty(fileno(stdout))) ? _IOLBF : _IOFBF;
    vbuf = (unsigned char *) malloc((unsigned) size);
    if (vbuf == NULL) {
        fprintf(stderr, "malloc failed");
        exit(1);
    }
    iop->_flag |= _IOMYBUF;
    setvbuf(iop, vbuf, type, size);
    iop->_cnt = size;
}