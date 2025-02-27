#include <stdio.h>

/* Non-text files only!  Text files require lazy-i/o, which means the
   tests need to be done first, not second. */
void
get (f, size)
     register FILE *f;
     register int size;		/* unsigned causes unsigned test below */
{
    if (!(f->_flag & _IOREAD)) {
	fprintf(stderr, "get called on a file open for writing.\n");
	return;
    }
    f->_ptr += size;
    f->_cnt -= size;
    if (f->_cnt < size) {
	int ctemp;
	if (f->_cnt > 0)
	  fprintf(stderr, "Buffer not a multiple of record size.\n");
	/* We don't yet want the char that _filbuf tries to give us */
	ctemp = __filbuf(f);
	if (ctemp != EOF) ungetc(ctemp, f);
    }
}