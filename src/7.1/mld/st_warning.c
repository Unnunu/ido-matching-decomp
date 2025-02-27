#include <stdio.h>

extern char	*st_errname;

void st_warning (s, a, b, c, d) 

char *s; 
int a,b,c,d;
{
	fprintf( stderr, "\n" );
	fprintf( stderr, "%s: Warning: ", st_errname );
	fprintf( stderr, s, a, b, c, d );
	fprintf( stderr, "\n" );
}