// Many headers
#define TRUE 1
#define FALSE 0


typedef signed char s8;
typedef unsigned char u8;
typedef signed short int s16;
typedef unsigned short int u16;
typedef signed int s32;
typedef unsigned int u32;
typedef signed long long int s64;
typedef unsigned long long int u64;
typedef volatile u8 vu8;
typedef volatile u16 vu16;
typedef volatile u32 vu32;
typedef volatile u64 vu64;
typedef volatile s8 vs8;
typedef volatile s16 vs16;
typedef volatile s32 vs32;
typedef volatile s64 vs64;
typedef float f32;
typedef double f64;


typedef unsigned int size_t;

char *strcat( char *dest, const char *src );
char* strcpy(char*, const char*);
size_t strlen(const char*);

#pragma intrinsic (strcpy)



// sgidefs.h

typedef int __int32_t;
typedef unsigned  __uint32_t;

/* a 32 bit world */
typedef __int32_t __scint_t;
typedef __uint32_t __scunsigned_t;


// types.h

/* POSIX Extensions */
typedef unsigned char   uchar_t;
typedef unsigned short  ushort_t;
typedef unsigned int    uint_t;
typedef unsigned long   ulong_t;

/* Primarily Kernel types */
typedef	char *		addr_t;		/* ?<core address> type */
typedef	char *		caddr_t;	/* ?<core address> type */
typedef	long		daddr_t;	/* <disk address> type */
typedef	long		pgno_t;		/* virtual page number type */
// typedef	__uint32_t	pfn_t;		/* physical page number type */
typedef	short		cnt_t;		/* ?<count> type */

typedef __scint_t	__scoff_t;	/* scaling off_t */

typedef	unsigned long	mode_t;		/* file attrs */
typedef	unsigned long	dev_t;		/* device type */
typedef	long		uid_t;
typedef	long		gid_t;
typedef unsigned long	nlink_t;	/* used for link counts */
typedef long		pid_t;		/* proc & grp IDs  */
typedef	unsigned long	ino_t;		/* <inode> type */


typedef	long		off_t;		/* byte offset type */

typedef __uint32_t inst_t;		/* an instruction */


// time.h
typedef long 	clock_t;
typedef long 	time_t;
typedef struct timestruc {
	time_t	tv_sec;		/* seconds */
	long	tv_nsec;	/* and nanoseconds */
} timestruc_t;

struct tms {
	clock_t	tms_utime;		/* user time */
	clock_t	tms_stime;		/* system time */
	clock_t	tms_cutime;		/* user time, children */
	clock_t	tms_cstime;		/* system time, children */
};
extern clock_t	times (struct tms *);


// ucontext.h
#define NGREG	36
typedef unsigned int greg_t;

typedef greg_t gregset_t[NGREG];

// procfs.h
typedef struct {                /* signal set type */
        __uint32_t sigbits[4];
} sigset_t;

#define	__sigret_t	void
#define _sigargs	

typedef struct sigaction {
	int sa_flags;			/* see below for values		*/
	__sigret_t (*sa_handler)(_sigargs);	/* SIG_DFL, SIG_IGN, or *fn */
	sigset_t sa_mask;		/* additional set of sigs to be	*/
					/* blocked during handler execution */
	int sa_resv[2];
} sigaction_t;

typedef union sigval {
	int	sival_int;
	void	*sival_ptr;
} sigval_t;

#define SI_MAXSZ	128
#define SI_PAD		((SI_MAXSZ / sizeof(__int32_t)) - 3)

typedef struct siginfo {
	int	si_signo;		/* signal from signal.h	*/
	int 	si_code;		/* code from above	*/
	int	si_errno;		/* error from errno.h	*/
	union {

		int	_pad[SI_PAD];	/* for future growth	*/

		struct {			/* kill(), SIGCLD	*/
			pid_t	_pid;		/* process ID		*/
			union {
				struct {
					uid_t	_uid;
				} _kill;
				struct {
					clock_t _utime;
					int _status;
					clock_t _stime;
				} _cld;
			} _pdata;
		} _proc;			

		struct {	/* SIGSEGV, SIGBUS, SIGILL and SIGFPE	*/
			caddr_t	_addr;		/* faulting address	*/
		} _fault;

		struct {			/* SIGPOLL, SIGXFSZ	*/
		/* fd not currently available for SIGPOLL */
			int	_fd;	/* file descriptor	*/
			int	_band;
		} _file;
#if !defined (_XOPEN_SOURCE) // ??
		union sigval	_value;
#define si_value	_data._value
#endif

	} _data;

} siginfo_t;

struct sigaltstack {
	char	*ss_sp;
	int	ss_size;
	int	ss_flags;
};
typedef struct sigaltstack stack_t;

#define PRSYSARGS	6		/* max number of syscall arguments */


/*
 * ioctl codes and system call interfaces for /proc.
 */
#define PIOC		('q'<<8)
#define PIOCSTATUS	(PIOC|1)	/* get process status */
#define PIOCSTOP	(PIOC|2)	/* post STOP request and... */
#define PIOCWSTOP	(PIOC|3)	/* wait for process to STOP */
#define PIOCRUN		(PIOC|4)	/* make process runnable */
#define PIOCGTRACE	(PIOC|5)	/* get traced signal set */
#define PIOCSTRACE	(PIOC|6)	/* set traced signal set */
#define PIOCSSIG	(PIOC|7)	/* set current signal */
#define PIOCKILL	(PIOC|8)	/* send signal */
#define PIOCUNKILL	(PIOC|9)	/* delete a signal */
#define PIOCGHOLD	(PIOC|10)	/* get held signal set */
#define PIOCSHOLD	(PIOC|11)	/* set held signal set */
#define PIOCMAXSIG	(PIOC|12)	/* get max signal number */
#define PIOCACTION	(PIOC|13)	/* get signal action structs */
#define PIOCGFAULT	(PIOC|14)	/* get traced fault set */
#define PIOCSFAULT	(PIOC|15)	/* set traced fault set */
#define PIOCCFAULT	(PIOC|16)	/* clear current fault */
#define PIOCGENTRY	(PIOC|17)	/* get syscall entry set */
#define PIOCSENTRY	(PIOC|18)	/* set syscall entry set */
#define PIOCGEXIT	(PIOC|19)	/* get syscall exit set */
#define PIOCSEXIT	(PIOC|20)	/* set syscall exit set */
/*
 * These four are obsolete (replaced by PIOCSET/PIOCRESET)
 */
#define PIOCSFORK	(PIOC|21)	/* set inherit-on-fork flag */
#define PIOCRFORK	(PIOC|22)	/* reset inherit-on-fork flag */
#define PIOCSRLC	(PIOC|23)	/* set run-on-last-close flag */
#define PIOCRRLC	(PIOC|24)	/* reset run-on-last-close flag */

#define PIOCGREG	(PIOC|25)	/* get general registers */
#define PIOCSREG	(PIOC|26)	/* set general registers */
#define PIOCGFPREG	(PIOC|27)	/* get floating-point registers */
#define PIOCSFPREG	(PIOC|28)	/* set floating-point registers */
#define PIOCNICE	(PIOC|29)	/* set nice priority */
#define PIOCPSINFO	(PIOC|30)	/* get ps(1) information */
#define PIOCNMAP	(PIOC|31)	/* get number of memory mappings */
#define PIOCMAP		(PIOC|32)	/* get memory map information */
#define PIOCOPENM	(PIOC|33)	/* open mapped object for reading */
#define PIOCCRED	(PIOC|34)	/* get process credentials */
#define PIOCGROUPS	(PIOC|35)	/* get supplementary groups */
#define PIOCGETPR	(PIOC|36)	/* read struct proc */
#define PIOCGETU	(PIOC|37)	/* read user area */
/*
 * These are new with SVR4
 */
#define PIOCSET		(PIOC|38)	/* set modes of operation */
#define PIOCRESET	(PIOC|39)	/* reset modes of operation */
#define PIOCNWATCH	(PIOC|40)	/* get # watch points */
#define PIOCGWATCH	(PIOC|41)	/* get watch point */
#define PIOCSWATCH	(PIOC|42)	/* set watch point */
#define PIOCUSAGE	(PIOC|43)	/* get prusage_t structure */

#define premptyset(sp) \
	{ register int _i_ = sizeof(*(sp))/sizeof(u32); \
		while(_i_) ((u32*)(sp))[--_i_] = 0L; }

#define praddset(sp, flag) \
	(((unsigned)((flag)-1) < 32*sizeof(*(sp))/sizeof(u32)) \
	&& (((u32*)(sp))[((flag)-1)/32] |= (1L<<(((flag)-1)%32))))




typedef struct prstatus {
	ulong_t		pr_flags;	/* Process flags */
	short		pr_why;		/* Reason for process stop */
	short		pr_what;	/* More detailed reason */
	short		pr_cursig;	/* Current signal */
	sigset_t	pr_sigpend;	/* Set of pending signals */
	sigset_t	pr_sighold;	/* Set of held signals */
	struct siginfo	pr_info;	/* info assoc. with signal or fault */
	struct sigaltstack pr_altstack;	/* Alternate signal stack info */
	sigaction_t	pr_action;	/* Signal action for current signal */
	long		pr_syscall;	/* syscall number (if in syscall) */
	long		pr_nsysarg;	/* number of arguments to syscall */
	long		pr_errno;	/* error number from system call */
	long		pr_rval1;	/* syscall return value 1 */
	long		pr_rval2;	/* syscall return value 2 */
	long		pr_sysarg[PRSYSARGS];	/* syscall arguments */
	pid_t		pr_pid;		/* Process id */
	pid_t		pr_ppid;	/* Parent process id */
	pid_t		pr_pgrp;	/* Process group id */
	pid_t		pr_sid;		/* Session id */
	timestruc_t	pr_utime;	/* Process user cpu time */
	timestruc_t	pr_stime;	/* Process system cpu time */
	timestruc_t	pr_cutime;	/* Sum of children's user times */
	timestruc_t	pr_cstime;	/* Sum of children's system times */
	char		pr_clname[8];	/* Scheduling class name */
	long		pr_filler[20];	/* Filler area for future expansion */
	inst_t		pr_instr;	/* Current instruction */
	gregset_t	pr_reg;		/* General registers */
} prstatus_t; // size 0x2E8 (?)


/* values for pr_why */
#define PR_REQUESTED	1	/* in the interest of binary compatibility, */
#define PR_SIGNALLED	2	/* PR_REQUESTED thru PR_SYSEXIT match the   */
#define PR_SYSENTRY	3	/* prior settings from proc.h               */
#define PR_SYSEXIT	4
#define PR_FAULTED	5
#define PR_JOBCONTROL	6

typedef struct {
    unsigned long word[0x10];
} sysset_t;

typedef struct prmap_sgi {
	caddr_t	pr_vaddr;	/* Virtual base address */
	ulong_t	pr_size;	/* Size of mapping in bytes */
	__scoff_t	pr_off;	/* Offset into mapped object, if any */
	ulong_t	pr_mflags;	/* Protection and attribute flags */
				/* non PYHS type region information... */
	pgno_t	pr_vsize;	/* # of valid pages in this region */
	pgno_t	pr_psize;	/* # of private pages in this region */
	pgno_t	pr_wsize;	/* # of pages in region weighted base 256 */
	pgno_t	pr_rsize;	/* # of referenced pages in this region */
	pgno_t	pr_msize;	/* # of modified pages in this region */
	dev_t	pr_dev;		/* Device # of region iff mapped */
	ino_t	pr_ino;		/* Inode # of region iff mapped */
	long	pr_fill[5];	/* spares */
} prmap_sgi_t;

#define MA_READ		0x0001	/* mapping has readable permission */
#define MA_WRITE	0x0002	/* mapping has writable permission */
#define MA_EXEC		0x0004	/* mapping has executable permission */
#define MA_SHARED	0x0008	/* mapping is a shared or mapped object */
#define MA_BREAK	0x0010	/* mapping is grown by brk(2) */
#define MA_STACK	0x0020	/* mapping is grown on stack faults */
#define MA_PHYS		0x0040	/* mapping is a physical device */
/* flag values added for prmap_sgi */
#define	MA_PRIMARY	0x0800	/* mapping is part of primary object */
#define MA_SREGION	0x1000	/* mapping is on shared region list */
#define MA_COW		0x2000	/* mapping is set to copy on write */
#define	MA_NOTCACHED	0x4000	/* mapping is not cacheable by process */
#define MA_SHMEM	0x8000	/* mapping is a shmem() memory region */
#define	MA_REFCNT_SHIFT	    16	/* shift for region reference count */
/* fractional base for pr_wsize */
#define	MA_WSIZE_FRAC	   256	/* base for pr_wsize */

// stdlib.h

extern void *calloc(size_t, size_t);
extern void free(void *);
extern void *malloc(size_t);
extern void *realloc(void *, size_t);

// stdio.h

typedef long	fpos_t;
#define NULL (void*)0

#define BUFSIZ	4096
#define _NFILE	100	/* initial number of streams */

#define stdin	(&__iob[0])	
#define stdout	(&__iob[1])	
#define stderr	(&__iob[2])	

typedef struct {
    int        _cnt;    /* number of available characters in buffer */
    unsigned char    *_ptr;    /* next character from/to here in buffer */
    unsigned char    *_base;    /* the buffer */
    unsigned char    _flag;    /* the state of the stream */
    unsigned char    _file;    /* UNIX System file descriptor */
} FILE;

extern FILE		__iob[_NFILE];	
extern FILE		*_lastbuf;
extern unsigned char 	*_bufendtab[];
extern unsigned char	 _sibuf[], _sobuf[];

extern int	remove(const char *);
extern int	rename(const char *, const char *);
extern FILE	*tmpfile(void);
extern char	*tmpnam(char *);
extern int	fclose(FILE *);
extern int	fflush(FILE *);
extern FILE	*fopen(const char *, const char *);
extern FILE	*freopen(const char *, const char *, FILE *);
extern void	setbuf(FILE *, char *);
extern int	setvbuf(FILE *, char *, int, size_t);
/* PRINTFLIKE2 */
extern int	fprintf(FILE *, const char *, ...);
/* SCANFLIKE2 */
extern int	fscanf(FILE *, const char *, ...);
/* PRINTFLIKE1 */
extern int	printf(const char *, ...);
/* SCANFLIKE1 */
extern int	scanf(const char *, ...);
/* PRINTFLIKE2 */
extern int	sprintf(char *, const char *, ...);
/* SCANFLIKE2 */
extern int	sscanf(const char *, const char *, ...);
extern int	vfprintf(FILE *, const char *, /* va_list */ char *);
extern int	vprintf(const char *, /* va_list */ char *);
extern int	vsprintf(char *, const char *, /* va_list */ char *);
extern int	fgetc(FILE *);
extern char	*fgets(char *, int, FILE *); 
extern int	fputc(int, FILE *);
extern int	fputs(const char *, FILE *);
extern int	getc(FILE *);
extern int	getchar(void);
extern char	*gets(char *);
extern int	putc(int, FILE *);
extern int	putchar(int);
extern int	puts(const char *);
extern int	ungetc(int, FILE *);
extern size_t	fread(void *, size_t, size_t, FILE *);
#pragma int_to_unsigned fread
extern size_t	fwrite(const void *, size_t, size_t, FILE *);
#pragma int_to_unsigned fwrite
extern int	fgetpos(FILE *, fpos_t *);
extern int	fseek(FILE *, long, int);
extern int	fsetpos(FILE *, const fpos_t *);
extern long	ftell(FILE *);
extern void	rewind(FILE *);
extern void	clearerr(FILE *);
extern int	feof(FILE *);
extern int	ferror(FILE *);
extern void	perror(const char *);

extern int	__filbuf(FILE *);	
extern int	__flsbuf(int, FILE *);	

extern int	__semputc(int, FILE *);
extern int	__semgetc(FILE *);
extern int	__us_rsthread_stdio;

#define getc_locked(p)	   	(__us_rsthread_stdio ? __semgetc(p) : \
			(--(p)->_cnt < 0 ? __filbuf(p) : (int)*(p)->_ptr++))
#define putc_locked(x, p)     	(__us_rsthread_stdio ? __semputc(x,p) : \
			(--(p)->_cnt < 0 ? __flsbuf((x), (p)) \
					  : (int)(*(p)->_ptr++ = (x))))
#define getchar_locked()	getc_locked(stdin)
#define putchar_locked(x)	putc_locked((x), stdout)
#define clearerr_locked(p)	clearerr(p)
#define feof_locked(p)		feof_unlocked(p)
#define ferror_locked(p)	ferror_unlocked(p)
#define fileno_locked(p)	fileno_unlocked(p)

/* Explicit unlocked (thread-unsafe) versions */
#define getc_unlocked(p)	(--(p)->_cnt < 0 ? __filbuf(p) : (int)*(p)->_ptr++)
#define putc_unlocked(x, p)	(--(p)->_cnt < 0 ? __flsbuf((x), (p)) \
				: (int)(*(p)->_ptr++ = (x)))
#define getchar_unlocked()	getc_unlocked(stdin)
#define putchar_unlocked(x)	putc_unlocked((x), stdout)
#define clearerr_unlocked(p)	((void)((p)->_flag &= ~(_IOERR | _IOEOF)))
#define feof_unlocked(p)	(((int)(p)->_flag) & _IOEOF)
#define ferror_unlocked(p)	(((int)(p)->_flag) & _IOERR)
#define fileno_unlocked(p)	(p)->_file


// fcntl.h

/*
 * Flag values accessible to open(2) and fcntl(2)
 * (the first three and O_DIRECT can only be set by open).
 */
#define	O_RDONLY	0
#define	O_WRONLY	1
#define	O_RDWR		2
#if !defined(_POSIX_SOURCE) 
#define	O_NDELAY	0x04	/* non-blocking I/O */
#endif /* !defined(_POSIX_SOURCE) */ 
#define	O_APPEND	0x08	/* append (writes guaranteed at the end) */
#if !defined(_POSIX_SOURCE) || defined(_XOPEN_SOURCE) 
#define	O_SYNC		0x10	/* synchronous write option */
#endif /* !defined(_POSIX_SOURCE) || defined(_XOPEN_SOURCE */ 
#define	O_NONBLOCK	0x80	/* non-blocking I/O (POSIX) */
#if defined(_SGI_SOURCE) && !defined(_POSIX_SOURCE) && !defined(_XOPEN_SOURCE)
#define O_DIRECT	0x8000	/* direct I/O */
#endif /* SGI && !POSIX && !XOPEN */
/*
 * Flag values accessible only to open(2).
 */
#define	O_CREAT		0x100	/* open with file create (uses third open arg) */
#define	O_TRUNC		0x200	/* open with truncation */
#define	O_EXCL		0x400	/* exclusive open */
#define	O_NOCTTY	0x800	/* don't allocate controlling tty (POSIX) */


// unistd.h
typedef int    ssize_t;

extern pid_t getpid(void);
extern pid_t getppid(void);
extern uid_t getuid(void);
extern int isatty(int);
extern int link(const char *, const char *);
extern off_t lseek(int, off_t, int);
extern long pathconf(const char *, int);
extern int pause(void);
extern int pipe(int *);
extern ssize_t read(int, void *, size_t);
extern int rename(const char *, const char *);
extern int rmdir(const char *);
extern int setgid(gid_t);
extern int setpgid(pid_t, pid_t);
extern pid_t setsid(void);
extern int setuid(uid_t);
extern unsigned sleep(unsigned);
extern long sysconf(int);
extern pid_t tcgetpgrp(int);
extern int tcsetpgrp(int, pid_t);
extern char *ttyname(int);
extern int unlink(const char *);
extern ssize_t write(int, const void *, size_t);




// varargs.h from indy dump

typedef char *va_list;
typedef unsigned long __va_iptr_t;
#define _FP 1

#define __VA_REGBYTES 4
#define __VA_PADJUST(mode)	0
#define __NO_CFOLD_WARNING(x) x
#define __VA_SADJUST _VA_INIT_STATE
#define __VA_MALIGN(mode) \
    (__NO_CFOLD_WARNING(  \
       (__builtin_alignof(mode) > __VA_REGBYTES)  \
	  ? (__va_iptr_t)__builtin_alignof(mode) \
	  : (__va_iptr_t)__VA_REGBYTES ))
#define	__VA_PALIGN(p,mode)	\
  ( ( ((__va_iptr_t)p)+(__VA_MALIGN(mode)-1) ) & (-__VA_MALIGN(mode)) )
#define __VA_STACK_ARG(vp,mode)	( vp = (va_list) \
	(__VA_PALIGN(vp,mode)+__VA_PADJUST(mode)+sizeof(mode)) )
#define __VA_DOUBLE_ARG(vp,mode) ( \
    (((__va_iptr_t)vp & 0x1) /* 1 byte aligned? */ \
      ? ((vp = ((va_list)vp + 7)),((va_list)vp-6))\
      : (((__va_iptr_t)vp & 0x2) /* 2 byte aligned? */ \
	  ? ((vp = ((va_list)vp +10)),((va_list)vp-24)) \
	  : __VA_STACK_ARG(vp,mode) )))

#define va_dcl long va_alist;

#define va_start(vp) (vp = ((va_list)&va_alist) - __VA_SADJUST)

#define va_arg(vp,mode) ((mode*)(void *)(  \
	(__NO_CFOLD_WARNING(                \
	   (__builtin_classof(mode)==_FP && \
	    __builtin_alignof(mode)==sizeof(double)) \
	      ? __VA_DOUBLE_ARG(vp,mode) \
	      : __VA_STACK_ARG(vp,mode))))) [-1]

#define va_end(__list)


// errno.h
extern s32 errno;
extern const char* sys_errlist[];
extern s32 sys_nerr;

