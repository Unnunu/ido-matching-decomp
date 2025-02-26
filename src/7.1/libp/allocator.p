#define ptradd(_type, _ptr, _offset) _type(ord(_ptr) + (_offset))

#include "cmplrs/mipspascal.h"
#include "cmplrs/allocator.h"

const
    default_scb_size = 64*1024;
    bcb_mask = 16#fffffffc;
    curr_allocated = 16#1;
    prev_allocated = 16#2;
    min_fragment = 256;

type
    scbp = ^scb;
    bcbp = ^bcb;
    scb = record
        last_scb : scbp;
        next_scb : scbp;
        free_list : bcbp;
        scb_size : integer;
    end {record};

    {---------------------------------------------------------------------------}
    { curr_size is the size of the current bcb, it is always a factor of 8. The }
    { lowest two bits encode whether the entry is allocated and whether the     }
    { previous entry is allocated. The two masks curr_allocated and	      }
    { prev_allocated are used to determine the two conditions.		      }
    {---------------------------------------------------------------------------}
    bcb = record
        prev_size : integer;
        curr_size : integer;
        case boolean of
            true : ();
            false : (
                last_bcb : bcbp;
                next_bcb : bcbp);
    end {record};

var
    alloc_anchor : scbp := nil;

function sbrk(fsize : integer): scbp; external;
procedure memcpy(toptr, fromptr : pointer; fsize : cardinal); external;

function alloc_page(fsize : integer): scbp;
var
    p : scbp;
    q : scbp;
    i : integer;
begin
    if (alloc_anchor = nil) or (alloc_anchor^.scb_size < fsize) then begin
        p := sbrk(fsize);
        if ord(p) = -1 then 
            p := nil
        else if bitand(ord(p), -4096) <> ord(p) then begin
            i := bitand(ord(p) + 4095, -4096) - ord(p);
            q := sbrk(i);
            p := ptradd(scbp, p, i);
        end;
    end else begin
        p := alloc_anchor;
        alloc_anchor := alloc_anchor^.next_scb;
    end;
    alloc_page := p;
end {function alloc_page};

procedure alloc_free(fptr : scbp);
begin
    fptr^.next_scb := alloc_anchor;
    alloc_anchor := fptr;
    fptr^.scb_size := abs(fptr^.scb_size);
end {procedure alloc_free};

procedure alloc_scb(var fmark : scbp; fsize : integer);
var
    q : scbp;
    r : bcbp;
    s : bcbp;

begin
    q := alloc_page(fsize);
    fmark := q;
    if q = nil then return;
    q^.scb_size := -fsize;
    q^.last_scb := nil;
    q^.next_scb := nil;

    {-------------------------------------------------------------------------}
    { construct a bcb out of free space 				      }
    {-------------------------------------------------------------------------}
    r := ptradd(bcbp, q, sizeof(scb));
    s := ptradd(bcbp, q, fsize-8);
    r^.prev_size := 0;
    r^.curr_size := ord(s)-ord(r)+prev_allocated;
    s^.prev_size := ord(s)-ord(r);
    s^.curr_size := 0+curr_allocated;
    r^.last_bcb := r;
    r^.next_bcb := r;
    q^.free_list := r;
end {procedure alloc_scb};

function alloc_mark; { (var fheap : integer): integer; external; }
var
    p : scbp;
    q : scbp;
    r : bcbp;
    s : bcbp;
    t : bcbp;
    rsize : integer;

begin
    alloc_scb(q, default_scb_size);
    if q = nil then return(0);
    alloc_mark := ord(q);
    p := scbp(fheap);

    {-------------------------------------------------------------------------}
    { chain scb onto list						      }
    {-------------------------------------------------------------------------}
    if p <> nil then begin
        while p^.next_scb <> nil do p := p^.next_scb;
        p^.next_scb := q;
        q^.last_scb := p;
    end;

    fheap := q;
    q^.scb_size := abs(q^.scb_size);

    r := q^.free_list;
    rsize := bitand(r^.curr_size, bcb_mask);
    s := ptradd(bcbp, r, sizeof(bcb));
    t := ptradd(bcbp, r, rsize);
    r^.next_bcb := s;
    r^.last_bcb := s;
    s^.next_bcb := r;
    s^.last_bcb := r;
    t^.prev_size := ord(t)-ord(s);
    s^.curr_size := ord(t)-ord(s)+prev_allocated;
    r^.curr_size := 0+prev_allocated;
    q^.free_list := s;

end {function alloc_mark};

procedure alloc_release; { (var fheap : integer; fmark : integer); external; }
var
    p : scbp;
    q : scbp;
    r : scbp;

begin
    p := scbp(fheap);
    q := scbp(fmark);

    {-------------------------------------------------------------------------}
    { be sure mark is in the heap					      }
    {-------------------------------------------------------------------------}
    while (p <> q) and (p <> nil) do p := p^.last_scb;
    if p = nil then return;		{ could post an error		      }

    {-------------------------------------------------------------------------}
    { set the heap to the first mark before fmark or nil		      }
    {-------------------------------------------------------------------------}
    r := q^.last_scb;
    if r <> nil then r^.next_scb := nil;
    while (r <> nil) and (r^.scb_size < 0) do r := r^.last_scb;
    fheap := r;

    {-------------------------------------------------------------------------}
    { free all the scb's from the mark until the end of the list              }
    {-------------------------------------------------------------------------}
    repeat
        r := q^.next_scb;
        alloc_free(q);
        q := r;
    until q = nil;

end {procedure alloc_release};

function alloc_next_scb(fsize : integer; var fheap : pointer): integer;
var
    p : scbp;
    q : scbp;
    r : bcbp;
    s : bcbp;

begin
    alloc_scb(q, max(default_scb_size, bitand(fsize+8+sizeof(scb)+4095,
	16#7ffff000)));
    if q = nil then return(0);
    p := scbp(fheap);

    {-------------------------------------------------------------------------}
    { chain scb onto list						      }
    {-------------------------------------------------------------------------}
    while p^.next_scb <> nil do p := p^.next_scb;
    p^.next_scb := q;
    q^.last_scb := p;
    p := scbp(fheap);
    r := q^.free_list;
    s := p^.free_list;

    {-------------------------------------------------------------------------}
    { place bcb on free chain						      }
    {-------------------------------------------------------------------------}
    if s <> nil then begin
        r^.last_bcb := s^.last_bcb;
        r^.next_bcb := s;
        s^.last_bcb^.next_bcb := r;
        s^.last_bcb := r;
    end;
    p^.free_list := r;
    return(1);
  end {function alloc_next_scb};


{ NON_MATCHING !!! }
function alloc_resize; { (fptr : pointer; fsize : cardinal; var fheap : pointer): pointer }
var
    nptr : bcbp;
    csize : integer;

begin
    if fptr <> nil then begin
        nptr := ptradd(bcbp, fptr, -8);
        if bitand(nptr^.curr_size, curr_allocated) = 0 then return(pointer(nil));
        csize := bitand(nptr^.curr_size, bcb_mask);
        if csize >= fsize + 4 then return(fptr);

        nptr := bcbp(alloc_new(fsize, fheap));
        if nptr = nil then return(pointer(nil));
        memcpy(pointer(nptr), fptr, csize);
        alloc_dispose(fptr, fheap);
        alloc_resize := pointer(nptr);
    end else
        alloc_resize := alloc_new(fsize, fheap);
end {function alloc_resize};
