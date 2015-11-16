/* index_prune implements a function to build a query structure
 * from a query string.  This turned out to be surprisingly difficult,
 * as it turns out to be an optimisation problem when trying to select
 * words from the query.
 *
 * written nml 2003-06-02 (moved from index_search.c 2003-09-23)
 *
 */

#include "firstinclude.h"

#include "include/index_prune.h"

#include "_index.h"

#include "vec.h"
#include "def.h"
#include "iobtree.h" 
#include "queryparse.h" 
#include "str.h" 
#include "stem.h" 
#include "stop.h" 
#include "vec.h"
#include "poolalloc.h"
#include "metric.h"
#include "fdset.h"
#include "objalloc.h"
#include "docmap.h" 
#include "chash.h"
#include "_chash.h"
#include "heap.h"
#include "search.h"


#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>


#ifdef MT_ZET
#include <pthread.h>

static pthread_mutex_t vocab_mutex = PTHREAD_MUTEX_INITIALIZER;

#endif /* MT_ZET */

/* maximum length of an in-vocab vector. */
#define MAX_VOCAB_VECTOR_LEN 4096




/**
 *  Non-synchronized version of get_vocab_vector, i.e. we
 *  assume that, in a multi-threaded environment, the caller
 *  has already performed any necessary synchronisation.
 */
static int get_vocab_vector_locked(struct iobtree * vocab, 
  struct vocab_vector * entry_out, const char * term, unsigned int term_len,
  char * vec_buf, int vec_buf_len, int impact) {
    void * ve_data = NULL;
    unsigned int veclen = 0;
    struct vec v;

    ve_data = iobtree_find(vocab, term, term_len, 0, &veclen);
    if (!ve_data)
        return 0;
    v.pos = ve_data;
    v.end = v.pos + veclen;
    if (!impact) {
        /* select first non-impact-ordered vector */
        do {
            if (vocab_decode(entry_out, &v) != VOCAB_OK) {
                return -1; 
            }
        } while (entry_out->type == VOCAB_VTYPE_IMPACT);
    } else {
        /* select first impact-ordered vector */
        do {
            if (vocab_decode(entry_out, &v) != VOCAB_OK) {
                return -1; 
            }
        } while (entry_out->type != VOCAB_VTYPE_IMPACT);
    }
    if (entry_out->location == VOCAB_LOCATION_VOCAB) {
        assert(entry_out->size <= (unsigned int) vec_buf_len);
        memcpy(vec_buf, entry_out->loc.vocab.vec, entry_out->size);
        entry_out->loc.vocab.vec = vec_buf;
    }
    return 1;
}

/**
 *  Extract a vocab entry from a btree.
 *
 *  This function is synchronised on the vocab_mutex mutex.
 *  At the end of this call, the vocab entry is completely
 *  independent form the btree.
 *
 *  @param vec_buf buffer to store vector if the vocab entry
 *  has an in-vocab vector.  entry_out->loc.vocab.vec will be
 *  made to point to this.  You need to copy this before
 *  reusing the vector if you want to retain it.
 *
 *  @return 0 if the term does not exist in the vocab 
 *  (entry_out will be unchanged); 1 if the term exists in
 *  the vocab (entry_out will hold the vocab entry for the
 *  term); < 0 on error.
 */
static int get_vocab_vector(struct iobtree * vocab, 
  struct vocab_vector * entry_out, const char * term, unsigned int term_len,
  char * vec_buf, int vec_buf_len, int impact) {
    int retval = 0;
#ifdef MT_ZET
    pthread_mutex_lock(&vocab_mutex);
#endif /* MT_ZET */
    retval = get_vocab_vector_locked(vocab, entry_out, term, term_len,
      vec_buf, vec_buf_len, impact);
#ifdef MT_ZET
    pthread_mutex_unlock(&vocab_mutex);
#endif /* MT_ZET */
    return retval;
}

/* internal function to append a new word to a conjunct */
static int conjunct_append(struct query *query, 
  struct conjunct *conj, struct vocab_vector * sve,
  const char *term, unsigned int termlen, unsigned int *maxterms) {
    struct term *currterm;

    /* OPTIMISE: search existing AND conjunct for word */

    /* we're building a new phrase */
    if (query->terms < *maxterms) {
        /* iterate to the end of the phrase */
        for (currterm = &conj->term; currterm->next;
          currterm = currterm->next) ;

        /* add next word on */
        (*maxterms)--;
        currterm = currterm->next = &query->term[*maxterms].term;
        if (!(currterm->term = str_ndup(term, termlen))) {
            return 0;
        }
        memcpy(&currterm->vocab, sve, sizeof(*sve));

        /* allocate memory for vector part of vector */
        if (currterm->vocab.location == VOCAB_LOCATION_VOCAB) {
            if ((currterm->vecmem = malloc(currterm->vocab.size))) {
                memcpy(currterm->vecmem, 
                  currterm->vocab.loc.vocab.vec, currterm->vocab.size);
            } else {
                free(currterm->term);
                return 0;
            }
        } else {
            currterm->vecmem = NULL;
        }
        currterm->next = NULL;
        conj->terms++;
    }
    /* else we need to steal slots (OPTIMIZE) */

    return 1;
}

static struct conjunct *conjunct_find(struct query *query,
  struct vocab_vector *sve, const char *term, unsigned int termlen,
  int type) {
    unsigned int i;
    for (i = 0; i < query->terms; i++) {
        if ((query->term[i].type == type) 
          && (sve->size == query->term[i].term.vocab.size)
          && (sve->location == query->term[i].term.vocab.location)
          && (((sve->location == VOCAB_LOCATION_VOCAB) 
              && (query->term[i].term.term) 
              && !str_ncmp(term, query->term[i].term.term, termlen))
            || ((sve->location == VOCAB_LOCATION_FILE) 
              && (sve->loc.file.fileno 
                == query->term[i].term.vocab.loc.file.fileno)
              && (sve->loc.file.offset 
                == query->term[i].term.vocab.loc.file.offset)))) {

            return &query->term[i];
        }
    }
    return NULL;
}

/* internal function to copy a word into a new conjunct */
static struct conjunct *conjunct_add(struct query *query, 
  struct vocab_vector * sve, const char *term, 
  unsigned int termlen, int type, unsigned int *maxterms) {
    struct conjunct *ret = NULL;

    ret = conjunct_find(query, sve, term, termlen, type);

    if (ret != NULL) {
        ret->f_qt++;
    } else {
        /* couldn't find a match, might have to insert the word */
        if (query->terms < *maxterms) {
            ret = &query->term[query->terms];
            ret->type = type;
            ret->f_qt = 1;
            ret->f_t = sve->header.docwp.docs;
            ret->F_t = sve->header.docwp.occurs;
            ret->term.next = NULL;
            ret->vecmem = NULL;
            ret->terms = 1;
            ret->sloppiness = 0;
            ret->cutoff = 0;
            query->terms++;
            if (!(ret->term.term = str_ndup(term, termlen))) {
                query->terms--;
                ret = NULL;
            }
            memcpy(&ret->term.vocab, sve, sizeof(*sve));
            /* allocate memory for vector part of vector */
            if (ret->term.vocab.location == VOCAB_LOCATION_VOCAB) {
                if ((ret->term.vecmem = malloc(sve->size))) {
                    memcpy(ret->term.vecmem, sve->loc.vocab.vec, sve->size);
                } else {
                    free(ret->term.term);
                    return 0;
                }
            } else {
                ret->term.vecmem = NULL;
            }
        }
        /* else we might have to steal a slot (OPTIMIZE) */
    }

    return ret;
}

/* internal function to copy a conjunction and add an new word onto the end of 
 * it (convenience function) */
static struct conjunct *conjunct_copy(struct query *query, 
  struct conjunct *conj, unsigned int matches, struct vocab_vector * sve,
  const char *term, unsigned int termlen, unsigned int *maxterms) {
    struct conjunct *ret = NULL,
                    *next;
    struct term *currterm,
                *nextterm;

    if (!matches) {
        return NULL;
    }

    /* copy head of non-matching phrase */
    if (query->terms < *maxterms) {
        ret = next = &query->term[query->terms++];
        memcpy(&next->term.vocab, &conj->term.vocab, sizeof(conj->term.vocab));
        if (!(next->term.term = str_dup(conj->term.term))) {
            /* FIXME: need to cleanup properly here */
            return NULL;
        }

        /* allocate memory for vector part of vector */
        if (next->term.vocab.location == VOCAB_LOCATION_VOCAB) {
            if ((next->term.vecmem = malloc(conj->term.vocab.size))) {
                memcpy(next->term.vecmem, conj->term.vecmem, 
                  conj->term.vocab.size);
            } else {
                free(next->term.term);
                return NULL;
            }
        }

        next->term.next = NULL;
        next->terms = 1;
        next->f_qt = 1;
        next->type = conj->type;
        matches--;

        nextterm = &next->term;
        currterm = conj->term.next;
        while ((query->terms < *maxterms) && matches) {
            (*maxterms)--;
            matches--;
            nextterm->next = &query->term[*maxterms].term;
            nextterm = nextterm->next;
            memcpy(&nextterm->vocab, &currterm->vocab, sizeof(currterm->vocab));
            if (!(nextterm->term = str_dup(currterm->term))) {
                /* FIXME: need to cleanup properly here */
                return NULL;
            }

            /* allocate memory for vector part of vector */
            if (nextterm->vocab.location == VOCAB_LOCATION_VOCAB) {
                if ((nextterm->vecmem = malloc(currterm->vocab.size))) {
                    memcpy(nextterm->vecmem, currterm->vecmem, 
                      currterm->vocab.size);
                } else {
                    free(nextterm->term);
                    return NULL;
                }
            }
            next->terms++;
        }
        nextterm->next = NULL;

        /* append new term to phrase */
        if ((query->terms < *maxterms) && sve) {
            /* add next word on */
            (*maxterms)--;
            currterm = nextterm->next = &query->term[*maxterms].term;
            if (!(currterm->term = str_ndup(term, termlen))) {
                /* FIXME: need to cleanup properly here */
                return NULL;
            }
            memcpy(&currterm->vocab, sve, sizeof(*sve));
            /* allocate memory for vector part of vector */
            if (currterm->vocab.location == VOCAB_LOCATION_VOCAB) {
                if ((currterm->vecmem = malloc(currterm->vocab.size))) {
                    memcpy(currterm->vecmem, currterm->vocab.loc.vocab.vec,
                      currterm->vocab.size);
                } else {
                    free(nextterm->term);
                    return NULL;
                }
            }
            currterm->next = NULL;
            next->terms++;
        }
    }
    /* else we need to steal slots (OPTIMIZE) */

    return ret;
}

/* internal function to construct a query structure from a given string (query)
 * of length len.  At most maxterms will be read from the query. */ 
unsigned int index_querybuild(struct index *idx, struct query *query, 
  const char *querystr, unsigned int len, unsigned int maxterms, 
  unsigned int maxtermlen, int impacts) {
    struct queryparse *qp;           /* structure to parse the query */
    struct conjunct *current = NULL; /* pointer to a current conjunction */
    char word[TERMLEN_MAX + 1];      /* buffer to hold words */
    unsigned int i,                  /* counter */
                 wordlen,            /* length of word */
                 words = 0,          /* number of words parsed */
                 currmatch = 0;      /* number of matches against current 
                                      * entry */
                 /* veclen; */
    int state = CONJUNCT_TYPE_WORD,  /* state variable, can take on values 
                                      * from conjunct types enum */
        stopped = 0;                 /* whether the last word was stopped */
    /* void *ve;  */                 /* compressed vocabulary entry for a 
                                      * word */
    enum queryparse_ret parse_ret;   /* value returned by parser */
    /* last modifier seen; also, are we in a modifier */
    enum { MODIFIER_NONE, MODIFIER_SLOPPY, MODIFIER_CUTOFF } modifier 
      = MODIFIER_NONE;
    void (*stem)(void *, char *) = index_stemmer(idx);

    assert(maxtermlen <= TERMLEN_MAX);
    if (!(qp 
      = queryparse_new(maxtermlen, querystr, len))) {
        return 0;
    }

    query->terms = 0;

    /* This bit of code builds a structure that represents a query from an
     * array, where the array of words will be filled from 0 upwards, and
     * conjunctions that require a linked list of words (phrase, AND) take
     * additional words from the end of the array. */

    do {
        struct vocab_vector entry;
        int retval;
        char vec_buf[MAX_VOCAB_VECTOR_LEN];
        parse_ret = queryparse_parse(qp, word, &wordlen);
        switch (parse_ret) {
        case QUERYPARSE_WORD_EXCLUDE:
            /* this functionality not included yet, just ignore the word for 
             * now */

            /* look up word in vocab */
            /* ve = hFetch(word, idx->vocab, NULL); */

            /* OPTIMIZE: search existing conjunctions for word and remove 
             * them */

            /* FIXME: stop word */
            /* if (ve) {
                conjunct_add(query, ve, CONJUNCT_TYPE_EXCLUDE, 
                  &maxterms);
            } */

            current = NULL;   /* this can't be the start of a conjunction */
            words++;
            break;

        case QUERYPARSE_WORD_NOSTOP:
        case QUERYPARSE_WORD:
            if (modifier != MODIFIER_NONE) {
                /* this is not a query term, but an argument to a modifier */
                switch (modifier) {
                case MODIFIER_SLOPPY:
                    if (query->terms > 0)
                        query->term[query->terms - 1].sloppiness = atoi(word);
                    break;

                case MODIFIER_CUTOFF:
                    if (query->terms > 0)
                        query->term[query->terms - 1].cutoff = atoi(word);
                    break;

                default:
                    /* FIXME WARN */
                    break;
                }
                break;
            }
            /* look up word in vocab */
            /* FIXME: word needs to be looked up in in-memory postings as 
             * well */
            if (stem) {
                word[wordlen] = '\0';
                stem(idx->stem, word);
                wordlen = str_len(word);
            }
            retval = get_vocab_vector(idx->vocab, &entry, word, wordlen,
              vec_buf, sizeof(vec_buf), impacts);
            if (retval < 0) {
                return 0;
            } else if (retval == 0) {
                stopped = 0;   /* so we know that this term wasn't stopped */
                currmatch = 1; /* so that we know that phrases have started */
                if (current && (state == CONJUNCT_TYPE_AND)) {
                    /* need to remove current conjunction, as it contains a word
                     * that isn't in the collection */
                    if (current->f_qt > 1) {
                        current->f_qt--;
                    } else {
                        state = CONJUNCT_TYPE_WORD;   /* stop AND condition */
                        maxterms += current->terms - 1;
                        query->terms--;
                    }
                } else if (current && (state == CONJUNCT_TYPE_PHRASE)) {
                    /* same, except phrase continues until end-phrase */
                    if (current->f_qt > 1) {
                        current->f_qt--;
                    } else {
                        maxterms += current->terms - 1;
                        query->terms--;
                    }
                }
                current = NULL;
            } else if (state == CONJUNCT_TYPE_PHRASE) {
                /* OPTIMIZE: check word against excluded terms */
                struct term *currterm;

                /* processing a phrase */
                if (!currmatch) {
                    /* first word in phrase, match or add a conjunction */
                    current = conjunct_add(query, &entry,
                      /* ve, veclen,  */
                      word, wordlen, 
                      CONJUNCT_TYPE_PHRASE, &maxterms);
                    currmatch = 1;
                } else if (current && (current->f_qt > 1)) {
                    /* we're matching an existing phrase */
 
                    /* iterate to next term we need to match */
                    for (i = 0, currterm = &current->term; i < currmatch; 
                      i++, currterm = currterm->next) ;

                    if (currterm && !str_cmp(currterm->term, word)) {
                        /* matched */
                        currmatch++;
                    } else {
                        /* didn't match, copy non-matching phrase */
                        current->f_qt--;
                        current = conjunct_copy(query, current, currmatch, 
                          &entry, word, wordlen, &maxterms);
                        currmatch++;
                    }
                } else if (current) {
                    /* we're building a new phrase, add next word on */
                    conjunct_append(query, current, 
                      &entry,
                     /* ve, veclen, */
                      word, wordlen, 
                      &maxterms);
                    currmatch++;
                }
                /* otherwise we're ignoring this phrase (because it contains a
                 * word thats not in the vocab) */

            } else if (state == CONJUNCT_TYPE_AND) {
                /* we are constructing an AND conjunction */

                /* FIXME: stop word 
                stopped = 1;
                current = NULL; */

                /* OPTIMIZE: check word against excluded terms */

                if (current) {
                    if ((current->type == CONJUNCT_TYPE_AND) 
                      || (current->f_qt == 1)) {
                        /* add to current conjunct */
                        conjunct_append(query, current, &entry,
                          word, wordlen, &maxterms);
                        current->type = CONJUNCT_TYPE_AND;
                    } else {
                        /* copy matched word to new location for AND conjunct */
                        current->f_qt--;
                        current = conjunct_copy(query, current, 1, &entry,
                          word, wordlen, &maxterms);
                        current->type = CONJUNCT_TYPE_AND;
                    }
                } else if (stopped) { 
                    /* first word(s) in conjunct was stopped, so start a new
                     * one */
                    current = conjunct_add(query, &entry, word, wordlen,
                      CONJUNCT_TYPE_WORD, &maxterms);
                }

                state = CONJUNCT_TYPE_WORD;   /* stop AND condition */
            } else if (state == CONJUNCT_TYPE_WORD) {
                /* its a single word */
                stopped = 0;
                if (parse_ret != QUERYPARSE_WORD_NOSTOP) {
                    word[wordlen] = '\0';
                    if (idx->qstop 
                      && stop_stop(idx->qstop, word) == STOP_STOPPED) {
                        /* it is a stopword */
                        stopped = 1;
                        current = NULL;
                    }
                }

                if (!stopped) {
                    current = conjunct_add(query, &entry,
                      /* ve, veclen, */
                      word, wordlen,
                      CONJUNCT_TYPE_WORD, &maxterms);
                    currmatch = 1;
                }
            }

            words++;
            break;

        case QUERYPARSE_OR:
            state = CONJUNCT_TYPE_WORD;  /* or is the default mode anyway */
            break;

        case QUERYPARSE_AND:
            state = CONJUNCT_TYPE_AND;
            break;

        case QUERYPARSE_START_PHRASE: 
            /* phrase starts */
            state = CONJUNCT_TYPE_PHRASE;
            current = NULL;
            currmatch = 0;
            break;

        case QUERYPARSE_END_PHRASE:
            if (current && (current->terms != currmatch)) {
                /* partial match, need to copy phrase */
                current->f_qt--;
                current = conjunct_copy(query, current, currmatch, NULL,
                  NULL, 0, &maxterms);
            }

            /* treat single-word phrases as, well, words */
            if (current && (current->terms == 1)) {
                struct conjunct *ret;
                /* see if this single-word occurred previously */
                ret = conjunct_find(query, &current->term.vocab,
                  current->term.term, str_len(current->term.term), 
                  CONJUNCT_TYPE_WORD);
                if (ret == NULL) {
                    /* ok, this is the first occurence */
                    current->type = CONJUNCT_TYPE_WORD;
                } else {
                    /* there was a previous occurence: increment its f_qt,
                       and free this one */
                    ret->f_qt++;
                    assert(current == &query->term[query->terms - 1]);
                    free(current->term.term);
                    if (current->term.vocab.location == VOCAB_LOCATION_VOCAB) {
                        free(current->term.vecmem);
                    }
                    query->terms--;
                }
            }
            current = NULL;
            state = CONJUNCT_TYPE_WORD;
            break;

        case QUERYPARSE_END_SENTENCE: 
            /* we're ignoring this at the moment - it might be used later if
             * we don't want to match phrases across sentence boundaries */
            break;

        case QUERYPARSE_END_MODIFIER: 
            modifier = MODIFIER_NONE;
            break;
        case QUERYPARSE_START_MODIFIER: 
            if (str_casecmp(word, "sloppy") == 0) 
                modifier = MODIFIER_SLOPPY;
            else if (str_casecmp(word, "cutoff") == 0) 
                modifier = MODIFIER_CUTOFF;
            else
                /* FIXME WARN */
                modifier = MODIFIER_NONE;
            break;

        case QUERYPARSE_EOF: break; /* this will finish the parse */

        default:
            /* unexpected return code, error */
            queryparse_delete(qp);
            return 0;
        }
    } while ((parse_ret != QUERYPARSE_EOF)
      && (query->terms < maxterms));  /* FIXME: temporary stopping condition */

    queryparse_delete(qp);
    /* returning word count confuses errors with empty queries. */
    /* return words; */
    return 1;
}



/* internal function to compare phrase term pointers by frequency/estimated
 * frequency */
static int f_t_cmp(const void *one, const void *two) {
    const struct conjunct *done = one,
                          *dtwo = two;

    if (done->f_t < dtwo->f_t) {
        return -1;
    } else if (done->f_t > dtwo->f_t) {
        return 1;
    } else {
        return 0;
    }
}

/* internal function to compare phrase term pointers by frequency/estimated
 * frequency */
static int F_t_cmp(const void *one, const void *two) {
    const struct conjunct *done = one,
                          *dtwo = two;

    if (done->F_t < dtwo->F_t) {
        return -1;
    } else if (done->F_t > dtwo->F_t) {
        return 1;
    } else {
        return 0;
    }
}

/* internal function to compare phrase term pointers by frequency/estimated
 * frequency */
static int loc_cmp(const void *one, const void *two) {
    const struct termsrc *done = one,
                         *dtwo = two;

    /* order terms that have already been read toward the bottom */
    if (done->term->vecmem || dtwo->term->vecmem) {
        if (done->term->vecmem) {
            return 1;
        } else {
            return -1;
        }
    }

    assert(done->term->term.vocab.location == VOCAB_LOCATION_FILE);
    assert(dtwo->term->term.vocab.location == VOCAB_LOCATION_FILE);

    if (done->term->term.vocab.loc.file.fileno 
      == dtwo->term->term.vocab.loc.file.fileno) {
        if (done->term->term.vocab.loc.file.offset 
          < dtwo->term->term.vocab.loc.file.offset) {
            return -1;
        } else if (done->term->term.vocab.loc.file.offset 
          > dtwo->term->term.vocab.loc.file.offset) {
            return 1;
        } else {
            assert("can't get here" && 0);
            return 0;
        }
    } else {
        return dtwo->term->term.vocab.loc.file.fileno
          - done->term->term.vocab.loc.file.fileno;
    }
}

static int term_cmp(const void *one, const void *two) {
    const struct termsrc *done = one,
                         *dtwo = two;
    return done->term - dtwo->term;
}


/* structure to allow sourcing of a list from a single, contiguous
 * location in memory */
struct memsrc {
    struct search_list_src src;
    void *mem;
    unsigned int len;
    int returned;
};

static void memsrc_delete(struct search_list_src *src) {
    free(src);
}

static enum search_ret memsrc_read(struct search_list_src *src, 
  unsigned int leftover, void **retbuf, unsigned int *retlen) {
    struct memsrc *msrc = src->opaque;

    if (leftover) {
        return SEARCH_EINVAL;
    }

    if (msrc->returned || !msrc->len) {
        return SEARCH_FINISH;
    }

    msrc->returned = 1;
    *retbuf = msrc->mem;
    *retlen = msrc->len;
    return SEARCH_OK;
}

static enum search_ret memsrc_reset(struct search_list_src *src) {
    struct memsrc *msrc = src->opaque;

    msrc->returned = 0;
    return SEARCH_OK;
}

static struct search_list_src *memsrc_new(void *mem, unsigned int len) {
    struct memsrc *msrc = malloc(sizeof(*msrc));

    if (msrc) {
        msrc->mem = mem;
        msrc->len = len;
        msrc->returned = 0;
        msrc->src.opaque = msrc;
        msrc->src.delet = memsrc_delete;
        msrc->src.reset = memsrc_reset;
        msrc->src.readlist = memsrc_read;
    }
    return &msrc->src;
}

static struct search_list_src *memsrc_new_from_disk(struct index *idx, 
  unsigned int type, unsigned int fileno, unsigned long int offset, 
  unsigned int size, void *mem) {
    unsigned int bytes = size;
    char *pos;
    int fd = fdset_pin(idx->fd, type, fileno, offset, SEEK_SET);
    ssize_t read_bytes;

    if ((fd >= 0) && (pos = mem)) {
        do {
            read_bytes = read(fd, pos, bytes);
        } while ((read_bytes != -1) 
          && (pos += read_bytes, bytes -= read_bytes));

        fdset_unpin(idx->fd, type, fileno, fd);
        if (!bytes) {
            return memsrc_new(mem, size);
        }
    } else {
        if (fd >= 0) {
            fdset_unpin(idx->fd, type, fileno, fd);
        }
    }
    return NULL;
}



/* FIXME: structure to allow sourcing of a list from a bucket on disk */

/* structure to allow sourcing of a list from an fd */
struct disksrc {
    struct search_list_src src;      /* parent source structure */
    struct alloc alloc;              /* buffer allocation object */
    char *buf;                       /* available buffer */
    unsigned int bufsize;            /* size of stuff in buffer */
    unsigned int bufcap;             /* capacity of buffer */
    unsigned long int bufpos;        /* position buffer was read from */
    unsigned int size;               /* size of the list */
    unsigned int pos;                /* position in list */

    struct index *idx;               /* index we're using */
    int fd;                          /* pinned fd */
    unsigned int type;               /* the type of the fd */
    unsigned int fileno;             /* the file number of the fd */
    unsigned long int offset;        /* starting offset of the list */
};

static enum search_ret disksrc_reset(struct search_list_src *src) {
    struct disksrc *dsrc = src->opaque;
    dsrc->pos = 0;
    return SEARCH_OK;
}

static enum search_ret disksrc_read(struct search_list_src *src, 
  unsigned int leftover, void **retbuf, unsigned int *retlen) {
    struct disksrc *dsrc = src->opaque;

    /* this routine is somewhat complex because we'd like to handle cases where
     * an initial read, a reset, followed by another read incur only one seek
     * and one read. */

    if (leftover > dsrc->bufsize || leftover >= dsrc->bufcap 
      /* if we're requesting leftover bytes, we should just have read a
       * bufferload */
      || (leftover && dsrc->bufpos + dsrc->bufsize != dsrc->pos)) {
        assert("can't get here" && 0);
        return SEARCH_EINVAL;
    }

    if (dsrc->pos >= dsrc->bufpos 
      && (dsrc->pos < dsrc->bufpos + dsrc->bufsize)) {
        unsigned int len;
        /* buffer can be used to answer request */
        assert(!leftover);

        len = dsrc->pos - dsrc->bufpos;
        *retbuf = dsrc->buf + len;
        *retlen = dsrc->bufsize - len;
        dsrc->pos += *retlen;
        return SEARCH_OK;
    } else {
        ssize_t bytes,
                cap = dsrc->size - dsrc->pos;

        if (dsrc->pos != dsrc->bufpos + dsrc->bufsize) {
            /* need to seek before reading */
            off_t newoff;
            assert(!leftover);

            dsrc->bufsize = 0;
            if ((newoff = lseek(dsrc->fd, dsrc->offset + dsrc->pos, SEEK_SET)) 
              != (off_t) dsrc->offset) {
                return SEARCH_EINVAL;
            }
        }

        dsrc->bufpos = dsrc->pos - leftover;

        if (leftover) {
            /* preserve leftover bytes */
            memmove(dsrc->buf, dsrc->buf + dsrc->bufsize - leftover, leftover);
        }
        dsrc->bufsize = leftover;

        if (!cap) {
            if (leftover) {
                *retbuf = dsrc->buf;
                *retlen = dsrc->bufsize;
                return SEARCH_OK;
            } else {
                return SEARCH_FINISH;
            }
        }

        /* limit amount we try to read to available buffer size */
        if ((unsigned int) cap > dsrc->bufcap - dsrc->bufsize) {
            cap = dsrc->bufcap - dsrc->bufsize;
        }

        while ((bytes = read(dsrc->fd, dsrc->buf + dsrc->bufsize, cap)) == -1) {
            switch (errno) {
            case EINTR: /* do nothing, try again */ break;
            case EIO: return SEARCH_EIO;
            default: return SEARCH_EINVAL;
            }
        }
        dsrc->bufsize += bytes;
        dsrc->pos += bytes;

        *retbuf = dsrc->buf;
        *retlen = dsrc->bufsize;

        if (dsrc->bufsize) {
            return SEARCH_OK;
        } else {
            return SEARCH_FINISH;
        }
    }
}

static void disksrc_delete(struct search_list_src *src) {
    struct disksrc *dsrc = src->opaque;

    dsrc->alloc.free(dsrc->alloc.opaque, dsrc->buf);
    fdset_unpin(dsrc->idx->fd, dsrc->type, dsrc->fileno, dsrc->fd);
    free(src);
    return;
}

static struct search_list_src *disksrc_new(struct index *idx, 
  unsigned int type, unsigned int fileno, unsigned long int offset, 
  unsigned int size, struct alloc *alloc, unsigned int mem) {
    int fd = fdset_pin(idx->fd, type, fileno, offset, SEEK_SET);

    if (mem > size) {
        mem = size;
    }

    if (fd >= 0) {
        struct disksrc *dsrc = malloc(sizeof(*dsrc));

        if (dsrc && (dsrc->buf = alloc->malloc(alloc->opaque, mem))) {
            dsrc->src.opaque = dsrc;
            dsrc->src.delet = disksrc_delete;
            dsrc->src.reset = disksrc_reset;
            dsrc->src.readlist = disksrc_read;

            /* ensure that nothing gets served out of the buffer first time */
            dsrc->bufpos = -1;  
            dsrc->bufsize = 0;

            dsrc->alloc = *alloc;
            dsrc->bufcap = mem;
            dsrc->pos = 0;
            dsrc->fd = fd;
            dsrc->idx = idx;
            dsrc->type = type;
            dsrc->fileno = fileno;
            dsrc->offset = offset;
            dsrc->size = size;
            return &dsrc->src;
        } else {
            if (dsrc) {
                free(dsrc);
            }
            fdset_unpin(idx->fd, type, fileno, fd);
        }
    }

    return NULL;
}

struct search_list_src *search_term_src(struct index *idx, struct term *term,
  struct alloc *alloc, unsigned int mem) {
    if (term->vecmem) {
        /* memory source */
        assert(term->vocab.location == VOCAB_LOCATION_VOCAB);
        return memsrc_new(term->vecmem, term->vocab.size);
    } else {
        /* disk source */
        assert(term->vocab.location == VOCAB_LOCATION_FILE);
        return disksrc_new(idx, idx->index_type, 
            term->vocab.loc.file.fileno, term->vocab.loc.file.offset, 
            term->vocab.size, alloc, mem);
    }
}

/* internal function to return the correct source for a given term */
struct search_list_src *search_conjunct_src(struct index *idx, 
  struct conjunct *conj, struct alloc *alloc, unsigned int memlimit) {
    if (conj->vecmem) {
        /* memory source */
        return memsrc_new(conj->vecmem, conj->vecsize);
    } else {
        /* source from term */
        return search_term_src(idx, &conj->term, alloc, memlimit);
    }
}






/* macro to atomically read the next docno and f_dt from a vector 
 * (note: i also tried a more complicated version that tested for a long vec 
 * and used unchecked reads, but measurements showed no improvement) */
#define NEXT_DOC(v, docno, f_dt)                                              \
    (vec_vbyte_read(v, &docno_d)                                              \
      && (((vec_vbyte_read(v, &f_dt) && ((docno += docno_d + 1), 1))          \
        /* second read failed, reposition vec back to start of docno_d */     \
        || (((v)->pos -= vec_vbyte_len(docno_d)), 0))))

/* macro to scan over f_dt offsets from a vector/source */
#define SCAN_OFFSETS(src, v, f_dt)                                            \
    do {                                                                      \
        unsigned int toscan = f_dt,                                           \
                     scanned;                                                 \
        enum search_ret sret;                                                 \
                                                                              \
        do {                                                                  \
            if ((scanned = vec_vbyte_scan(v, toscan, &scanned)) == toscan) {  \
                toscan = 0;                                                   \
                break;                                                        \
            } else if (scanned < toscan) {                                    \
                toscan -= scanned;                                            \
                /* need to read more */                                       \
                if ((sret = src->readlist(src, VEC_LEN(v),                    \
                    (void **) &(v)->pos, &bytes)) == SEARCH_OK) {             \
                                                                              \
                    (v)->end = (v)->pos + bytes;                              \
                } else if (sret == SEARCH_FINISH) {                           \
                    /* shouldn't end while scanning offsets */                \
                    return SEARCH_EINVAL;                                     \
                } else {                                                      \
                    return sret;                                              \
                }                                                             \
            } else {                                                          \
                assert("can't get here" && 0);                                \
                return SEARCH_EINVAL;                                         \
            }                                                                 \
        } while (toscan);                                                     \
    } while (0)


/* internal function to evaluate a query structure using document ordered
 * inverted lists and place the results into an accumulator linked list */
enum prune_ret prune(struct index *idx, 
  struct poolalloc *list_alloc,
  int opts, struct index_search_opt *opt) {

	

	unsigned int state[3] = {0, 0, 0};
    void *data;
    unsigned int datalen,
                 tmp;
    struct vocab_vector vv;
    const char *tmpTerm;
	char term[25];
    unsigned int capacity,
		fileno;       
    unsigned long int offset;
	int ret;
	FILE *output;
	unsigned int i = 0;
	unsigned long int docs,
		occurs,
		last;
	unsigned int scanned;
	struct termsrc trm;	
	
	output = fopen("vocabulary.txt", "w+");

	fprintf(output, "docs = number of documents term occurs in\n");
	fprintf(output, "occurs = total number of times term occurrs\n");
	fprintf(output, "last = last docno in vector\n");
	fprintf(output, "capacity = how much space is there \n");
	fprintf(output, "fileno = number of file its in\n");
	fprintf(output, "offset = offset it's at\n");
	fprintf(output, "length = returns the length in bytes of a vocab vector\n");
	fprintf(output, "size = size of stored vector\n");
	//fprintf(output, "\n");
	//fprintf(output, "\n");
	fprintf(output, "                TERM    DOCS    OCCURS    LAST    SIZE    LENGTH    CAPACITY    FILENO     OFFSET\n");     

	while ((tmpTerm = iobtree_next_term(idx->vocab, state, &tmp, &data, &datalen))) {
		unsigned int bytes;
        unsigned int info;
        struct vec v;
        enum vocab_ret vret;
		
		trm.src = NULL;	
		for (i = 0; i < tmp; i++) {
			term[i] = tmpTerm[i];
		}
		while(i < 25){
			term[i++] = '\0';
		}

        v.pos = data;
        v.end = v.pos + datalen;

        while ((vret = vocab_decode(&vv, &v)) == VOCAB_OK) {
			unsigned long int f_dt,        /* number of offsets for this document */
				          docno_d;     /* d-gap */
			unsigned long int docno = SEARCH_DOCNO_START;		          
			void *mem;
			int exitwhile = 1;
			bytes = vocab_len(&vv);
            assert(bytes);
            //stats->vectors += vv.size;
            info = vec_vbyte_len(vv.header.doc.docs) 
              + vec_vbyte_len(vv.header.doc.occurs) 
              + vec_vbyte_len(vv.header.doc.last) + vec_vbyte_len(vv.size);
            //stats->vocab_info += vec_vbyte_len(tmp) + tmp + info;
            assert(bytes > info);
            //stats->vocab_structure += bytes - info;


			/* returns the number of docs from a vocab vector */
			docs = vocab_docs(&vv);
			/* returns the number of occurences from a vocab vector */
			occurs = vocab_occurs(&vv);
			/* returns the last docnum from a vocab vector */
			last = vocab_last(&vv);			

	fprintf(output, "                TERM    DOCS    OCCURS    LAST    SIZE    LENGTH    CAPACITY    FILENO     OFFSET\n");     

			fprintf(output, "%20s %7lu %9lu %7lu %7u %9lu %11u %9u %10lu\n", 
				term, bytes, docs, occurs, last, vv.size, vv.loc.file.capacity, vv.loc.file.fileno, vv.loc.file.offset);

	        
			fprintf(output, "location = %u\n", vv.location);
		    if ((vv.location == VOCAB_LOCATION_FILE)
		      && (mem = poolalloc_malloc(list_alloc, vv.size))
		      && (trm.src = memsrc_new_from_disk(idx, idx->index_type, 
		           vv.loc.file.fileno, 
		          vv.loc.file.offset, 
		          vv.size, mem))
				 ) {
	//	static struct search_list_src *memsrc_new_from_disk(struct index *idx, 
	//  unsigned int type, unsigned int fileno, unsigned long int offset, 
	//  unsigned int size, void *mem)
				//printf("fileno : %u\noffset: %lu\nsize: %u\n", srcarr[i].term->term.vocab.loc.file.fileno,
				//srcarr[i].term->term.vocab.loc.file.offset, srcarr[i].term->term.vocab.size);
				printf("mem = %d\n", mem);
				printf("mem in srcarr = %d\n", ((struct memsrc *) trm.src->opaque)->mem);
	            /* succeeded, do nothing */
	        } else if ((vv.location == VOCAB_LOCATION_FILE)) {

				
				/* failed to allocate or read new source */
	         //   free(srcarr);
			//				   return -1;
	        }
	    
			while(exitwhile){
				while (NEXT_DOC(&v, docno, f_dt)) {
					
					SCAN_OFFSETS(trm.src, &v, f_dt);
					fprintf(output, "scanned = %u\n", scanned);
					fprintf(output, "<docno = %u,f_dt= %u>, ", docno, f_dt); 
				}
				if ((ret = trm.src->readlist(trm.src, VEC_LEN(&v),
					(void **) &v.pos, &bytes)) == SEARCH_OK) {
					//fprintf(output, "bbbbbb\n");
					v.end = v.pos + bytes;
				} else if (ret == SEARCH_FINISH) {
					//fprintf(output, "cccccc\n");
					/* finished, update number of accumulators */

					if (!VEC_LEN(&v)) {
						//fprintf(output, "burdayim1\n");
						exitwhile = 0;
					} else {
						//fprintf(output, "burdayim1\n");
						exitwhile = 0;
					}
				} else {
					exitwhile = 0;
				}
			}
			fprintf(output, "\n");
		
		}
    }
	return PRUNE_OK;
}

/* internal function to compare accumulators based on accumulated weight */
static int accumulator_cmp(const void *vone, const void *vtwo) {
    const struct search_acc *one = vone,
                            *two = vtwo;
 				 		printf("----search.c-----accumulator_cmp\n");

    if (one->weight < two->weight) {
        return -1;
    } else if (one->weight > two->weight) {
        return 1;
    } else {
        /* sub-rank by docid, so that at least we impose a clear, deterministic
         * order upon the results.  Two accumulators with the same score are
         * unlikely anyway. */
        if (one->docno < two->docno) {
            return -1;
        } else if (one->docno > two->docno) {
            return 1;
        } else {
            /* shouldn't get two accumulators with the same docno */
            assert(0);
            return 0;
        }
    }
}

/* internal functions to sort accumulators in a list into an array */
static void sort_hash(struct search_acc *heap, unsigned int heapsize, 
  struct chash *acc) {
    unsigned int i,
                 j,
                 hashsize = chash_size(acc);
    struct chash_link *link = NULL;
    struct search_acc *lowest,
                      tmp;
    float lowest_weight;
 				 		printf("----search.c-----sort_hash\n");

    /* fill heap with accumulators in the order they occur */
    for (i = 0, j = 0; j < heapsize; i++) {
        link = acc->table[i];
        while (link && (j < heapsize)) {
            heap[j].docno = link->key.k_luint;
            heap[j].weight = (float) link->data.d_luint;

            j++;
            link = link->next;
        }
    }

    /* heapify heap, so the we know what the lowest accumulator in it is */
    heap_heapify(heap, heapsize, sizeof(*heap), accumulator_cmp);
    lowest = heap_peek(heap, heapsize, sizeof(*heap));
    lowest_weight = lowest->weight;

    /* continue traversing hashtable, replacing lowest element whenever we find
     * one higher than it (note this loop finishes last chain as well) */
    do {
        while (link) {
            if (link->data.d_luint > lowest_weight) {
                /* replace smallest element in heap with a larger one */
                tmp.docno = link->key.k_luint;
                tmp.weight = (float) link->data.d_luint;
                heap_replace(heap, heapsize, sizeof(*heap), 
                  accumulator_cmp, &tmp);
                lowest = heap_peek(heap, heapsize, sizeof(*heap));
                lowest_weight = lowest->weight;
            }
            j++;
            link = link->next;
        }
    } while ((j < hashsize)
      && ((link = acc->table[i++]), 1)); /* get next entry and cont */

    assert((j == chash_size(acc)) && (j == hashsize));

    /* we now have all of the largest accumulators.  Continue heaping, taking
     * the smallest element from the back of the array and copying it to the
     * front. */
    while (heapsize > 1) {
        /* note: shrink heapsize by one, copy smallest element into space
         * we just past */
        heap_pop(heap, &heapsize, sizeof(*heap), accumulator_cmp);
    }
}

/* internal functions to sort accumulators in a list into an array */
static void sort_list(struct search_acc *heap, unsigned int heapsize, 
  struct search_acc_cons *acc) {
    unsigned int i;
    struct search_acc *lowest;
    float lowest_weight;
 				 		printf("----search.c-----sort_list\n");

    /* fill heap with accumulators in the order they occur */
    for (i = 0; i < heapsize; i++, acc = acc->next) {
        assert(acc);
        heap[i] = acc->acc;
    }

    /* heapify heap, so the we know what the lowest accumulator in it is */
    heap_heapify(heap, heapsize, sizeof(*heap), accumulator_cmp);
    lowest = heap_peek(heap, heapsize, sizeof(*heap));
    lowest_weight = lowest->weight;

    /* continue traversing accumulators, replacing lowest element whenever we 
     * find one higher than it */
    while (acc) {
        if (acc->acc.weight > lowest_weight) {
            /* replace smallest element in heap with a larger one */
            heap_replace(heap, heapsize, sizeof(*heap), 
              accumulator_cmp, &acc->acc);
            lowest = heap_peek(heap, heapsize, sizeof(*heap));
            lowest_weight = lowest->weight;
        }
        acc = acc->next;
    }

    /* we now have all of the largest accumulators.  Continue heaping, taking
     * the smallest element from the back of the array and copying it to the
     * front. */
    while (heapsize > 1) {
        /* note: shrink heapsize by one, copy smallest element into space
         * we just past */
        heap_pop(heap, &heapsize, sizeof(*heap), accumulator_cmp);
    }
}
/* internal function to select the top len results, starting from startdoc, 
 * into the results array from accumulators, either hashed or in a list. */
static unsigned int index_heap_select(struct index *idx, 
  struct index_result *results, unsigned int startdoc, unsigned int len, 
  struct search_acc_cons *acc, unsigned int accs, struct chash *hashacc) {
    struct search_acc *heap;
    unsigned int i,
                 numdocs = startdoc + len,
                 heapsize;
 				 		printf("----search.c-----index_heap_select\n");

    if (accs <= startdoc) {
        /* not enough accumulators to get to desired result */
        return 0;
    } else if (numdocs > accs) {
        /* not enough accumulators to get all of desired results */
        numdocs = accs;
    }

    /* allocate a heap of startdoc + len elements */
    if (!(heap = malloc(sizeof(*heap) * numdocs))) {
        return 0;
    }
    heapsize = numdocs;

    if (!hashacc) {
        /* accumulators as list */
        sort_list(heap, heapsize, acc);
    } else {
        /* accumulators as hash table */
        sort_hash(heap, heapsize, hashacc);
    }

    /* copy relevant accumulators into results (this loop form works properly 
     * if less than startdoc + len documents match the query - think before 
     * changing it) */ 
    for (i = startdoc; i < numdocs; i++) {
        unsigned aux_len = 0;
        enum docmap_ret ret;

        results[i - startdoc].docno = heap[i].docno;
        results[i - startdoc].score = heap[i].weight;

        /* lookup document auxilliary */
        ret = docmap_get_trecno(idx->map, heap[i].docno, 
          results[i - startdoc].auxilliary, INDEX_AUXILIARYLEN, &aux_len);
        if (ret != DOCMAP_OK) {
            return 0;
        }
        if (aux_len > INDEX_AUXILIARYLEN) {
            aux_len = INDEX_AUXILIARYLEN;
        }
        results[i - startdoc].auxilliary[aux_len] = '\0';

        /* summary and title provided later */
        results[i - startdoc].summary[0] = '\0';
        results[i - startdoc].title[0] = '\0';
    }

    free(heap);                        /* free heap */
    return i - startdoc;
}
