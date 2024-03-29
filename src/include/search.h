/* _search.h declares the internal details of how searching works.
 * Not much in here at the moment.
 *
 * written nml 2005-05-11
 *
 */

#ifndef SEARCH_H
#define SEARCH_H

#ifdef __cplusplus
extern "C" {
#endif

#include "def.h"

enum search_ret {
    SEARCH_OK = 0,
    SEARCH_FINISH = 1,        /* no error, but at the end */
    SEARCH_ENOMEM = -1,
    SEARCH_EINVAL = -2,
    SEARCH_EAGAIN = -3,
    SEARCH_EIO = -4 
};

struct termsrc {
    struct conjunct *term;
    struct search_list_src *src;
};

/* structure to accumulate the weight for a document during ranking */
struct search_acc {
    unsigned long int docno;
    float weight;
};

/* linked list of accumulators */
struct search_acc_cons {
    struct search_acc_cons *next;
    struct search_acc acc;
};

/* declaration we'll need for the metric structure below */
struct query;
struct objalloc;
struct index;
struct index_search_opt;

/* struct to model the operation of a source of compressed postings */
struct search_list_src {
    void *opaque;
    /* method to reset the list src to the start of the list */
    enum search_ret (*reset)(struct search_list_src *src);
    /* method to read bytes from the src into buf, which is of length len.
     * read_len contains the number of bytes written into the buffer when the
     * return value is SEARCH_OK, with 0 indicating that the end of the list has
     * been reached.  leftover indicates how many bytes where left from the
     * previous read, and need to be preserved in the next bufferload.  Note
     * that this could be handled elsewhere, but making it the responsibility of
     * the reader simplifies things in the face of different buffer sources,
     * since the source can either adjust the existing buffer or read the extra
     * few bytes again. */
    enum search_ret (*readlist)(struct search_list_src *src, 
      unsigned int leftover, void **retbuf, unsigned int *retlen);
    /* method to delete the src structure and free all resources used by it */
    void (*delet)(struct search_list_src *src);
};

/* structure to represent results being passed between evaluation calls */
struct search_metric_results {
     struct search_acc_cons *acc;     /* list of accumulators */
     unsigned int accs;               /* count of accumulators */
     unsigned int acc_limit;          /* 'soft' accumulator limit */
     struct objalloc *alloc;          /* allocator for acc's */
     float v_t;                       /* threshold for accepting accumulators */
     int estimated;                   /* whether total_results is estimated */
     double total_results;            /* total number of possible results for 
                                       * this query */
};

/* structure containing a set of functions that define a metric over document 
 * ordered lists.  Each function accepts options in the same flags and 
 * structure form as index_search.  Here are the meanings of common arguments:
 *   idx: index which we are evaluating the query on
 *   query: user query that we are evaluating 
 *   qterm: index of the term in the query that we're dealing with
 *   start_docno: what document number to start decoding the list relative to.
 *                use SEARCH_DOCNO_START if decoding from the start of a list
 *   src: list to decode
 *   postings: number of documents in list v.  This will often 
 *             (but not always) be equal to f_t
 *   opts: option flags, from index_search
 *   opt: option structure, from index_search
 */
struct search_metric {
    /* prepares to evaluate the metric on index idx */
    enum search_ret (*pre)(struct index *idx, struct query *query, 
      int opts, struct index_search_opt *opt);

    /* post-processes (typically this involves document length normalisation) 
     * accumulators that have been generated by the xxx_decode fns */
    enum search_ret (*post)(struct index *idx, struct query *query, 
      struct search_acc_cons *acc, int opts, struct index_search_opt *opt);

    /* decode a list in OR mode (initialising new accumulators) */
    enum search_ret (*or_decode)(struct index *idx, struct query *query, 
      unsigned int qterm, unsigned long int start_docno, 
      struct search_metric_results *results, struct search_list_src *src,
      int opts, struct index_search_opt *opt);

    /* decode a list in AND mode (not initialising new accumulators) */
    enum search_ret (*and_decode)(struct index *idx, struct query *query, 
      unsigned int qterm, unsigned long int start_docno, 
      struct search_metric_results *results, struct search_list_src *src,
      int opts, struct index_search_opt *opt);

    /* decode a list in THRESH mode (hueristically attempts to initialise 
     * accumulators only for the highest scoring documents in the list).
     * results->acc_limit is the accumulator limit that we are trying to reach.
     * results->v_t is the current threshold, which is updated during the 
     * course of the procedure.  
     * thresh_decode can return SEARCH_FINISH to indicate that
     * AND processing should be performed on the subsequent lists. */
    enum search_ret (*thresh_decode)(struct index *idx, struct query *query,
      unsigned int qterm, unsigned long int start_docno, 
      struct search_metric_results *results, 
      struct search_list_src *src, unsigned int postings, 
      int opts, struct index_search_opt *opt);
};

/* constant to pass as start_docno when decoding from the start of a list */
#define SEARCH_DOCNO_START -1

/* function to return the number of terms in a query structure */
unsigned int search_qterms(struct query *q);

/* function to return the cosine weight of a query structure */
float search_qweight(struct query *q);

#include "alloc.h"
#include "index_querybuild.h"

// #include "index_prune.h"

/* function to return a list source for a given term (FIXME: move to a different
 * module) */
struct search_list_src *search_term_src(struct index *idx, struct term *term,
  struct alloc *alloc, unsigned int mem);

#ifdef __cplusplus
}
#endif

#endif

