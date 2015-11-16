/* index_prune.h 
 */

#ifndef INDEX_PRUNE_H
#define INDEX_PRUNE_H

#ifdef __cplusplus
extern "C" {
#endif

#include "vocab.h"

struct index;

enum prune_ret {
    PRUNE_OK = 0,
    PRUNE_FINISH = 1,
	PRUNE_FAIL = 2
};


enum prune_ret prune(struct index *idx,
  struct poolalloc *list_alloc,
  int opts, struct index_search_opt *opt);

/* function to construct a query structure from a given string
 * (querystr) of length len.  At most maxwords will be read from the query. */ 
/*
unsigned int index_querybuild(struct index *idx, struct query *query, 
  const char *querystr, unsigned int len, unsigned int maxwords, 
  unsigned int maxtermlen, int impact);
*/
#ifdef __cplusplus
}
#endif

#endif

