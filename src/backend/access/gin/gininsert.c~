/*-------------------------------------------------------------------------
 *
 * gininsert.c
 *	  insert routines for the postgres inverted index access method.
 *
 *
 * Portions Copyright (c) 1996-2014, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *			src/backend/access/gin/gininsert.c
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/gin_private.h"
#include "access/xloginsert.h"
#include "catalog/index.h"
#include "miscadmin.h"
#include "storage/bufmgr.h"
#include "storage/smgr.h"
#include "storage/indexfsm.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "postmaster/bgworker.h"
#include "storage/ipc.h"
#include "storage/latch.h"
#include "storage/proc.h"
#include "fmgr.h"
#include "storage/shm_mq.h"
#include "storage/shm_toc.h"
#include "storage/spin.h"
#include "storage/dsm.h"
#include "storage/procsignal.h"



/* Identifier for shared memory segments used by this extension. */
#define PG_TEST_SHM_MQ_MAGIC 0x79fb2447
#define QUEUE_SIZE 64
#define NWORKERS 1


typedef struct
{
	int			nworkers;
	BackgroundWorkerHandle *handle[FLEXIBLE_ARRAY_MEMBER];
} worker_state;

typedef struct
{
	slock_t     mutex;
	int         workers_total;
	int         workers_attached;
	int         workers_ready;
} test_shm_mq_header;

typedef struct
{
	GinState	ginstate;
	double		indtuples;
	GinStatsData buildStats;
	MemoryContext tmpCtx;
	MemoryContext funcCtx;
	BuildAccumulator accum;
	
} GinBuildState;

static void setup_dynamic_shared_memory(int64 queue_size, int nworkers,
							dsm_segment **segp,
							test_shm_mq_header **hdrp,
							shm_mq **outp, shm_mq **inp);
static worker_state *setup_background_workers(int nworkers,
						 dsm_segment *seg);
static void cleanup_background_workers(dsm_segment *seg, Datum arg);
static void wait_for_workers_to_become_ready(worker_state *wstate,
								 volatile test_shm_mq_header *hdr);
static bool check_worker_status(worker_state *wstate);




/*
 * Adds array of item pointers to tuple's posting list, or
 * creates posting tree and tuple pointing to tree in case
 * of not enough space.  Max size of tuple is defined in
 * GinFormTuple().  Returns a new, modified index tuple.
 * items[] must be in sorted order with no duplicates.
 */
static IndexTuple
addItemPointersToLeafTuple(GinState *ginstate,
						   IndexTuple old,
						   ItemPointerData *items, uint32 nitem,
						   GinStatsData *buildStats)
{
	OffsetNumber attnum;
	Datum		key;
	GinNullCategory category;
	IndexTuple	res;
	ItemPointerData *newItems,
			   *oldItems;
	int			oldNPosting,
				newNPosting;
	GinPostingList *compressedList;

	Assert(!GinIsPostingTree(old));

	attnum = gintuple_get_attrnum(ginstate, old);
	key = gintuple_get_key(ginstate, old, &category);

	/* merge the old and new posting lists */
	oldItems = ginReadTuple(ginstate, attnum, old, &oldNPosting);

	newItems = ginMergeItemPointers(items, nitem,
									oldItems, oldNPosting,
									&newNPosting);

	/* Compress the posting list, and try to a build tuple with room for it */
	res = NULL;
	compressedList = ginCompressPostingList(newItems, newNPosting, GinMaxItemSize,
											NULL);
	pfree(newItems);
	if (compressedList)
	{
		res = GinFormTuple(ginstate, attnum, key, category,
						   (char *) compressedList,
						   SizeOfGinPostingList(compressedList),
						   newNPosting,
						   false);
		pfree(compressedList);
	}
	if (!res)
	{
		/* posting list would be too big, convert to posting tree */
		BlockNumber postingRoot;

		/*
		 * Initialize posting tree with the old tuple's posting list.  It's
		 * surely small enough to fit on one posting-tree page, and should
		 * already be in order with no duplicates.
		 */
		postingRoot = createPostingTree(ginstate->index,
										oldItems,
										oldNPosting,
										buildStats);

		/* Now insert the TIDs-to-be-added into the posting tree */
		ginInsertItemPointers(ginstate->index, postingRoot,
							  items, nitem,
							  buildStats);

		/* And build a new posting-tree-only result tuple */
		res = GinFormTuple(ginstate, attnum, key, category, NULL, 0, 0, true);
		GinSetPostingTree(res, postingRoot);
	}
	pfree(oldItems);

	return res;
}

/*
 * Build a fresh leaf tuple, either posting-list or posting-tree format
 * depending on whether the given items list will fit.
 * items[] must be in sorted order with no duplicates.
 *
 * This is basically the same logic as in addItemPointersToLeafTuple,
 * but working from slightly different input.
 */
static IndexTuple
buildFreshLeafTuple(GinState *ginstate,
					OffsetNumber attnum, Datum key, GinNullCategory category,
					ItemPointerData *items, uint32 nitem,
					GinStatsData *buildStats)
{
	IndexTuple	res = NULL;
	GinPostingList *compressedList;

	/* try to build a posting list tuple with all the items */
	compressedList = ginCompressPostingList(items, nitem, GinMaxItemSize, NULL);
	if (compressedList)
	{
		res = GinFormTuple(ginstate, attnum, key, category,
						   (char *) compressedList,
						   SizeOfGinPostingList(compressedList),
						   nitem, false);
		pfree(compressedList);
	}
	if (!res)
	{
		/* posting list would be too big, build posting tree */
		BlockNumber postingRoot;

		/*
		 * Build posting-tree-only result tuple.  We do this first so as to
		 * fail quickly if the key is too big.
		 */
		res = GinFormTuple(ginstate, attnum, key, category, NULL, 0, 0, true);

		/*
		 * Initialize a new posting tree with the TIDs.
		 */
		postingRoot = createPostingTree(ginstate->index, items, nitem,
										buildStats);

		/* And save the root link in the result tuple */
		GinSetPostingTree(res, postingRoot);
	}

	return res;
}

/*
 * Insert one or more heap TIDs associated with the given key value.
 * This will either add a single key entry, or enlarge a pre-existing entry.
 *
 * During an index build, buildStats is non-null and the counters
 * it contains should be incremented as needed.
 */
void
ginEntryInsert(GinState *ginstate,
			   OffsetNumber attnum, Datum key, GinNullCategory category,
			   ItemPointerData *items, uint32 nitem,
			   GinStatsData *buildStats)
{
	GinBtreeData btree;
	GinBtreeEntryInsertData insertdata;
	GinBtreeStack *stack;
	IndexTuple	itup;
	Page		page;

	insertdata.isDelete = FALSE;

	/* During index build, count the to-be-inserted entry */
	if (buildStats)
		buildStats->nEntries++;

	ginPrepareEntryScan(&btree, attnum, key, category, ginstate);

	stack = ginFindLeafPage(&btree, false);
	page = BufferGetPage(stack->buffer);

	if (btree.findItem(&btree, stack))
	{
		/* found pre-existing entry */
		itup = (IndexTuple) PageGetItem(page, PageGetItemId(page, stack->off));

		if (GinIsPostingTree(itup))
		{
			/* add entries to existing posting tree */
			BlockNumber rootPostingTree = GinGetPostingTree(itup);

			/* release all stack */
			LockBuffer(stack->buffer, GIN_UNLOCK);
			freeGinBtreeStack(stack);

			/* insert into posting tree */
			ginInsertItemPointers(ginstate->index, rootPostingTree,
								  items, nitem,
								  buildStats);
			return;
		}

		/* modify an existing leaf entry */
		itup = addItemPointersToLeafTuple(ginstate, itup,
										  items, nitem, buildStats);

		insertdata.isDelete = TRUE;
	}
	else
	{
		/* no match, so construct a new leaf entry */
		itup = buildFreshLeafTuple(ginstate, attnum, key, category,
								   items, nitem, buildStats);
	}

	/* Insert the new or modified leaf tuple */
	insertdata.entry = itup;
	ginInsertValue(&btree, stack, &insertdata, buildStats);
	pfree(itup);
}

/*
 * Extract index entries for a single indexable item, and add them to the
 * BuildAccumulator's state.
 *
 * This function is used only during initial index creation.
 */
static void
ginHeapTupleBulkInsert(GinBuildState *buildstate, OffsetNumber attnum,
					   Datum value, bool isNull,
					   ItemPointer heapptr)
{
	Datum	   *entries;
	GinNullCategory *categories;
	int32		nentries;
	MemoryContext oldCtx;

	oldCtx = MemoryContextSwitchTo(buildstate->funcCtx);
	entries = ginExtractEntries(buildstate->accum.ginstate, attnum,
								value, isNull,
								&nentries, &categories);
	MemoryContextSwitchTo(oldCtx);

	ginInsertBAEntries(&buildstate->accum, heapptr, attnum,
					   entries, categories, nentries);

	buildstate->indtuples += nentries;

	MemoryContextReset(buildstate->funcCtx);
}

static void
ginBuildCallback(Relation index, HeapTuple htup, Datum *values,
				 bool *isnull, bool tupleIsAlive, void *state)
{
	GinBuildState *buildstate = (GinBuildState *) state;
	MemoryContext oldCtx;
	int i;
	int j;
	Datum *entries;
	GinNullCategory *categories;
	int32 nentries;
	oldCtx = MemoryContextSwitchTo(buildstate->tmpCtx);


	for (i = 0; i < buildstate->ginstate.origTupdesc->natts; i++){
		entries = ginExtractEntries(buildstate->accum.ginstate, (OffsetNumber) (i + 1),
						values[i], isnull[i], &nentries, &categories);

		//DatumGetPointer VARSIZE_ANY hash_any
		//ginstate tupdesc *attrs attbyval if(attbyval) hash(Datum)
		//цикл получить Pointer, найти хэш от него
		//+for

		elog(NOTICE, "nentries = %d", nentries);
	}

	MemoryContextSwitchTo(oldCtx);

}

static void
dowork(Datum main_arg)
{
	elog(LOG, "DOWORK %d!", DatumGetInt32(main_arg));
}

static void
setup_dynamic_shared_memory(int64 queue_size, int nworkers,
							dsm_segment **segp, test_shm_mq_header **hdrp,
							shm_mq **outp, shm_mq **inp)
{
	shm_toc_estimator e;
	int			i;
	Size		segsize;
	dsm_segment *seg;
	shm_toc    *toc;
	test_shm_mq_header *hdr;

	/* Ensure a valid queue size. */
	if (queue_size < 0 || ((uint64) queue_size) < shm_mq_minimum_size)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("queue size must be at least %zu bytes",
						shm_mq_minimum_size)));
	if (queue_size != ((Size) queue_size))
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("queue size overflows size_t")));

	/*
	 * Estimate how much shared memory we need.
	 *
	 * Because the TOC machinery may choose to insert padding of oddly-sized
	 * requests, we must estimate each chunk separately.
	 *
	 * We need one key to register the location of the header, and we need
	 * nworkers + 1 keys to track the locations of the message queues.
	 */
	shm_toc_initialize_estimator(&e);
	for (i = 0; i <= nworkers; ++i)
		shm_toc_estimate_chunk(&e, (Size) queue_size);
	shm_toc_estimate_keys(&e, 2 + nworkers);
	segsize = shm_toc_estimate(&e);

	/* Create the shared memory segment and establish a table of contents. */
	seg = dsm_create(shm_toc_estimate(&e));
	toc = shm_toc_create(PG_TEST_SHM_MQ_MAGIC, dsm_segment_address(seg),
						 segsize);

	/* Set up the header region. */
	hdr = shm_toc_allocate(toc, sizeof(test_shm_mq_header));
	SpinLockInit(&hdr->mutex);
	hdr->workers_total = nworkers;
	hdr->workers_attached = 0;
	hdr->workers_ready = 0;
	shm_toc_insert(toc, 0, hdr);

	/* Set up one message queue per worker, plus one. */
	for (i = 0; i <= nworkers; ++i)
	{
		shm_mq	   *mq;

		mq = shm_mq_create(shm_toc_allocate(toc, (Size) queue_size),
						   (Size) queue_size);
		shm_toc_insert(toc, i + 1, mq);

		if (i == 0)
		{
			/* We send messages to the first queue. */
			shm_mq_set_sender(mq, MyProc);
			*outp = mq;
		}
		if (i == nworkers)
		{
			/* We receive messages from the last queue. */
			shm_mq_set_receiver(mq, MyProc);
			*inp = mq;
		}
	}

	/* Return results to caller. */
	*segp = seg;
	*hdrp = hdr;
}

void
test_shm_mq_setup(int64 queue_size, int32 nworkers, dsm_segment **segp,
				  shm_mq_handle **output, shm_mq_handle **input)
{
	dsm_segment *seg;
	test_shm_mq_header *hdr;
	shm_mq	   *outq = NULL;	/* placate compiler */
	shm_mq	   *inq = NULL;		/* placate compiler */
	worker_state *wstate;

	/* Set up a dynamic shared memory segment. */
	setup_dynamic_shared_memory(queue_size, nworkers, &seg, &hdr, &outq, &inq);
	*segp = seg;

	/* Register background workers. */
	wstate = setup_background_workers(nworkers, seg);

	/* Attach the queues. */
	*output = shm_mq_attach(outq, seg, wstate->handle[0]);


	/* Wait for workers to become ready. */
	wait_for_workers_to_become_ready(wstate, hdr);

	/*
	 * Once we reach this point, all workers are ready.  We no longer need to
	 * kill them if we die; they'll die on their own as the message queues
	 * shut down.
	 */
	cancel_on_dsm_detach(seg, cleanup_background_workers,
						 PointerGetDatum(wstate));
	pfree(wstate);
}

/*
 * Register background workers.
 */
static worker_state *
setup_background_workers(int nworkers, dsm_segment *seg)
{
	MemoryContext oldcontext;
	BackgroundWorker worker;
	worker_state *wstate;
	int			i;

	/*
	 * We need the worker_state object and the background worker handles to
	 * which it points to be allocated in CurTransactionContext rather than
	 * ExprContext; otherwise, they'll be destroyed before the on_dsm_detach
	 * hooks run.
	 */
	oldcontext = MemoryContextSwitchTo(CurTransactionContext);

	/* Create worker state object. */
	wstate = MemoryContextAlloc(TopTransactionContext,
								offsetof(worker_state, handle) +
								sizeof(BackgroundWorkerHandle *) * nworkers);
	wstate->nworkers = 0;

	/*
	 * Arrange to kill all the workers if we abort before all workers are
	 * finished hooking themselves up to the dynamic shared memory segment.
	 *
	 * If we die after all the workers have finished hooking themselves up to
	 * the dynamic shared memory segment, we'll mark the two queues to which
	 * we're directly connected as detached, and the worker(s) connected to
	 * those queues will exit, marking any other queues to which they are
	 * connected as detached.  This will cause any as-yet-unaware workers
	 * connected to those queues to exit in their turn, and so on, until
	 * everybody exits.
	 *
	 * But suppose the workers which are supposed to connect to the queues to
	 * which we're directly attached exit due to some error before they
	 * actually attach the queues.  The remaining workers will have no way of
	 * knowing this.  From their perspective, they're still waiting for those
	 * workers to start, when in fact they've already died.
	 */
	on_dsm_detach(seg, cleanup_background_workers,
				  PointerGetDatum(wstate));

	/* Configure a worker. */
	worker.bgw_flags = BGWORKER_SHMEM_ACCESS;
	worker.bgw_start_time = BgWorkerStart_ConsistentState;
	worker.bgw_restart_time = BGW_NEVER_RESTART;
	worker.bgw_main = dowork;
	snprintf(worker.bgw_name, BGW_MAXLEN, "GinWorker");
	worker.bgw_main_arg = UInt32GetDatum(dsm_segment_handle(seg));
	/* set bgw_notify_pid, so we can detect if the worker stops */
	worker.bgw_notify_pid = MyProcPid;

	/* Register the workers. */
	for (i = 0; i < nworkers; ++i)
	{
		if (!RegisterDynamicBackgroundWorker(&worker, &wstate->handle[i]))
			ereport(ERROR,
					(errcode(ERRCODE_INSUFFICIENT_RESOURCES),
					 errmsg("could not register background process"),
				 errhint("You may need to increase max_worker_processes.")));
		++wstate->nworkers;
	}

	/* All done. */
	MemoryContextSwitchTo(oldcontext);
	return wstate;
}

static void
cleanup_background_workers(dsm_segment *seg, Datum arg)
{
	worker_state *wstate = (worker_state *) DatumGetPointer(arg);

	while (wstate->nworkers > 0)
	{
		--wstate->nworkers;
		TerminateBackgroundWorker(wstate->handle[wstate->nworkers]);
	}
}

static void
wait_for_workers_to_become_ready(worker_state *wstate,
								 volatile test_shm_mq_header *hdr)
{
	bool		save_set_latch_on_sigusr1;
	bool		result = false;

	save_set_latch_on_sigusr1 = set_latch_on_sigusr1;
	set_latch_on_sigusr1 = true;

	PG_TRY();
	{
		for (;;)
		{
			int			workers_ready;

			/* If all the workers are ready, we have succeeded. */
			SpinLockAcquire(&hdr->mutex);
			workers_ready = hdr->workers_ready;
			SpinLockRelease(&hdr->mutex);
			if (workers_ready >= wstate->nworkers)
			{
				result = true;
				break;
			}

			/* If any workers (or the postmaster) have died, we have failed. */
			if (!check_worker_status(wstate))
			{
				result = false;
				break;
			}

			/* Wait to be signalled. */
			WaitLatch(&MyProc->procLatch, WL_LATCH_SET, 0);

			/* An interrupt may have occurred while we were waiting. */
			CHECK_FOR_INTERRUPTS();

			/* Reset the latch so we don't spin. */
			ResetLatch(&MyProc->procLatch);
		}
	}
	PG_CATCH();
	{
		set_latch_on_sigusr1 = save_set_latch_on_sigusr1;
		PG_RE_THROW();
	}
	PG_END_TRY();

	if (!result)
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_RESOURCES),
				 errmsg("one or more background workers failed to start")));
}

static bool
check_worker_status(worker_state *wstate)
{
	int			n;

	/* If any workers (or the postmaster) have died, we have failed. */
	for (n = 0; n < wstate->nworkers; ++n)
	{
		BgwHandleStatus status;
		pid_t		pid;

		status = GetBackgroundWorkerPid(wstate->handle[n], &pid);
		if (status == BGWH_STOPPED || status == BGWH_POSTMASTER_DIED)
			return false;
	}

	/* Otherwise, things still look OK. */
	return true;
}

Datum
ginbuild(PG_FUNCTION_ARGS)
{	
	int64		queue_size = QUEUE_SIZE;
	text	   *message = PG_GETARG_TEXT_PP(1);
	char	   *message_contents = VARDATA_ANY(message);
	int			message_size = VARSIZE_ANY_EXHDR(message);
	int32		loop_count = PG_GETARG_INT32(2);
	int32		nworkers = NWORKERS;
	dsm_segment *seg;
	shm_mq_handle *outqh;
	shm_mq_handle *inqh;
	shm_mq_result res;
	Size		len;
	void	   *data;

	/* Set up dynamic shared memory segment and background workers. */
	test_shm_mq_setup(queue_size, nworkers, &seg, &outqh, &inqh);

	Relation	heap = (Relation) PG_GETARG_POINTER(0);
	Relation	index = (Relation) PG_GETARG_POINTER(1);
	IndexInfo  *indexInfo = (IndexInfo *) PG_GETARG_POINTER(2);
	IndexBuildResult *result;
	double		reltuples;
	GinBuildState buildstate;
	Buffer		RootBuffer,
				MetaBuffer;
	ItemPointerData *list;
	Datum		key;
	GinNullCategory category;
	uint32		nlist;
	MemoryContext oldCtx;
	OffsetNumber attnum;

	if (RelationGetNumberOfBlocks(index) != 0)
		elog(ERROR, "index \"%s\" already contains data",
			 RelationGetRelationName(index));

	initGinState(&buildstate.ginstate, index);
	buildstate.indtuples = 0;
	memset(&buildstate.buildStats, 0, sizeof(GinStatsData));

	/* initialize the meta page */
	MetaBuffer = GinNewBuffer(index);

	/* initialize the root page */
	RootBuffer = GinNewBuffer(index);

	START_CRIT_SECTION();
	GinInitMetabuffer(MetaBuffer);
	MarkBufferDirty(MetaBuffer);
	GinInitBuffer(RootBuffer, GIN_LEAF);
	MarkBufferDirty(RootBuffer);

	if (RelationNeedsWAL(index))
	{
		XLogRecPtr	recptr;
		Page		page;

		XLogBeginInsert();
		XLogRegisterBuffer(0, MetaBuffer, REGBUF_WILL_INIT);
		XLogRegisterBuffer(1, RootBuffer, REGBUF_WILL_INIT);

		recptr = XLogInsert(RM_GIN_ID, XLOG_GIN_CREATE_INDEX);

		page = BufferGetPage(RootBuffer);
		PageSetLSN(page, recptr);

		page = BufferGetPage(MetaBuffer);
		PageSetLSN(page, recptr);
	}

	UnlockReleaseBuffer(MetaBuffer);
	UnlockReleaseBuffer(RootBuffer);
	END_CRIT_SECTION();

	/* count the root as first entry page */
	buildstate.buildStats.nEntryPages++;

	/*
	 * create a temporary memory context that is reset once for each tuple
	 * inserted into the index
	 */
	buildstate.tmpCtx = AllocSetContextCreate(CurrentMemoryContext,
											  "Gin build temporary context",
											  ALLOCSET_DEFAULT_MINSIZE,
											  ALLOCSET_DEFAULT_INITSIZE,
											  ALLOCSET_DEFAULT_MAXSIZE);

	buildstate.funcCtx = AllocSetContextCreate(buildstate.tmpCtx,
					 "Gin build temporary context for user-defined function",
											   ALLOCSET_DEFAULT_MINSIZE,
											   ALLOCSET_DEFAULT_INITSIZE,
											   ALLOCSET_DEFAULT_MAXSIZE);

	buildstate.accum.ginstate = &buildstate.ginstate;
	ginInitBA(&buildstate.accum);

	/*
	 * Do the heap scan.  We disallow sync scan here because dataPlaceToPage
	 * prefers to receive tuples in TID order.
	 */
	reltuples = IndexBuildHeapScan(heap, index, indexInfo, false,
								   ginBuildCallback, (void *) &buildstate);

	/* dump remaining entries to the index */
	oldCtx = MemoryContextSwitchTo(buildstate.tmpCtx);
	ginBeginBAScan(&buildstate.accum);
	while ((list = ginGetBAEntry(&buildstate.accum,
								 &attnum, &key, &category, &nlist)) != NULL)
	{
		/* there could be many entries, so be willing to abort here */
		CHECK_FOR_INTERRUPTS();
		ginEntryInsert(&buildstate.ginstate, attnum, key, category,
					   list, nlist, &buildstate.buildStats);
	}
	MemoryContextSwitchTo(oldCtx);

	MemoryContextDelete(buildstate.tmpCtx);

	/*
	 * Update metapage stats
	 */
	buildstate.buildStats.nTotalPages = RelationGetNumberOfBlocks(index);
	ginUpdateStats(index, &buildstate.buildStats);

	/*
	 * Return statistics
	 */
	result = (IndexBuildResult *) palloc(sizeof(IndexBuildResult));

	result->heap_tuples = reltuples;
	result->index_tuples = buildstate.indtuples;

	PG_RETURN_POINTER(result);
}

/*
 *	ginbuildempty() -- build an empty gin index in the initialization fork
 */
Datum
ginbuildempty(PG_FUNCTION_ARGS)
{
	Relation	index = (Relation) PG_GETARG_POINTER(0);
	Buffer		RootBuffer,
				MetaBuffer;

	/* An empty GIN index has two pages. */
	MetaBuffer =
		ReadBufferExtended(index, INIT_FORKNUM, P_NEW, RBM_NORMAL, NULL);
	LockBuffer(MetaBuffer, BUFFER_LOCK_EXCLUSIVE);
	RootBuffer =
		ReadBufferExtended(index, INIT_FORKNUM, P_NEW, RBM_NORMAL, NULL);
	LockBuffer(RootBuffer, BUFFER_LOCK_EXCLUSIVE);

	/* Initialize and xlog metabuffer and root buffer. */
	START_CRIT_SECTION();
	GinInitMetabuffer(MetaBuffer);
	MarkBufferDirty(MetaBuffer);
	log_newpage_buffer(MetaBuffer, false);
	GinInitBuffer(RootBuffer, GIN_LEAF);
	MarkBufferDirty(RootBuffer);
	log_newpage_buffer(RootBuffer, false);
	END_CRIT_SECTION();

	/* Unlock and release the buffers. */
	UnlockReleaseBuffer(MetaBuffer);
	UnlockReleaseBuffer(RootBuffer);

	PG_RETURN_VOID();
}

/*
 * Insert index entries for a single indexable item during "normal"
 * (non-fast-update) insertion
 */
static void
ginHeapTupleInsert(GinState *ginstate, OffsetNumber attnum,
				   Datum value, bool isNull,
				   ItemPointer item)
{
	Datum	   *entries;
	GinNullCategory *categories;
	int32		i,
				nentries;

	entries = ginExtractEntries(ginstate, attnum, value, isNull,
								&nentries, &categories);

	for (i = 0; i < nentries; i++)
		ginEntryInsert(ginstate, attnum, entries[i], categories[i],
					   item, 1, NULL);
}

Datum
gininsert(PG_FUNCTION_ARGS)
{
	Relation	index = (Relation) PG_GETARG_POINTER(0);
	Datum	   *values = (Datum *) PG_GETARG_POINTER(1);
	bool	   *isnull = (bool *) PG_GETARG_POINTER(2);
	ItemPointer ht_ctid = (ItemPointer) PG_GETARG_POINTER(3);

#ifdef NOT_USED
	Relation	heapRel = (Relation) PG_GETARG_POINTER(4);
	IndexUniqueCheck checkUnique = (IndexUniqueCheck) PG_GETARG_INT32(5);
#endif
	GinState	ginstate;
	MemoryContext oldCtx;
	MemoryContext insertCtx;
	int			i;

	insertCtx = AllocSetContextCreate(CurrentMemoryContext,
									  "Gin insert temporary context",
									  ALLOCSET_DEFAULT_MINSIZE,
									  ALLOCSET_DEFAULT_INITSIZE,
									  ALLOCSET_DEFAULT_MAXSIZE);

	oldCtx = MemoryContextSwitchTo(insertCtx);

	initGinState(&ginstate, index);

	if (GinGetUseFastUpdate(index))
	{
		GinTupleCollector collector;

		memset(&collector, 0, sizeof(GinTupleCollector));

		for (i = 0; i < ginstate.origTupdesc->natts; i++)
			ginHeapTupleFastCollect(&ginstate, &collector,
									(OffsetNumber) (i + 1),
									values[i], isnull[i],
									ht_ctid);

		ginHeapTupleFastInsert(&ginstate, &collector);
	}
	else
	{
		for (i = 0; i < ginstate.origTupdesc->natts; i++)
			ginHeapTupleInsert(&ginstate, (OffsetNumber) (i + 1),
							   values[i], isnull[i],
							   ht_ctid);
	}

	MemoryContextSwitchTo(oldCtx);
	MemoryContextDelete(insertCtx);

	PG_RETURN_BOOL(false);
}
