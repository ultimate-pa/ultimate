// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

// Benchmark: pgdropbuf.c
// Property: istemp => G(A!=1)

#include <stdio.h>
#define AF_INET 1
#define AF_INET6 2
#define AF_UNIX 3
#define __builtin___snprintf_chk(a,b,c,d,e,f) {}
#define __builtin___object_size(a,b) nondet()

int family;
char *hostName;
unsigned short portNumber;
char *unixSocketName;
int MaxListen;
int fd, err;
int maxconn;
int one;
int ret;
char       *service;
int hint;
int                     listen_index;
int                     added;
int addr_ai_family;
int addr;
int MAXADDR;
int ListenSocket_OF_listen_index;
int ret;
char *sock_path;
int addrs;


/* ---------------------------------------------------------------------
 *              DropRelFileNodeBuffers
 *
 *              This is the same as DropRelationBuffers, except that the target
 *              relation is specified by RelFileNode and temp status, and one
 *              may specify the first block to drop.
 *
 *              This is NOT rollback-able.      One legitimate use is to clear the
 *              buffer cache of buffers for a relation that is being deleted
 *              during transaction abort.
 * --------------------------------------------------------------------
 */

int rnode;
int istemp;
int firstDelBlock;
int A; int R;
char *bufHdr;

int bufHdr_tag_blockNum;

int bufHdr_tag_blockNum;
int bufHdr_tag_rnode;
int bufHdr_tag_rnode_spcNode;
int bufHdr_tag_rnode_dbNode;
int bufHdr_tag_rnode_relNode;
int bufHdr_flags;
#define BM_DIRTY 1
#define BM_JUST_DIRTIED 2
#define BM_IO_IN_PROGRESS 3
int bufHdr_cntxDirty;
int bufHdr_tag_rnode_relNode;
int LocalRefCount_i;
int LocalBufferDescriptors_i;
int NLocBuffer;
int i;
int NBuffers;
int bufHdr_refcount;
void StrategyInvalidateBuffer(int bufHdr) {}
void WaitIO(int a) {}
int RelFileNodeEquals(int a, int b) { return nondet(); }


void init() {
  istemp = nondet(); A = R = 0;
  NLocBuffer = nondet();
  NBuffers = nondet();
}




//void DropRelFileNodeBuffers(RelFileNode rnode, bool istemp,   BlockNumber firstDelBlock)
void body() {
        if (istemp==1)
        {
                for (i = 0; i < NLocBuffer; i++)
                {
                        bufHdr = &LocalBufferDescriptors_i;
                        if (RelFileNodeEquals(bufHdr_tag_rnode, rnode) &&
                                bufHdr_tag_blockNum >= firstDelBlock)
                        {
			  if (LocalRefCount_i != 0) ;
                                        /* elog(ERROR, "block %u of %u/%u/%u is still referenced (local %u)", */
                                        /*          bufHdr_tag_blockNum, */
                                        /*          bufHdr_tag_rnode_spcNode, */
                                        /*          bufHdr_tag_rnode_dbNode, */
                                        /*          bufHdr_tag_rnode_relNode, */
                                        /*          LocalRefCount_i); */
                                bufHdr_flags &= ~(BM_DIRTY | BM_JUST_DIRTIED);
                                bufHdr_cntxDirty = 0;
                                bufHdr_tag_rnode_relNode = 1; // InvalidOid;
                        }
                }
                goto my_exit;
        }

        A = 1; A = 0; // LWLockAcquire(BufMgrLock, LW_EXCLUSIVE);

        for (i = 1; i <= NBuffers; i++)
        {
	  bufHdr = nondet(); // &BufferDescriptors[i - 1];
recheck:
                if (RelFileNodeEquals(bufHdr_tag_rnode, rnode) &&
                        bufHdr_tag_blockNum >= firstDelBlock)
                {
                        /*
                         * If there is I/O in progress, better wait till it's done;
                         * don't want to delete the relation out from under someone
                         * who's just trying to flush the buffer!
                         */
                        if (bufHdr_flags & BM_IO_IN_PROGRESS)
                        {
                                WaitIO(bufHdr);

                                /*
                                 * By now, the buffer very possibly belongs to some other
                                 * rel, so check again before proceeding.
                                 */
                                goto recheck;
                        }

                        /*
                         * There should be no pin on the buffer.
                         */
                        if (bufHdr_refcount != 0)
			  ;
                                /* elog(ERROR, "block %u of %u/%u/%u is still referenced (private %d, global %u)", */
                                /*          bufHdr_tag_blockNum, */
                                /*          bufHdr_tag_rnode_spcNode, */
                                /*          bufHdr_tag_rnode_dbNode, */
                                /*          bufHdr_tag_rnode_relNode, */
                                /*          PrivateRefCount[i - 1], bufHdr_refcount); */

                        /* Now we can do what we came for */
                        bufHdr_flags &= ~(BM_DIRTY | BM_JUST_DIRTIED);
                        bufHdr_cntxDirty = 0;

                        /*
                         * And mark the buffer as no longer occupied by this rel.
                         */
                        StrategyInvalidateBuffer(bufHdr);
                }
        }

        R = 1; R = 0; //LWLockRelease(BufMgrLock);
 my_exit:
	while(1) { int yyy;yyy=yyy;}
}

int main() {}
