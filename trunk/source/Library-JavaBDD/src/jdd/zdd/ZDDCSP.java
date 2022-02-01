
package jdd.zdd;


import jdd.bdd.OptimizedCache;
import jdd.util.Configuration;
import jdd.util.Test;

/**
 * ZDD operations for CSP problems.
 * based on "On the properties of combination set operations", by Okuno, Minato and Isozaki.
 *
 * I am also thankfull to Paolo Bonzini who suggested 
 * replaceing the slow Exclude() with noSubset() :)
 */
public class ZDDCSP  extends ZDD2  {
	protected static final int  CACHE_RESTRICT = 0, CACHE_NOSUPSET = 1;

	protected OptimizedCache csp_cache;
    
	public ZDDCSP(int nodesize, int cachesize) {
		super(nodesize, cachesize);
		csp_cache = new OptimizedCache("csp", cachesize / Configuration.zddCSPCacheDiv , 3, 2);
	}
    

	// ---------------------------------------------------------------
	@Override
	public void cleanup() {
		super.cleanup();
		csp_cache = null;
	}
	// ---------------------------------------------------------------


	@Override
	protected void post_removal_callbak() {
		super.post_removal_callbak();
		csp_cache.free_or_grow(this);
	}



	public final int restrict(int F, int C) {
		if(F == 0 || C == 0) {
			return 0;
		}
		if(F == C)
		 {
			return F;
			//if(C == 1) return 0; // <=== is this OK ???
		}

		if(csp_cache.lookup(F, C, CACHE_RESTRICT)) {
			return csp_cache.answer;
		}
		final int hash = csp_cache.hash_value;

		int ret = 0;
		final int v = getVar(F);
		if(v < getVar(C)) { // F0 = F, F1 = 0 ==> restrict(F1,Cn) = 0
			final int tmp =  work_stack[work_stack_tos++] = restrict(F,getLow(C));
			ret = mk(getVar(C), tmp, 0);
			work_stack_tos--;
		} else if(v > getVar(C)) { // C0 = C, C1 = 0 => restrict(F1,C1) = 0
			final int tmp  = work_stack[work_stack_tos++] = restrict( getHigh(F), C);
			final int tmp2 = work_stack[work_stack_tos++] = restrict( getLow(F), C);
			ret = mk(v, tmp2, tmp);
			work_stack_tos -= 2;
		} else {
			int tmp1 = work_stack[work_stack_tos++]  = restrict(getHigh(F), getHigh(C));
			int tmp2 = work_stack[work_stack_tos++]  = restrict(getHigh(F), getLow(C));
			tmp1 = union(tmp1, tmp2);
			work_stack_tos-= 2; work_stack[work_stack_tos++] = tmp1;
			tmp2 = work_stack[work_stack_tos++] = restrict(getLow(F),getLow(C));
			ret = mk(v, tmp2, tmp1);
			work_stack_tos -= 2;
		}


		csp_cache.insert(hash, F, C, CACHE_RESTRICT, ret);
		return ret;
	}
	// ---------------------------------------------------------------
    /**
     * slow Exclude conputed using the definition: 
     * Exclude(F,C) = F - Restrict(F,C)
     */
	private final int exclude_slow(int F, int C) {
		int tmp = work_stack[work_stack_tos++] = restrict(F,C);
		tmp = diff(F, tmp);
		work_stack_tos--;
		return tmp;
	}
    
    
	// ---------------------------------------------------------------	 
    /**
     * fast Exclude computed under its other name "noSupset":
	 *
	 * noSupset(F, C) = {f \in F | \lnot \exist c \in C, c \subseteq f }
     * 
     * NOTE THAT THE SAME CODE IS ALSO FOUND IN ZDDGraph.noSupset(F,C)
     * We could have used some OOP tricks to reuse that code here, but
     * I decided not to...
     */

    private final int exclude_fast(int F, int C)  {
		if( emptyIn(C)) {
			return 0;
		}
		return noSupset_rec(F, C);
	}


    private final int noSupset_rec(int F, int C) {
        
		if(F == 0 || C == 1 || F == C) {
			return 0;
		}
        if(F == 1 || C == 0) {
			return F;
		}         
        
		if(csp_cache.lookup(F, C, CACHE_NOSUPSET)) {
			return csp_cache.answer;
		}
		final int hash = csp_cache.hash_value;

		int ret;
		final int fvar = getVar(F);
		final int cvar = getVar(C);

		if (fvar < cvar) {
			ret = noSupset_rec(F, getLow(C));
		} else if (fvar > cvar) {
			final int tmp1 = work_stack[work_stack_tos++] = noSupset_rec(getHigh(F), C);
			final int tmp2 = work_stack[work_stack_tos++] = noSupset_rec(getLow(F) , C);
			ret = mk(fvar, tmp2, tmp1);
			work_stack_tos -= 2;
		} else {            
            int tmp1, tmp2;            
            final int C1 = getHigh(C);
            
            if( emptyIn(C1)) { 
                // special case, because noSupset( getHigh(F), C1) = 0
               tmp1 = work_stack[work_stack_tos++] = 0;
            } else {
                final int F1 = getHigh(F);
                tmp1 = work_stack[work_stack_tos++] = noSupset_rec( F1, getLow(C));
                tmp2 = work_stack[work_stack_tos++] = noSupset_rec( F1, C1);                
                tmp1 = intersect(tmp1, tmp2);
                work_stack_tos -= 2;
                work_stack[work_stack_tos++] = tmp1;
            }                        

			tmp2 = work_stack[work_stack_tos++] = noSupset_rec( getLow(F), getLow(C));
			ret  = mk(fvar, tmp2, tmp1);
			work_stack_tos -= 2;
		}

		csp_cache.insert(hash, F, C, CACHE_NOSUPSET, ret);
		return ret;
    }


    // ---------------------------------------------------------------
    /**
     * Exclude(F,C), defined as "F - Restrict(F,C)"
     */
	public final int exclude(int F, int C) {
		// return exclude_slow(F,C);
        return exclude_fast(F, C);
	}

	// --- [ debug ] ----------------------------------------------

	@Override
	public void showStats() {
		super.showStats();
		csp_cache.showStats();
	}

	@Override
	public long getMemoryUsage() {
		long ret = super.getMemoryUsage();
		if(csp_cache != null) {
			ret += csp_cache.getMemoryUsage();
		}
		return ret;
	}

	/** testbench. do not call */
	public static void internal_test() {

		Test.start("ZDDCSP");

		final ZDDCSP csp = new ZDDCSP(200, 1000);
		final int a = csp.createVar();
		final int b = csp.createVar();
		final int c = csp.createVar();
		final int d = csp.createVar();
		final int e = csp.createVar();
        
        final int p = csp.cubes_union("00011 00111 01110");
        final int q = csp.cubes_union("00110 00111");
        
		// test P * Q
		final int answer_product = csp.cubes_union("00111 01111 01110");
		Test.checkEquality( answer_product, csp.mul(p,q), "P * Q" );
		Test.checkEquality( csp.work_stack_tos, 0, "TOS restored (1)" );




		// test P / Q
		final int answer_division = 0;
		Test.checkEquality( answer_division, csp.div(p,q), "P / Q" );
		Test.checkEquality( csp.work_stack_tos, 0, "TOS restored (2)" );


		// test P % Q
		final int answer_quotient = csp.cubes_union("00011 00111 01110");
		Test.checkEquality( answer_quotient, csp.mod(p,q), "P % Q" );
		Test.checkEquality( csp.work_stack_tos, 0, "TOS restored (3)" );



		// restrict:
		final int answer_restrict_pq = csp.cubes_union("00111 01110");
		final int answer_restrict_qp = csp.cube("00111");
		Test.checkEquality(csp.restrict(p, q), answer_restrict_pq, "Restrict(P,Q)");
		Test.checkEquality(csp.restrict(q, p), answer_restrict_qp, "Restrict(Q,P)");
		Test.checkEquality( csp.work_stack_tos, 0, "TOS restored (4)" );


		// exclude
		final int answer_exclude_pq = csp.cube("00011");
		final int answer_exclude_qp = csp.cube("00110");
		Test.checkEquality(csp.exclude(p, q), answer_exclude_pq, "Exclude(P,Q)");
		Test.checkEquality(csp.exclude(q, p), answer_exclude_qp, "Exclude(Q,P)");
		Test.checkEquality( csp.work_stack_tos, 0, "TOS restored (5)" );

		Test.end();
	}

}

