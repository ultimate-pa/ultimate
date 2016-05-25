
package jdd.zdd;


import jdd.bdd.OptimizedCache;
import jdd.util.Configuration;
import jdd.util.Test;

/**
 * ZDD2 extends ZDD with some additional operations for unate cube set algerba
 * @see ZDD
 */
public class ZDD2  extends ZDD  {

	private static final int CACHE_MUL = 0, CACHE_DIV = 1, CACHE_MOD = 2;
	protected OptimizedCache unate_cache;


	public ZDD2(int nodesize) {
		this(nodesize, Configuration.DEFAULT_ZDD_CACHE_SIZE);
	}

	public ZDD2(int nodesize, int cachesize) {
		super(nodesize, cachesize);
		unate_cache = new OptimizedCache("unate", cachesize / Configuration.zddUnateCacheDiv , 3, 2);
	}



	// ---------------------------------------------------------------
	@Override
	public void cleanup() {
		super.cleanup();
		unate_cache = null;
	}

	// ---------------------------------------------------------------
	@Override
	protected void post_removal_callbak() {
		super.post_removal_callbak();
		unate_cache.free_or_grow(this);
	}


	// ----------------------------------------------------------------------
    public final int mul(int p, int q) {
        
        if(p == 0 || q == 0) {
			return 0;
		}
        if(p == 1) {
			return q;
		}
        if(q == 1) {
			return p;
		}
        
        
        int pvar = getVar(p);
        int qvar = getVar(q);
        
        // maybe we should compare p and q?
        if(pvar > qvar) {
            int tmp = p; p = q; q = tmp;
            tmp = pvar; pvar = qvar; qvar = tmp;
        }
        
        if(unate_cache.lookup(p, q, CACHE_MUL)) {
			return unate_cache.answer;
		}
		final int hash = unate_cache.hash_value;
        
        int tmp1, tmp2, ret;
        if(pvar < qvar) {
            tmp1 =  work_stack[work_stack_tos++] = mul( p, getHigh(q));
            tmp2 =  work_stack[work_stack_tos++] = mul( p, getLow(q));
            ret = mk(qvar, tmp2, tmp1);
            work_stack_tos -= 2;
        } else { // pvar == qvar
            tmp1 = work_stack[work_stack_tos++] = mul( getHigh(p), getHigh(q));
            tmp2 = work_stack[work_stack_tos++] = mul( getHigh(p), getLow(q));
            
            ret = union(tmp1, tmp2);            
            work_stack_tos -= 2;
            work_stack[work_stack_tos++] = ret;
            
            tmp1 = work_stack[work_stack_tos++] = mul(getLow(p), getHigh(q));
            
            tmp1 = union(ret, tmp1);
            work_stack_tos -= 2;
            work_stack[work_stack_tos++] = tmp1;
            
            tmp2 = work_stack[work_stack_tos++] = mul(getLow(p), getLow(q));
            ret  = mk(pvar, tmp2, tmp1);
            work_stack_tos -= 2;
        }
        
        
		unate_cache.insert(hash, p, q, CACHE_MUL, ret);
		return ret;
	}
    /*
	public final int mul_old(int p, int q) {
		if(q == 0 || p == 0) return 0;
		if(q == 1) return p;
		if(getVar(p) < getVar(q)) return mul(q,p);

		if(unate_cache.lookup(p, q, CACHE_MUL)) return unate_cache.answer;
		int hash = unate_cache.hash_value;


		int tmp1 = 0, tmp2 = 0, v = getVar(p);
		int pl = work_stack[work_stack_tos++]  = subset0( p, v);
		int ph = work_stack[work_stack_tos++]  = subset1( p, v);

		if(v == getVar(q)) { // ql = getVar(q), qh = getHigh(q)
			tmp1 = work_stack[work_stack_tos++] = mul(ph, getHigh(q));
			tmp2 = work_stack[work_stack_tos++] = mul(ph, getLow(q));
			tmp1 = union(tmp1, tmp2);		// p1*q1 + p1*q0
			work_stack_tos -= 2; work_stack[work_stack_tos++]  = tmp1;

			tmp2 = work_stack[work_stack_tos++] = mul(pl, getHigh(q));
			tmp1 = union(tmp1, tmp2); // p1*q1 + p1*q0 + p0*q1
			work_stack_tos -=2; work_stack[work_stack_tos++]  = tmp1;
			tmp2 = work_stack[work_stack_tos++] = mul(pl, getLow(q)); // p0*q0
		} else { // ql = q, qh = 0  == >mul(ph,qh) =  0
			tmp1 = work_stack[work_stack_tos++] = mul(ph, q); // p1 * q0
			tmp2 = work_stack[work_stack_tos++] = mul(pl, q); // p0 * q0
		}

		tmp1 = mk(v, tmp2, tmp1); // v(p1*q1 + p1*q0 + p0*q1) + p0*q1
		work_stack_tos -= 2 + 2;

		unate_cache.insert(hash, p, q, CACHE_MUL, tmp1);
		return tmp1;
       }
     */

	// ----------------------------------------------------------------
	/** 
     * if q contains a single literal, this equals subset1(p, getVar(q)) 
     */
    public final int div(int p, int q) {
        if(p < 2) {
			return 0;
		}
        if(p == q) {
			return 1;
		}
        if(q == 1) {
			return p;
		}
        
        final int pvar = getVar(p);
        final int qvar = getVar(q);
        
        if(pvar < qvar) {
			return 0;
		}
        
        
		if(unate_cache.lookup(p, q, CACHE_DIV)) {
			return unate_cache.answer;
		}
		final int hash = unate_cache.hash_value;
        
        int tmp1, tmp2, ret;
        if(pvar > qvar) {
            tmp1 = work_stack[work_stack_tos++] = div(getLow(p), q);
            tmp2 = work_stack[work_stack_tos++] = div(getHigh(p), q);
            ret  = mk(pvar, tmp1, tmp2);
            work_stack_tos -= 2;
        } else {
            ret = div( getHigh(p), getHigh(q));
            
            tmp1 = getLow(q);
            if(tmp1 != 0 && ret != 0) {
                work_stack[work_stack_tos++] = ret; // save it
                tmp1 = work_stack[work_stack_tos++] = div( getLow(p), tmp1);
                ret = intersect(tmp1, ret);
                work_stack_tos -= 2;                
            }
        }
        
        unate_cache.insert(hash, p, q, CACHE_DIV, ret);
		return ret;
    }
/*    
	public final int div_old(int p, int q) {
		if(q == 1) return p;
		if(p < 2) return 0;
		if(p == q) return p;

		if(unate_cache.lookup(p, q, CACHE_DIV)) return unate_cache.answer;
		int hash = unate_cache.hash_value;

		int v = getVar(q);
		int ql = work_stack[work_stack_tos++] = subset0( q, v);
		int qh = work_stack[work_stack_tos++] = subset1( q, v);
		int pl = work_stack[work_stack_tos++] = subset0( p, v);
		int ph = work_stack[work_stack_tos++] = subset1( p, v);

		int tmp = div(ph, qh);
		if(tmp != 0 && ql != 0) {
			work_stack[work_stack_tos++] = tmp;
			int tmp2 = work_stack[work_stack_tos++] = div(pl, ql);
			tmp = intersect(tmp, tmp2);
			work_stack_tos -= 2;
		}
		work_stack_tos  -= 4;

		unate_cache.insert(hash, p, q, CACHE_DIV, tmp);
		return tmp;
   }
 */ 

	/** if q contains a single literal, this equals subset0(p, getVar(q)) */
	public final int mod(int p, int q) { // P % Q = P - Q * (P / Q)


		if(unate_cache.lookup(p, q, CACHE_MOD)) {
			return unate_cache.answer;
		}
		final int hash = unate_cache.hash_value;

		int tmp = work_stack[work_stack_tos++] = div(p, q);
		tmp = work_stack[work_stack_tos++] = mul(q, tmp);
		tmp = diff(p, tmp);
		work_stack_tos -= 2;

		unate_cache.insert(hash, p, q, CACHE_MOD, tmp);
		return tmp;

	}
	// --- [ debug ] ----------------------------------------------

	@Override
	public void showStats() {
		super.showStats();
		unate_cache.showStats();
	}

	/** return the amount of internally allocated memory in bytes */
	@Override
	public long getMemoryUsage() {
		long ret = super.getMemoryUsage();
		if(unate_cache != null) {
			ret += unate_cache.getMemoryUsage();
		}
		return ret;
	}

	// ---------------------------------------

	/** testbench. do not call */
	public static void internal_test() {
		Test.start("ZDD2");
		final ZDD2 zdd =  new ZDD2(1000);
		// Options.verbose = true; // want to see GC:s

		final int a = zdd.createVar();
		final int b = zdd.createVar();
		final int c = zdd.createVar();
		final int d = zdd.createVar();
		final int e = zdd.createVar();
		final int f = zdd.createVar();
		final int g = zdd.createVar();
		final int h = zdd.createVar();

        // MUL:
		// from minatos paper "Calculation of ..." {ab, b, c } * {ab, 1 } = {ab, abc, b, c }
		int tmp1 = zdd.cubes_union("010 100 011");
		int tmp2 = zdd.union( zdd.cube("11"), 1);
		int tmp3 = zdd.mul(tmp1, tmp2);
		int answer = zdd.cubes_union("010 100 011 111");
		Test.checkEquality( tmp3, answer, "P * Q");
		Test.checkEquality( zdd.work_stack_tos, 0, "TOS restored after mul");
        
        
		// simple mul test: prefix
		final int mp = zdd.cubes_union( "011 111 1110");
		int md = zdd.cube("1000");
		int mpd= zdd.mul(mp, md);
		answer = zdd.cubes_union( "1011 1111 1110" );
		Test.checkEquality(mpd, answer, "{ab,abc,bcd}*d = {abd,abcd,bcd}");

		// suffix
		md = zdd.cube("1");
		mpd = zdd.mul(mp, md);
		answer = zdd.cubes_union( "011 111 1111" );
		Test.checkEquality(mpd, answer, "{ab,abc,bcd}*a = {ab,abc,abc}");
        
        // DIV
		// from minatos paper "ZBDDs and their applications" (p162)
		tmp1 = zdd.cubes_union( "111 110 101");
		tmp2 = zdd.cube("110");
		tmp3 = zdd.div(tmp1, tmp2);
		answer = zdd.union( zdd.cube("1"), 1);
		Test.checkEquality( tmp3, answer, "P / Q");
		Test.checkEquality( zdd.work_stack_tos, 0, "TOS restored after div (1)");


		// again, from minatos paper "ZBDDs and their applications" (bottom of p162)
		tmp1 = zdd.cubes_union("1011 10011 1000011 1100 10000100 10100");        
		tmp2 = zdd.cubes_union("011 100");
		tmp3 = zdd.div(tmp1, tmp2);
		answer = zdd.cubes_union("1000 10000");
		Test.checkEquality( tmp3, answer, "P / Q (2)");
		Test.checkEquality( zdd.work_stack_tos, 0, "TOS restored after div (2)");


        
        // DIV & MOD: div/mod by a scalar, comparing with subset0/subset1
        
        // prefix
        tmp1   = zdd.cubes_union("1011 0111 1110");
        tmp2   = zdd.cubes_union("1000");
        answer = zdd.cubes_union("011 110");
        
        tmp3 = zdd.div(tmp1, tmp2);
        Test.checkEquality( tmp3, answer, "div by scalar (prefix)");
        Test.checkEquality( zdd.work_stack_tos, 0, "TOS restored after div (3)");        
        
        Test.checkEquality( answer, zdd.subset1(tmp1, zdd.getVar(tmp2)), "div by scalar (prefix)");
        
        tmp3 = zdd.mod(tmp1, tmp2);
        Test.checkEquality( tmp3, zdd.subset0(tmp1, zdd.getVar(tmp2)), "mod by scalar (prefix)");
        Test.checkEquality( zdd.work_stack_tos, 0, "TOS restored after mod");
        
        
        // suffix
        tmp1   = zdd.cubes_union("1011 0111 1110");
        tmp2   = zdd.cubes_union("0001");
        answer = zdd.cubes_union("1010 0110");
        
        tmp3 = zdd.div(tmp1, tmp2);
        Test.checkEquality( tmp3, answer, "div by scalar (suffix)");
        Test.checkEquality( zdd.work_stack_tos, 0, "TOS restored after div (4)");
        
        Test.checkEquality( answer, zdd.subset1(tmp1, zdd.getVar(tmp2)), "div by scalar (suffix)");
        
        tmp3 = zdd.mod(tmp1, tmp2);
        Test.checkEquality( tmp3, zdd.subset0(tmp1, zdd.getVar(tmp2)), "mod by scalar (suffix)");
        Test.checkEquality( zdd.work_stack_tos, 0, "TOS restored after mod (2)");
        
        
        
        // MUL+DIV+MOD
        // one generic mul/div/mod test
        tmp1   = zdd.cubes_union("0011 0111 1110");
        tmp2   = zdd.cubes_union("0110 0111");
        answer = zdd.cubes_union("0111 1111 1110");
        
        tmp3 = zdd.mul(tmp1, tmp2);
        Test.checkEquality( answer, tmp3, "generic mul");
        Test.checkEquality( zdd.work_stack_tos, 0, "TOS restored after mul (2)");
        
        Test.checkEquality( 0,    zdd.div(tmp1, tmp2), "generic div");
        Test.checkEquality( tmp1, zdd.mod(tmp1, tmp2), "generic mod");
        
        
        
		Test.end();
	}

}

