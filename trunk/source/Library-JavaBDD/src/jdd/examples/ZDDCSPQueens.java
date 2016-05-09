
package jdd.examples;

import jdd.util.*;
import jdd.zdd.*;

/**
 * <pre>
 * N Queen with Z-BDDs and the CSP procedures.
 * The implementation comes directly from a famous Z-BDD paper [Okuno's ].
 *
 * It will probably go much faster if we can figure out how to make the exclude-operator
 * native [current version makes calls to restrict and diff]...
 * </pre>
 *
 * @see ZDD
 * @see ZDDCSP
 */

public class ZDDCSPQueens extends ZDDCSP implements Queens {
	private int n, sols;
	private int [] x, xv;
	private int get(int i, int j) { return x[ i + j * n]; }
	private int getVar(int i, int j) { return xv[ i + j * n]; }
	private boolean [] solvec;
	private long time, memory;

	public ZDDCSPQueens(int n) {
		super(1+Math.max(1000, (int) (Math.pow(2, n-5))*800), 10000);

		time = System.currentTimeMillis() ;
		this.n = n;
		x = new int[ n * n];
		xv = new int[ n * n];
		boolean[] mark = new boolean[n * n];
		for(int i = 0; i < n * n; i++) {
			xv[i] = createVar();
			x[i] = ref( change(1, xv[i]) );
		}



		// compute G1
		int G1 = 0;
		for(int i = 0; i < n; i++) G1 = unionWith(G1, get(0, i) );

		// compute the rest
		int last_G = G1;
		for(int i = 1; i < n; i++) {
			int F = 0;
			for(int j = 0; j < n; j++)  {
				int bld = build(i, j, last_G, mark);
				F = unionWith( F, bld );
				deref(bld);
			}
			deref( last_G );
			last_G = F;

		}

		solvec = satOne(last_G, null);

		sols = count(last_G);
		deref(last_G);
		time = System.currentTimeMillis() - time;
		if(Options.verbose) showStats();
		memory = getMemoryUsage();
		cleanup();
	}

	// --- [Queens interface ] ---------------------------------------------
	public int getN() { return n; }
	public double numberOfSolutions() { return sols; }
	public long getTime() { return time; }
	public long getMemory() { return memory; }
	public boolean [] getOneSolution() { return solvec; }

	// --- [ internal stuff ] --------------------------------------------------
	private boolean valid(int a, int b) { return (a >= 0 && a < n) && (b >= 0 && b < n); }

	private int build(int i, int j, int G, boolean []mark) {
		Array.set(mark, false);

		for(int k = 0; k < i; k++)  mark[ k + n * j] = true;
		for(int k = 1; k <= i; k++)  {
			int a = j - k, b = i - k;
			if(valid(b, a)) mark[b + n * a] = true;
			a = j + k;
			if(valid(b, a)) mark[b + n * a] = true;
		}


		int C = 0;
		for(int k = 0; k < n * n; k++) {
			if(mark[k]) {
				int a = k / n, b = k % n;
				C = unionWith(C, get(b, a) );
			}
		}

		int tmp = ref( exclude(G,C) );
		deref(C);
		int ret = ref( mul( tmp, get(i,j)) );
		deref(tmp);
		return ret;
	}

	// -------------------------------------------------------------
	private int unionWith(int a, int b) {
		int tmp = ref( union(a,b) );
		deref(a);
		return tmp;
	}

	public static void main(String [] args) {
		if(args.length == 1) {
			ZDDCSPQueens q = new ZDDCSPQueens( Integer.parseInt( args[0] ) );
			JDDConsole.out.println("There are " + q.numberOfSolutions() + " solutions (time: " + q.getTime() + ")");
		}
	}

	/** testbench. do not call */
	public static void internal_test() {
		Test.start("ZDDCSPQueens");
		int [] correct = { 1, 0,0,2, 10, 4, 40,  92 ,  352, 724, 2680 /* , 14200  */ };
		for(int i = 0; i < correct.length; i++) {
			ZDDCSPQueens q = new ZDDCSPQueens( i + 1 );
			// System.out.println("Q"+ (i + 1) + " --> " + q.numberOfSolutions());
			Test.check(q.numberOfSolutions() == correct[i], "correct solutions for " + (i + 1) + " queens");
		}
		Test.end();
	}
}
