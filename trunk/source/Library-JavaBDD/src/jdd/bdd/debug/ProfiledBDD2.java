package jdd.bdd.debug;

import java.util.Collection;

import jdd.bdd.BDD;
import jdd.bdd.Permutation;
import jdd.util.Configuration;
import jdd.util.JDDConsole;
import jdd.util.Options;

/**
 * profiling the BDD by counting and timing each operation
 *
 * @see ProfiledBDD
 * @see BDD
 */
public class ProfiledBDD2 extends BDD {

	private long p_and, p_or, p_xor,p_biimp, p_imp, p_not, p_nand, p_nor;
	private long p_replace, p_exists, p_forall, p_relprod;
	private long p_support, p_restrict, p_simplify, p_ite;
	private long p_satcount, p_permutation;



	private long t_and, t_or, t_xor,t_biimp, t_imp, t_not, t_nand, t_nor;
	private long t_replace, t_exists, t_forall, t_relprod;
	private long t_support, t_restrict, t_simplify, t_ite;
	private long t_satcount, t_permutation;

	// private  long p_mk, p_hash;

	public ProfiledBDD2(int nodesize) { this(nodesize, Configuration.DEFAULT_BDD_CACHE_SIZE); }
	public ProfiledBDD2(int nodesize, int cache_size) {
		super(nodesize, cache_size);
		p_and = p_or = p_xor = p_biimp = p_imp = p_not = 0;
		p_support = p_restrict = p_simplify = p_ite = 0;
		p_replace =  p_exists =  p_forall =  p_relprod  = 0;
		p_satcount = p_permutation = 0;

		t_and = t_or = t_xor = t_biimp = t_imp = t_not = 0;
		t_support = t_restrict = t_simplify =  t_ite = 0;
		t_replace =  t_exists =  t_forall =  t_relprod  = 0;
		t_satcount = t_permutation = 0;


		if(Options.profile_cache) {
			new BDDDebugFrame(this);
		}
	}



	// ---------------------------------------------------------------
	// Debugging stuff
	@Override
	public Collection addDebugger(BDDDebuger d) {
		final Collection v = super.addDebugger( d );
		v.add( quant_cache );
		v.add( ite_cache );
		v.add( not_cache );
		v.add( op_cache );
		v.add( replace_cache );
		v.add( sat_cache );
		return v;
	}
	// ---------------------------------------------------------------


	@Override
	public int and(int a, int b) {
		final long t = System.currentTimeMillis();
		p_and++;
		final int ret = super.and(a,b);
		t_and += ( System.currentTimeMillis() - t);
		return ret;
	}
	@Override
	public int or(int a, int b) {
		final long t = System.currentTimeMillis();
		p_or++;
		final int ret = super.or(a,b);
		t_or += ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public int xor(int a, int b) {
		final long t = System.currentTimeMillis();
		p_xor++;
		final int ret = super.xor(a,b);
		t_xor += ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public int biimp(int a, int b) {
		final long t = System.currentTimeMillis();
		p_biimp++;
		final int ret =  super.biimp(a,b);
		t_biimp += ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public int imp(int a, int b) {
		final long t = System.currentTimeMillis();
		p_imp++;
		final int ret = super.imp(a,b);
		t_imp += ( System.currentTimeMillis() - t);
		return ret;
		}

	@Override
	public int nor(int a, int b) {
		final long t = System.currentTimeMillis();
		p_nor++;
		final int ret = super.nor(a,b);
		t_nor += ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public int nand(int a, int b) {
		final long t = System.currentTimeMillis();
		p_nand++;
		final int ret = super.nand(a,b);
		t_nand += ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public int not(int a) {
		final long t = System.currentTimeMillis();
		p_not++;
		final int ret = super.not(a);
		t_not += ( System.currentTimeMillis() - t);
		return ret;
	}


	@Override
	public int replace(int a, Permutation b) {
		final long t = System.currentTimeMillis();
		p_replace++;
		final int ret = super.replace(a,b);
		t_replace += ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public int exists(int a, int b) {
		final long t = System.currentTimeMillis();
		p_exists++;
		final int ret = super.exists(a,b);
		t_exists += ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public int forall(int a, int b) {
		final long t = System.currentTimeMillis();
		p_forall++;
		final int ret = super.forall(a,b);
		t_forall += ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public int relProd(int a, int b, int c) {
		final long t = System.currentTimeMillis();
		p_relprod++;
		final int ret = super.relProd(a,b,c);
		t_relprod += ( System.currentTimeMillis() - t);
		return ret;
	}


	@Override
	public int support(int a) {
		final long t = System.currentTimeMillis();
		p_support++;
		final int ret = super.support(a);
		t_support += ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public int restrict(int a, int b) {
		final long t = System.currentTimeMillis();
		p_restrict++;
		final int ret = super.restrict(a,b);
		t_restrict += ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public int simplify(int a, int b) {
		final long t = System.currentTimeMillis();
		p_simplify++;
		final int ret = super.simplify(a,b);
		t_simplify += ( System.currentTimeMillis() - t);
		return ret;
	}


	@Override
	public int ite(int a, int b, int c ) {
		final long t = System.currentTimeMillis();
		p_ite++;
		final int ret = super.ite(a,b,c);
		t_ite += ( System.currentTimeMillis() - t);
		return ret;
	}


	@Override
	public double satCount(int a) {
		final long t = System.currentTimeMillis();
		p_satcount++;
		final double ret = super.satCount(a);
		t_satcount+= ( System.currentTimeMillis() - t);
		return ret;
	}

	@Override
	public Permutation createPermutation( int [] cube_from, int [] cube_to) {
		final long t = System.currentTimeMillis();
		p_permutation++;
		final Permutation ret = super.createPermutation(cube_from, cube_to);
		t_permutation += ( System.currentTimeMillis() - t);
		return ret;
	}

	public void report(String what, long count, long time) {

		if(count > 0) {
			final StringBuffer sb = new StringBuffer(256);
			sb.append("calls to " + what);
			while(sb.length() < 28) {
				sb.append(' ');
			}
			sb.append(" : "+ count + " times");
			while(sb.length() < 48) {
				sb.append(' ');
			}
			sb.append(" " + time + " [ms]");
			JDDConsole.out.println(sb.toString() );
		}
	}
	@Override
	public void showStats() {
		report("AND", p_and,t_and);
		report("OR", p_or,t_or);

		report("NAND", p_nand,t_nand);
		report("NOR", p_nor,t_nor);

		report("XOR", p_xor,t_xor);
		report("BI-IMP", p_biimp,t_biimp);
		report("IMP", p_imp,t_imp);

		report("NOT", p_not,t_not);
		report("ITE", p_ite,t_ite);



		report("REPLACE", p_replace,t_replace);
		report("EXISTS", p_exists,t_exists);
		report("FORALL", p_forall,t_forall);
		report("REL-PROD", p_relprod,t_relprod);

		report("SUPPORT", p_support,t_support);
		report("RESTRICT", p_restrict,t_restrict);
		report("SIMPLIFY", p_simplify,t_simplify);

		report("SAT-COUNT", p_satcount, t_satcount);

		report("CREATE-PERMUTATION", p_permutation, t_permutation);



		super.showStats();
	}

}
