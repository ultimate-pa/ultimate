
package jdd.bdd.debug;

import jdd.bdd.*;
import jdd.util.*;

/**
The only function of the class is to verify the integrity of your BDD app by doing extensive
tests on every BDD operation. Not to be used in production (slow!!)
*/
public class DebugBDD extends BDD {


	public DebugBDD(int nodesize) { this(nodesize, Configuration.DEFAULT_BDD_CACHE_SIZE); }
	public DebugBDD(int nodesize, int cache_size) {
		super(nodesize, cache_size);
		// Options.verbose = true;
	}

	public int and(int a, int b) {
		check_node(a, "AND a");
		check_node(b, "AND b");

		return super.and(a,b);
	}
	public int or(int a, int b) {
		check_node(a, "OR a");
		check_node(b, "OR b");

		return super.or(a,b);
	}

	public int xor(int a, int b) {
		check_node(a, "xor a");
		check_node(b, "xor b");

		return super.xor(a,b);
	}

	public int biimp(int a, int b) {
		check_node(a, "biimp a");
		check_node(b, "biimp b");

		return super.biimp(a,b);
	}

	public int imp(int a, int b) {
		check_node(a, "imp a");
		check_node(b, "imp b");

		return super.imp(a,b);
	}
	public int nor(int a, int b) {
		check_node(a, "nor a");
		check_node(b, "nor b");

		return super.nor(a,b);
	}

	public int nand(int a, int b) {
		check_node(a, "nand a");
		check_node(b, "nand b");

		return super.nand(a,b);
	}

	public int ite(int a, int b, int c) {
		check_node(a, "ite a");
		check_node(b, "ite b");
		check_node(c, "ite c");

		return super.ite(a,b,c);
	}


	public int not(int a) {
		check_node(a, "not a");
		return super.not(a);
	}
	public int relProd(int u1, int u2, int c) {
		check_node(u1, "relProd u1");
		check_node(u2, "relProd u2");
		check_node(c , "relProd c");
		return super.relProd(u1,u2,c);
	}
	// ----------------------------------------------------

	public void check_node(int n, String str) {
		Test.check( getRef(n) > 0, "Unrefrenced node in a call, '" + str + "'");
		super.check_node(n,str);
	}
	// ----------------------------------------------------

	protected void post_removal_callbak() {
		super.post_removal_callbak();
		// TODO: add the other caches here:
		quant_cache.check_cache(this);
		replace_cache.check_cache(this);
		not_cache.check_cache(this);
		op_cache.check_cache(this);
	}
	// --------------------------------------------
	/*
	// this one is very slow!!
	public int gc(boolean mark_and_remove, boolean update_cache) {
		int ret = super.gc(mark_and_remove, update_cache);
		if(mark_and_remove) check_all_nodes();
		return ret;
	}
	*/
}
