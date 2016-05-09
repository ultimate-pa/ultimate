package jdd.bdd;


import java.io.*;

import jdd.util.*;

/** Printer class for BDD trees */

public class BDDPrinter {

	private static final int NODE_MASK = 0x7FFFFFFF, NODE_MARK = 0x80000000; // node-marking stuff


	private static NodeTable nt;
	private static PrintStream ps;
	private static NodeName nn;
	private static boolean had_0, had_1;

	private static char [] set_chars = null;
	private static int set_chars_len;

	private static void helpGC() { // make thins easier for the garbage collector
		BDDPrinter.ps = null;
		nn = null;
		nt = null;
	}


	private static final void print_unmark(int bdd) { // cleans up the marking
		if(bdd == 0 || bdd == 1) return;
		if(! nt.isNodeMarked(bdd)) return;
		// if( (v[bdd] & NODE_MARK) == 0)  return;
		nt.unmark_node(bdd);
		// v[bdd] &= NODE_MASK;
		print_unmark( nt.getLow(bdd));
		print_unmark( nt.getHigh(bdd));
	}


	// -----------------------------------------------------
	/** print the part of node-table that describes this BDD */
	public static void print(int bdd, NodeTable nt) {
		BDDPrinter.nn = nn;
		BDDPrinter.nt = nt;
		JDDConsole.out.println("\nBDD " + bdd);
		print_rec(bdd);
		print_unmark(bdd);
		helpGC();
	}
	public static void print_rec(int i) {
		if(i < 2) return;
		// if( (v[i] & NODE_MARK) != 0) return;
		if( nt.isNodeMarked(i)) return;
		JDDConsole.out.println("" + i + "\t" + nt.getVar(i) + "\t" + nt.getLow(i) + "\t" + nt.getHigh(i) );
		nt.mark_node(i);
		print_rec(nt.getLow(i));
		print_rec(nt.getHigh(i));
	}
	// -----------------------------------------------------

	public static void printDot(String filename, int bdd, NodeTable nt, NodeName nn)  {
		try {
			ps = new PrintStream( new FileOutputStream(filename));
			had_0 = had_1 = false;

			ps.println("digraph G {");


   		BDDPrinter.nn = nn;
			BDDPrinter.nt = nt;

			ps.println("\tinit__ [label=\"\", style=invis, height=0, width=0];");
			ps.println("\tinit__ -> "  + bdd + ";");


			printDot_rec(bdd);

			if(had_0)	ps.println("0 [shape=box, label=\"" + nn.zeroShort() + "\", style=filled, shape=box, height=0.3, width=0.3];");
			if(had_1) ps.println("1 [shape=box, label=\"" + nn.oneShort() + "\", style=filled, shape=box, height=0.3, width=0.3];\n");
			ps.println("}\n");
			print_unmark(bdd);
			ps.close();
			Dot.showDot(filename);
			helpGC();
		} catch(IOException exx) {
			JDDConsole.out.println("BDDPrinter.printDOT failed: " + exx);
		}
	}
	private static void printDot_rec(int bdd) {
		// if(bdd == 0 || bdd == 1) return;
		if(bdd == 0)  { had_0 = true; return; }
		if(bdd == 1)  { had_1 = true; return; }

		// if( (v[bdd] & NODE_MARK) != 0) return;
		if( nt.isNodeMarked(bdd)) return;

		int low = nt.getLow(bdd);
		int high = nt.getHigh(bdd);
		int var = nt.getVar(bdd);

		// v[bdd] |= NODE_MARK;
		nt.mark_node(bdd);

		// ps.println("" + bdd + "[label=\"v" + var + "\"];");
		ps.println("" + bdd + "[label=\"" +nn.variable(var) + ":" + bdd+ "\"];");
		ps.println("" + bdd + "-> " + low + " [style=dotted];");
		ps.println("" + bdd + "-> " + high + " [style=filled];");
		printDot_rec(low);
		printDot_rec(high);
	}
	// -----------------------------------------------------------------
	public static void printSet(int bdd, int max, NodeTable nt, NodeName nn)  {

		if( bdd < 2) {
			if(nn != null)  JDDConsole.out.println( (bdd == 0) ? nn.zero() : nn.one() );
			else JDDConsole.out.println( (bdd == 0) ? "FALSE" : "TRUE");
		} else {

			if(BDDPrinter.set_chars == null || BDDPrinter.set_chars.length < max)
				BDDPrinter.set_chars = Allocator.allocateCharArray(max);
			BDDPrinter.set_chars_len = max;
			BDDPrinter.nt = nt;
			BDDPrinter.nn = nn;

			printSet_rec(bdd, 0);
			JDDConsole.out.println();
			helpGC();
		}
	}
	private static void printSet_rec(int bdd, int level) {

		if(level == set_chars_len) {
			if(nn == null) {
				for(int i = 0; i < set_chars_len; i++)
					JDDConsole.out.print(set_chars[i]);
			} else {
				for(int i = 0; i < set_chars_len; i++)
					if(set_chars[i] == '1')
						JDDConsole.out.print(" " + nn.variable(i));
			}

			JDDConsole.out.println();
			return;
		}

		int var = nt.getVar(bdd);
		if(var > level || bdd == 1 ) {
			set_chars[level] = '-';
			printSet_rec(bdd, level+1);
			return;
		}

		int low = nt.getLow(bdd);
		int high = nt.getHigh(bdd);

		if(low != 0) {
			set_chars[level] = '0';
			printSet_rec(low, level+1);
		}

		if(high != 0) {
			set_chars[level] = '1';
			printSet_rec(high, level+1);
		}
	}
}
