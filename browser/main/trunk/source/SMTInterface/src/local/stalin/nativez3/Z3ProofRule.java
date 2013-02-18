package local.stalin.nativez3;

import java.io.PrintStream;

import local.stalin.logic.Formula;

public class Z3ProofRule {

//	static {
//		String osname = System.getProperty("os.name");
//		String z3libname = osname.contains("Windows") ? "z3" : "z3-gmp";
//		System.loadLibrary(z3libname);
//		System.loadLibrary("nativez3");
//	}

	public final static String[] RULENAMES = {
		"true",
		"asserted",
		"goal",
		"mp",
		"reflexivity",
		"symmetry",
		"transitivity",
		"transitivity*",
		"monotonicity",
		"quantintro",
		"distributivity",
		"and-elim",
		"not-or-elim",
		"rewrite",
		"rewrite*",
		"pullquant",
		"pullquant*",
		"pushquant",
		"elim-unused-vars",
		"def",
		"quantinst",
		"hypothesis",
		"lemma",
		"unit-resolution",
		"iff-true",
		"iff-false",
		"commutativity",
		"def-axiom",
		"def-intro",
		"apply-def",
		"iff~",
		"nnf-pos",
		"nnf-neg",
		"nnf*",
		"cnf*",
		"skolemize",
		"mp~",
		"th-lemma"
	};
	
	// Z3 proof rule number
	private int mrulenum;
	private Z3ProofRule[] mantecedents;
	private Formula mres;
	//private String mres;
	// Number of hypothesis or assumption
	private int massnum;
	
	private Z3ProofRule(int rulenum,int numantecedents) {
		mrulenum = rulenum;
		mantecedents = new Z3ProofRule[numantecedents];
	}
	
	@SuppressWarnings("unused")
	private void addProofRule(Z3ProofRule pr,int pos) {
		assert(pos < mantecedents.length);
		mantecedents[pos] = pr;
	}
	
//	@SuppressWarnings("unused")
//	private void setResult(String res) {
//		mres = res;
//	}
/*	private void setResult(Formula res) {
		mres = res;
	}*/
	
	@SuppressWarnings("unused")
	private void setAssNum(int assnum) {
		massnum = assnum;
	}
	
	public Z3ProofRule[] getAntecedents() {
		return mantecedents;
	}
	
	public Formula getResult() {
		return mres;
	}
//	public String getResult() {
//		return mres;
//	}

	public int getRuleNumber() {
		return mrulenum;
	}
	
	public String getRuleName() {
		return RULENAMES[mrulenum];
	}
	
	public int getAssertionNumber() {
		return massnum;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append('[').append(RULENAMES[mrulenum]);
		for( Z3ProofRule pr : mantecedents )
			sb.append(' ').append(pr.toString());
		sb.append(' ').append(mres.toString()).append(']');
		return sb.toString();
	}
	
	public static class Z3ProofRulePrinter {
		private int mindent = 0;
		private PrintStream ps;
		public Z3ProofRulePrinter(PrintStream out) {
			ps = out;
		}
		private void indent() {
			for( int i = 0; i < mindent; ++i )
				ps.print(' ');
		}
		public void print(Z3ProofRule pr) {
			indent();
			ps.print('[');
			ps.print(RULENAMES[pr.mrulenum]);
			ps.print('\n');
			mindent += 2;
			for( Z3ProofRule p : pr.mantecedents )
				print(p);
			indent();
			ps.print(pr.mres.toString());
			ps.print("]\n");
			mindent -= 2;
		}
	};

}
