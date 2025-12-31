package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Java translation of the Z3 Python example for MUS/MSS enumeration (Liffiton style).
 *
 * This example closely follows the algorithm on
 * https://microsoft.github.io/z3guide/programming/Example%20Programs/Cores%20and%20Satisfying%20Subsets/
 */
public class LiffitonMusExample {

//	public static void main(final String[] args) {
//		final SMTInterpol script = new SMTInterpol();
//		script.setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, "true");
//		script.setLogic(Logics.QF_LRA);
//		// script.setLogic(Logics.ALL);
//
//		final Sort realSort = script.getTheory().getRealSort();
//		script.declareFun("x", new Sort[0], realSort);
//		script.declareFun("y", new Sort[0], realSort);
//		final Term x = script.term("x");
//		final Term y = script.term("y");
//
//		final Term zero = script.numeral("0");
//		final Term one = script.numeral("1");
//		final Term two = script.numeral("2");
//
//		// Build constraints corresponding to the original example
//		// x > 2, x < 1, x < 0, Or(x + y > 0, y < 0), Or(y >= 0, x >= 0), Or(y < 0, x < 0), Or(y > 0, x < 0)
//		final List<Term> constraints = new ArrayList<>() {
//			{
//				add(SmtUtils.greater(script, x, two));
//				add(SmtUtils.less(script, x, one));
//				add(SmtUtils.less(script, x, zero));
//				add(SmtUtils.or(script, SmtUtils.greater(script, SmtUtils.sum(script, "+", x, y), zero),
//						SmtUtils.less(script, y, zero)));
//				add(SmtUtils.or(script, SmtUtils.geq(script, y, zero), SmtUtils.geq(script, x, zero)));
//				add(SmtUtils.or(script, SmtUtils.less(script, y, zero), SmtUtils.less(script, x, zero)));
//				add(SmtUtils.or(script, SmtUtils.greater(script, y, zero), SmtUtils.less(script, x, zero)));
//			}
//		};
//
//		final SubsetSolver csolver = new SubsetSolver(script, constraints);
//		final MapSolver msolver = new MapSolver(constraints.size());
//
//		System.out.println("Starting MUS/MSS enumeration:");
//		for (final Set<Integer> result : enumerateSets(csolver, msolver, null)) {
//			// System.out.println(result);
//		}
//	}

	public static Iterable<Set<Integer>> enumerateSets(final SubsetSolver csolver, final MapSolver msolver,
			final ILogger logger) {
		final List<Set<Integer>> results = new ArrayList<>();

		while (true) {
			final Set<Integer> seed = msolver.nextSeed();

			if (seed == null) {
				break;
			}

			if (csolver.checkSubset(seed)) { // <--- CSolver checkSat
				final Set<Integer> mss = csolver.grow(new HashSet<>(seed));
				msolver.blockDown(mss);

//				if (!mss.isEmpty()) {
//					results.add(mss);
//				}

//				if (logger != null) {
//					logger.info("MSS: " + mss);
//				} else {
//					System.out.println("MSS: " + mss);
//				}
			} else {
				final Set<Integer> mus = csolver.shrink(seed); // <--- CSolver getUnsatCore
				msolver.blockUp(mus);

				if (!mus.isEmpty()) {
					results.add(mus);
				}

				if (logger != null) {
					logger.info("MUS: " + mus);
				} else {
					System.out.println("MUS: " + mus);
				}
			}
		}

		return results;
	}

	public static class SubsetSolver {
		private final Script mScript;
		private final List<Term> mConstraints;
		private final Map<Integer, Term> varcache = new HashMap<>();

		public SubsetSolver(final Script script, final List<Term> constraints) {
			mScript = script;
			mConstraints = constraints;

			for (int i = 0; i < mConstraints.size(); i++) {
				final Term cVar = cVar(i);
				final Term annotated = script.annotate(script.term("=>", cVar, constraints.get(i)),
						new Annotation(":named", "n" + String.valueOf(i)));
				script.assertTerm(annotated);
			}
		}

		private Term cVar(final int i) {
			assert i >= 0 && i < mConstraints.size();

			if (!varcache.containsKey(i)) {
				// final String name = String.format("c%d ", i) + mConstraints.get(i).toString();
				final String name = "c" + String.valueOf(i);
				mScript.declareFun(name, new Sort[0], mScript.getTheory().getBooleanSort());
				final Term v = mScript.term(name);

				varcache.put(i, v);
			}

			return varcache.get(i);
		}

		public boolean checkSubset(final Set<Integer> seed) {
			return checkSubset(seed, false);
		}

		public boolean checkSubset(final Set<Integer> seed, final boolean doNotPopIfUnsat) { // <--- CSolver checkSat
			final Term[] assumptions = seed.stream().map(this::cVar).toArray(Term[]::new);

			mScript.push(1);

			for (final Term assumption : assumptions) {
				mScript.assertTerm(assumption);
			}

			// final LBool result = mScript.checkSatAssuming(assumptions);
			final LBool result = mScript.checkSat();
			assert result != LBool.UNKNOWN;

			if (!doNotPopIfUnsat || result != LBool.UNSAT) {
				mScript.pop(1);
			}

			return result == LBool.SAT;
		}

		public Set<Integer> complement(final Set<Integer> set) {
			final Set<Integer> result = new HashSet<>();

			for (int i = 0; i < mConstraints.size(); i++) {
				if (!set.contains(i)) {
					result.add(i);
				}
			}

			return result;
		}

		private List<Integer> seedFromCore() { // <--- CSolver getUnsatCore
			final List<Integer> result = new ArrayList<>();
			final Term[] core = mScript.getUnsatCore();

			mScript.pop(1);

			for (final Term t : core) {
				final String name = ((ApplicationTerm) t).getFunction().getName().substring(1);
				final Integer i = Integer.parseInt(name);
				result.add(i);
			}

			return result;
		}

		public Set<Integer> shrink(final Set<Integer> seed) {
			Set<Integer> current = new HashSet<>(seed);

			for (final int i : seed) {
				if (!current.contains(i)) {
					continue;
				}

				current.remove(i);

				if (!checkSubset(current, true)) {
					current = new HashSet<>(seedFromCore());
				} else {
					current.add(i);
				}
			}

			return current;
		}

		public Set<Integer> grow(final Set<Integer> seed) {
			final Set<Integer> current = new HashSet<>(seed);

			for (final int i : complement(seed)) {
				current.add(i);

				if (!checkSubset(current)) {
					current.remove(i);
				}
			}

			return current;
		}
	}

	public static class MapSolver {
		private final Script mScript;
		private final Set<Integer> mAllIndices = new HashSet<>();
		private final Map<Integer, Term> mModelVars = new HashMap<>();

		public MapSolver(final int n) {
			this(n, new SMTInterpol());
		}

		public MapSolver(final int n, final Script script) {
			mScript = script;

			if (mScript instanceof SMTInterpol) {
				mScript.setLogic(Logics.ALL);
			}

			for (int i = 0; i < n; i++) {
				mAllIndices.add(i);
			}
		}

//		public Map<Term, Term> getModelAssignments(final Model model) {
//			final Map<Term, Term> results = new HashMap<>();
//
//			for (final FunctionSymbol fs : model.getDefinedFunctions()) {
//				// Nur Bool-Konstanten
//				if (fs.getParameterSorts().length == 0
//						&& fs.getReturnSort().equals(mScript.getTheory().getBooleanSort())) {
//
//					// Definition holen
//					final Term valueTerm = model.getFunctionDefinition(fs.getName(), new TermVariable[0]);
//
//					final boolean isTrue = valueTerm.toString().equals("true");
//					final boolean isFalse = valueTerm.toString().equals("false");
//
//					results.put(mScript.term(fs.getName()), valueTerm);
//				}
//			}
//
//			return results;
//		}

		public Set<Integer> nextSeed() {
			// Check satisfiability ------------------------------------------------------------------------------------
			final LBool res = mScript.checkSat();
			assert res != LBool.UNKNOWN;

			if (res == LBool.UNSAT) {
				return null;
			}

			final Model model = mScript.getModel();
			final Set<Integer> seed = new HashSet<>(mAllIndices);
			final Set<Integer> toRemove = new HashSet<>();

//			for (final var evaluation : evaluations.entrySet()) {
//				final Term v = evaluation.getKey();
//				final Term val = evaluation.getValue();
//				final int i = Integer.parseInt(((ApplicationTerm) v).getFunction().getName());
//
//				if (val.equals(mScript.getTheory().mFalse)) {
//					toRemove.add(i);
//				}
//			}

			for (final Integer i : mModelVars.keySet()) {
				final Term v = mModelVars.get(i);
				final Term val = model.evaluate(v);

				if (val.equals(mScript.getTheory().mFalse)) {
					toRemove.add(i);
				}
			}
			seed.removeAll(toRemove);

			return seed;
		}

		private Set<Integer> complement(final Set<Integer> set) {
			final Set<Integer> result = new HashSet<>(mAllIndices);
			result.removeAll(set);

			return result;
		}

		public void blockDown(final Set<Integer> fromPoint) {
			final Set<Integer> comp = complement(fromPoint);

			final List<Term> lits = new ArrayList<>();
			for (final int i : comp) {
				if (!mModelVars.containsKey(i)) {
					mScript.declareFun(Integer.toString(i), new Sort[0], mScript.getTheory().getBooleanSort());
					mModelVars.put(i, mScript.term(Integer.toString(i)));
				}

				lits.add(mModelVars.get(i));
			}

			mScript.assertTerm(SmtUtils.or(mScript, lits));
		}

		public void blockUp(final Set<Integer> fromPoint) {
			final List<Term> lits = new ArrayList<>();
			for (final int i : fromPoint) {
				if (!mModelVars.containsKey(i)) {
					mScript.declareFun(Integer.toString(i), new Sort[0], mScript.getTheory().getBooleanSort());
					mModelVars.put(i, mScript.term(Integer.toString(i)));
				}

				lits.add(mScript.term("not", mModelVars.get(i)));
			}

			mScript.assertTerm(SmtUtils.or(mScript, lits));
		}
	}
}
