/*
 * Copyright (C) 2026 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */

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
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Java translation of the Z3 Python example "Enumeration of Minimal Unsatisfiable Cores and Maximal Satisfying Subsets"
 * https://microsoft.github.io/z3guide/programming/Example%20Programs/Cores%20and%20Satisfying%20Subsets/
 */
public class MusEnumerator {

	public record MusEnumeratorResult(Type type, Set<Integer> indices, List<Term> terms) {
		public enum Type {
			MUS, MSS
		}
	}

	public static List<MusEnumeratorResult> enumerate(final Script subsetSolverScript, final Script mapSolverScript,
			final List<Term> constraints, final ILogger logger) {
		final SubsetSolver subsetSolver = new SubsetSolver(subsetSolverScript, constraints);
		final MapSolver mapSolver = new MapSolver(mapSolverScript, constraints.size());
		return enumerate(subsetSolver, mapSolver, logger);
	}

	static List<MusEnumeratorResult> enumerate(final SubsetSolver csolver, final MapSolver msolver,
			final ILogger logger) {
		final List<MusEnumeratorResult> results = new ArrayList<>();

		while (true) {
			final Set<Integer> seed = msolver.nextSeed(); // MapSolver -> checkSat / getModel

			if (seed == null) {
				break;
			}

			if (csolver.checkSubset(seed)) { // SubsetSolver -> checkSat
				// Found MSS
				final Set<Integer> mss = csolver.grow(new HashSet<>(seed));

				if (!mss.isEmpty()) {
					results.add(new MusEnumeratorResult(MusEnumeratorResult.Type.MSS, mss,
							mss.stream().map(i -> csolver.mConstraints.get(i)).toList()));
				}
				msolver.blockDown(mss);
			} else {
				// Found MUS
				final Set<Integer> mus = csolver.shrink(seed); // SubsetSolver -> seedFromCore -> getUnsatCore

				if (!mus.isEmpty()) {
					results.add(new MusEnumeratorResult(MusEnumeratorResult.Type.MUS, mus,
							mus.stream().map(i -> csolver.mConstraints.get(i)).toList()));
				}
				msolver.blockUp(mus);
			}
		}

		return results;
	}

	static class SubsetSolver {
		private final Script mScript;
		private final List<Term> mConstraints;
		private final Map<Integer, Term> mVarCache = new HashMap<>();

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

			if (!mVarCache.containsKey(i)) {
				final String name = "c" + String.valueOf(i);
				mScript.declareFun(name, new Sort[0], mScript.getTheory().getBooleanSort());
				final Term v = mScript.term(name);

				mVarCache.put(i, v);
			}

			return mVarCache.get(i);
		}

		public boolean checkSubset(final Set<Integer> seed) {
			final Term[] assumptions = seed.stream().map(this::cVar).toArray(Term[]::new);
			final LBool result = mScript.checkSatAssuming(assumptions);
			assert result != LBool.UNKNOWN;
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

		private List<Integer> seedFromCore() {
			final List<Integer> result = new ArrayList<>();
			final Term[] core = mScript.getUnsatCore();

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

				if (!checkSubset(current)) {
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

	static class MapSolver {
		private final Script mScript;
		private final Set<Integer> mAllN = new HashSet<>();

		public MapSolver(final Script script, final int n) {
			mScript = script;

			if (mScript instanceof SMTInterpol) {
				mScript.setLogic(Logics.ALL);
			}

			for (int i = 0; i < n; i++) {
				mAllN.add(i);
			}
		}

		public Set<Integer> nextSeed() {
			final LBool res = mScript.checkSat();
			assert res != LBool.UNKNOWN;

			if (res == LBool.UNSAT) {
				return null;
			}

			final Model model = mScript.getModel();
			final Map<Integer, Term> evaluations = new HashMap<>();
			for (final FunctionSymbol fs : model.getDefinedFunctions()) {
				assert fs.getParameterSorts().length == 0
						&& fs.getReturnSort().equals(mScript.getTheory().getBooleanSort());

				final Term valueTerm = model.getFunctionDefinition(fs.getName(), new TermVariable[0]);
				evaluations.put(Integer.valueOf(fs.getName()), valueTerm);
			}

			final Set<Integer> seed = new HashSet<>(mAllN);
			final Set<Integer> toRemove = new HashSet<>();
			for (final Integer i : evaluations.keySet()) {
				final Term valueTerm = evaluations.get(i);

				if (valueTerm.equals(mScript.getTheory().mFalse)) {
					toRemove.add(i);
				}
			}
			seed.removeAll(toRemove);

			return seed;
		}

		private Set<Integer> complement(final Set<Integer> set) {
			final Set<Integer> result = new HashSet<>(mAllN);
			result.removeAll(set);

			return result;
		}

		public void blockDown(final Set<Integer> fromPoint) {
			final Set<Integer> complement = complement(fromPoint);

			final List<Term> lits = new ArrayList<>();
			for (final int i : complement) {
				if (mScript.getTheory().getFunctionSymbol(String.valueOf(i)) == null) {
					mScript.declareFun(Integer.toString(i), new Sort[0], mScript.getTheory().getBooleanSort());
				}
				lits.add(mScript.term(Integer.toString(i)));
			}

			mScript.assertTerm(SmtUtils.or(mScript, lits));
		}

		public void blockUp(final Set<Integer> fromPoint) {
			final List<Term> lits = new ArrayList<>();
			for (final int i : fromPoint) {
				if (mScript.getTheory().getFunctionSymbol(String.valueOf(i)) == null) {
					mScript.declareFun(Integer.toString(i), new Sort[0], mScript.getTheory().getBooleanSort());
				}
				lits.add(mScript.term("not", mScript.term(Integer.toString(i))));
			}

			mScript.assertTerm(SmtUtils.or(mScript, lits));
		}
	}
}
