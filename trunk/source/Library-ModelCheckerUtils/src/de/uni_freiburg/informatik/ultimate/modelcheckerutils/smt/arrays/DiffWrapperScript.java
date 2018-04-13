/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.WrapperScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 * A wrapper script to add support for {@literal @}diff for scripts that do not support it, e.g. external solvers. We
 * declare the internal function so that the outside script can use it. When asserting a term, there are corresponding
 * non-polymorphic uninterpreted diff functions created for each array sort. The diff terms are then replaced
 * accordingly. Finally we instantiate the diff axiom for all terms used in the asserted term.
 *
 * @author Jochen Hoenicke
 */
public class DiffWrapperScript extends WrapperScript {

	/**
	 * All declared non-polymorphic diff functions.
	 */
	private ScopedHashMap<Sort, String> mDiffFunctions;

	/**
	 * All instantiated diff axioms.
	 */
	private ScopedHashSet<Doubleton<Term>> mDiffAxioms;

	private final static String DIFF_FUNCTION_PREFIX = "ULTIMATE@diff";

	/**
	 * Create a new script adding diff support around some existing script.
	 *
	 * @param script
	 *            The wrapped script.
	 */
	public DiffWrapperScript(final Script script) {
		super(script);
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		mScript.setLogic(logic);
		setupDiffFunction();
		mDiffFunctions = new ScopedHashMap<>();
		mDiffAxioms = new ScopedHashSet<>();
	}

	private void setupDiffFunction() {
		final Theory theory = mScript.term("true").getSort().getTheory();
		final Sort[] vars = theory.createSortVariables("Index", "Elem");
		final Sort array = theory.getSort("Array", vars);
		theory.declareInternalPolymorphicFunction("@diff", vars, new Sort[] { array, array }, vars[0], 0);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mScript.setLogic(logic);
		setupDiffFunction();
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		mScript.push(levels);
		for (int i = 0; i < levels; i++) {
			mDiffFunctions.beginScope();
			mDiffAxioms.beginScope();
		}
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		mScript.pop(levels);
		for (int i = 0; i < levels; i++) {
			mDiffFunctions.endScope();
			mDiffAxioms.endScope();
		}
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		term = new FormulaUnLet().unlet(term);
		term = new DiffTransformer().transform(term);
		term = new FormulaLet().let(term);
		return mScript.assertTerm(term);
	}

	/**
	 * Get a unique name for a sort s that can be used as part of identifier.
	 *
	 * @param sort
	 *            the sort to get a name for
	 * @return the name.
	 */
	private String wrap(final Sort sort) {
		final StringBuilder sb = new StringBuilder();
		sb.append(sort.getName());
		if (sort.getIndices() != null) {
			for (final BigInteger index : sort.getIndices()) {
				sb.append('@').append(index);
			}
		}
		if (sort.getArguments() != null) {
			for (final Sort arg : sort.getArguments()) {
				sb.append('_').append(wrap(arg));
			}
		}
		return sb.toString();
	}

	private final class DiffTransformer extends TermTransformer {

		private String checkOrDeclare(final Sort arraySort) {
			String fsymName = mDiffFunctions.get(arraySort);
			if (fsymName == null) {
				final Sort[] indexElemSorts = arraySort.getArguments();
				final Sort indexSort = indexElemSorts[0];
				fsymName = DIFF_FUNCTION_PREFIX + wrap(indexElemSorts[0]) + wrap(indexElemSorts[1]);
				declareFun(fsymName, new Sort[] { arraySort, arraySort }, indexSort);
				mDiffFunctions.put(arraySort, fsymName);
			}
			return fsymName;
		}

		private void checkOrAddAxiom(final Term diffTerm, final Doubleton<Term> arrays) {
			if (mDiffAxioms.add(arrays)) {
				/*
				 * we neeed to add the diff axiom select(a, diff(a, b)) = select(b, diff(a,b)) ==> a = b
				 */
				final Term a = arrays.getOneElement();
				final Term b = arrays.getOtherElement();
				final Term selectA = term("select", a, diffTerm);
				final Term selectB = term("select", b, diffTerm);
				final Term axiom = term("=>", term("=", selectA, selectB), term("=", a, b));
				mScript.assertTerm(axiom);
			}
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			if (appTerm.getFunction().isIntern() && appTerm.getFunction().getName() == "@diff") {
				final String diffSymbol = checkOrDeclare(newArgs[0].getSort().getRealSort());
				final Term result = appTerm.getTheory().term(diffSymbol, newArgs);
				final Doubleton<Term> paramPair = new Doubleton<>(newArgs[0], newArgs[1]);
				checkOrAddAxiom(result, paramPair);
				setResult(result);
			} else {
				super.convertApplicationTerm(appTerm, newArgs);
			}
		}
	}
}
