/*
 * Copyright (C) 2019 Julian Löffler (loefflju@informatik.uni-freiburg.de), Breee@github
 * Copyright (C) 2012-2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;


public class SMTFeatureExtractionTermClassifier extends NonRecursive{

	private final ILogger mLogger;

	private Set<Term> mTermsInWhichWeAlreadyDescended;
	private final Set<String> mOccuringSortNames;
	private final Set<String> mOccuringFunctionNames;
	private final Set<Integer> mOccuringQuantifiers;
	private boolean mHasArrays;
	private int mNumberOfArrays;
	private int mNumberOfVariables;
	private int mNumberOfFunctions;
	private int mNumberOfQuantifiers;
	private int mDAGSize;
	private long mTreeSize;
	private final UnionFind<Term> mVariableEquivalenceClasses;
	private final ArrayList<String> mTerms;

	private class MyWalker extends TermWalker {
		MyWalker(final Term term) {
			super(term);
		}

		@Override
		public void walk(final NonRecursive walker) {
			if (mTermsInWhichWeAlreadyDescended.contains(getTerm())) {
				// do nothing
			} else {
				final Term term = getTerm();
				// Add sorts only if term is TermVariable or ApplicationTerm with arity 0.
				if(!term.toStringDirect().equals("true") && !term.toStringDirect().equals("false")
						&& ((term instanceof TermVariable) || isApplicationTermWithArityZero(term))) {
					final Sort currentSort = term.getSort();
					mOccuringSortNames.add(currentSort.toString());
					if (currentSort.isArraySort()) {
						mHasArrays = true;
						mNumberOfArrays += 1;
					}
				}
				super.walk(walker);
			}
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			mTermsInWhichWeAlreadyDescended.add(term);
			walker.enqueueWalker(new MyWalker(term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			final int numberOfParameters = term.getParameters().length;
			if(numberOfParameters > 0) {
				final String functionName = term.getFunction().getName();
				mOccuringFunctionNames.add(functionName);
				mLogger.warn("######################## START #######################");
				mLogger.warn("FUNCTION: " + functionName);
				mLogger.warn("TERM: " + term.toStringDirect());
				final Term[] termParameters = term.getParameters();
				for (int i = 0; i < (termParameters.length - 1); i++) {
					final Term term1 = termParameters[i];
					final Term term2 = termParameters[i+1];
					if (isApplicationTermWithArityZero(term1)  && isApplicationTermWithArityZero(term2) ) {
						final Term rep1 = mVariableEquivalenceClasses.findAndConstructEquivalenceClassIfNeeded(term1);
						final Term rep2 = mVariableEquivalenceClasses.findAndConstructEquivalenceClassIfNeeded(term2);
						mLogger.warn("REP1: " + rep1.toStringDirect());
						mLogger.warn("REP2: " + rep2.toStringDirect());
						mVariableEquivalenceClasses.union(rep1, rep2);
					}
				}
				mLogger.warn("######################### END #########################");

				mNumberOfFunctions += 1;
			}else {
				mNumberOfVariables += 1;
			}

			mTermsInWhichWeAlreadyDescended.add(term);
			for (final Term t : term.getParameters()) {
				walker.enqueueWalker(new MyWalker(t));
			}
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// cannot descend
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			mTermsInWhichWeAlreadyDescended.add(term);
			walker.enqueueWalker(new MyWalker(term.getSubTerm()));
			for (final Term v : term.getValues()) {
				walker.enqueueWalker(new MyWalker(v));
			}

		}

		@Override
		public void walk(final NonRecursive walker, final MatchTerm term) {
			throw new UnsupportedOperationException("not yet implemented: MatchTerm");
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			mOccuringQuantifiers.add(term.getQuantifier());
			mNumberOfQuantifiers += 1;
			walker.enqueueWalker(new MyWalker(term.getSubformula()));
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// cannot descend
		}
	}


	public SMTFeatureExtractionTermClassifier(final ILogger logger) {
		super();
		mLogger = logger;
		mOccuringSortNames = new HashSet<>();
		mOccuringFunctionNames = new HashSet<>();
		mOccuringQuantifiers = new HashSet<>();
		mHasArrays = false;
		mNumberOfArrays = 0;
		mNumberOfVariables = 0;
		mNumberOfFunctions = 0;
		mNumberOfQuantifiers = 0;
		mDAGSize = 0;
		mTreeSize = 0;
		mTerms = new ArrayList<>();
		mVariableEquivalenceClasses = new UnionFind<>();
	}

	/**
	 * Check a/another Term and add the result to the existing classification results.
	 */
	public void checkTerm(final Term term) {
		mTermsInWhichWeAlreadyDescended = new HashSet<>();
		mTerms.add(term.toString());
		mDAGSize += new DAGSize().size(term);
		mTreeSize += new DAGSize().treesize(term);
		mLogger.warn("FULL TERM: " + term.toStringDirect());
		run(new MyWalker(term));
		mTermsInWhichWeAlreadyDescended = null;
		mLogger.warn("UNION FIND: "  + mVariableEquivalenceClasses.toString());
	}

	public int getDAGSize() {
		return mDAGSize;
	}

	public int getNumberOfFunctions() {
		return mNumberOfFunctions;
	}

	public int getNumberOfQuantifiers() {
		return mNumberOfQuantifiers;
	}

	public int getNumberOfVariables() {
		return mNumberOfVariables;
	}

	public int getNumberOfArrays() {
		return mNumberOfArrays;
	}

	public Set<String> getOccuringFunctionNames() {
		return mOccuringFunctionNames;
	}

	public Set<Integer> getOccuringQuantifiers() {
		return mOccuringQuantifiers;
	}

	public Set<String> getOccuringSortNames() {
		return mOccuringSortNames;
	}


	public ArrayList<String> getTerm() {
		return mTerms;
	}

	public long getTreeSize() {
		return mTreeSize;
	}

	public boolean hasArrays() {
		return mHasArrays;
	}

	public int getDependencyScore() {
		return calcDependencyScore();
	}

	private boolean isApplicationTermWithArityZero(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			if(appterm.getParameters().length == 0) {
				return true;
			}
		}
		return false;
	}

	private int calcDependencyScore() {
		int score = 0;
		for (final Set<Term> eqclass : mVariableEquivalenceClasses.getAllEquivalenceClasses()) {
			// quadratic score, punishes equivalence classes which are large harder.
			score += Math.pow(eqclass.size(), 2);
		}
		return score;
	}
}
