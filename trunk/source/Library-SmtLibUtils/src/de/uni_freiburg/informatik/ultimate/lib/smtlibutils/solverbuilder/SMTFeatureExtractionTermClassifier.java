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

package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class SMTFeatureExtractionTermClassifier extends NonRecursive {

	private Set<Term> mTermsInWhichWeAlreadyDescended;
	private final Map<String, Integer> mOccuringSortNames;
	private final Map<String, Integer> mOccuringFunctionNames;
	private final Map<Integer, Integer> mOccuringQuantifiers;
	private boolean mHasArrays;
	private int mNumberOfArrays;
	private int mNumberOfVariables;
	private int mNumberOfFunctions;
	private int mNumberOfQuantifiers;
	private int mDAGSize;
	private long mTreeSize;
	private final UnionFind<Term> mVariableEquivalenceClasses;
	private Map<Integer, Set<Term>> mTermsets;
	private int mBiggestEquivalenceClass;
	private final ArrayList<String> mAssertionStack;
	private final Map<Term, Integer> mVariableToCount;

	public SMTFeatureExtractionTermClassifier() {
		mOccuringSortNames = new HashMap<>();
		mOccuringFunctionNames = new HashMap<>();
		mOccuringQuantifiers = new HashMap<>();
		mHasArrays = false;
		mNumberOfArrays = 0;
		mNumberOfVariables = 0;
		mNumberOfFunctions = 0;
		mNumberOfQuantifiers = 0;
		mDAGSize = 0;
		mTreeSize = 0;
		mAssertionStack = new ArrayList<>();
		mVariableEquivalenceClasses = new UnionFind<>();
		mTermsets = new HashMap<>();
		mBiggestEquivalenceClass = 0;
		mVariableToCount = new HashMap<>();
	}

	/**
	 * Check a/another Term and add the result to the existing classification results.
	 */
	public void checkTerm(final Term term) {
		mTermsInWhichWeAlreadyDescended = new HashSet<>();
		mAssertionStack.add(term.toString());
		mDAGSize += new DAGSize().size(term);
		mTreeSize += new DAGSize().treesize(term);
		run(new MyWalker(term));
		mTermsInWhichWeAlreadyDescended = null;
	}

	public enum ScoringMethod {
		NUM_FUNCTIONS, NUM_VARIABLES, DAGSIZE, DEPENDENCY, BIGGEST_EQUIVALENCE_CLASS, AVERAGE_EQUIVALENCE_CLASS,
		NUMBER_OF_EQUIVALENCE_CLASSES, NUMBER_OF_SELECT_FUNCTIONS, NUMBER_OF_STORE_FUNCTIONS, COMPARE_FEATURES,
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

	public Map<String, Integer> getOccuringFunctionNames() {
		return mOccuringFunctionNames;
	}

	public Map<Integer, Integer> getOccuringQuantifiers() {
		return mOccuringQuantifiers;
	}

	public Map<String, Integer> getOccuringSortNames() {
		return mOccuringSortNames;
	}

	public ArrayList<Integer> getVariableEquivalenceClassSizes() {
		final ArrayList<Integer> sizes = new ArrayList<>();
		mVariableEquivalenceClasses.getAllEquivalenceClasses().forEach(e -> {
			sizes.add(e.size());
		});
		return sizes;
	}

	public int getBiggestEquivalenceClass() {
		return mBiggestEquivalenceClass;
	}

	public ArrayList<String> getAssertionStack() {
		return mAssertionStack;
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

	public UnionFind<Term> getEquivalenceClasses() {
		return mVariableEquivalenceClasses;
	}

	public static double normalize(final double score, final double lower_bound, final double upper_bound) {
		// Normalizes a given value to a certain interval.
		// Normalize to [0,1]
		double normalized_score = 1.0 - 1.0 / (score != 0 ? (double) score : 1.0);
		// Scale to [lower_bound,upper_bound]
		final double range = upper_bound - lower_bound;
		return normalized_score * range + lower_bound;
	}

	public double getScore(final ScoringMethod scoringMethod) {
		int score = 0;
		if (scoringMethod == ScoringMethod.DEPENDENCY) {
			score = getDependencyScore();
		} else if (scoringMethod == ScoringMethod.NUM_FUNCTIONS) {
			score = getNumberOfFunctions();
		} else if (scoringMethod == ScoringMethod.NUM_VARIABLES) {
			score = getNumberOfVariables();
		} else if (scoringMethod == ScoringMethod.DAGSIZE) {
			score = getDAGSize();
		} else if (scoringMethod == ScoringMethod.BIGGEST_EQUIVALENCE_CLASS) {
			score = getBiggestEquivalenceClass();
		} else if (scoringMethod == ScoringMethod.AVERAGE_EQUIVALENCE_CLASS) {
			score = (int) getVariableEquivalenceClassSizes().stream().mapToInt(val -> val).average().orElse(0);
		} else if (scoringMethod == ScoringMethod.NUMBER_OF_EQUIVALENCE_CLASSES) {
			score = getVariableEquivalenceClassSizes().size();
		} else if (scoringMethod == ScoringMethod.NUMBER_OF_SELECT_FUNCTIONS) {
			score = getOccuringFunctionNames().getOrDefault("select", 0);
		} else if (scoringMethod == ScoringMethod.NUMBER_OF_STORE_FUNCTIONS) {
			score = getOccuringFunctionNames().getOrDefault("store", 0);
		} else if (scoringMethod == ScoringMethod.COMPARE_FEATURES) {
			// Dummy score
			score = 1;
		}
		return normalize(score, 0.5, 1);
	}

	private static boolean isApplicationTermWithArityZero(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			if (appterm.getParameters().length == 0) {
				return true;
			}
		}
		return false;
	}

	private int calcDependencyScore() {
		int score = 0;
		for (final Set<Term> eqclass : mVariableEquivalenceClasses.getAllEquivalenceClasses()) {
			// quadratic score, punishes equivalence classes which are large harder.
			final int classSize = eqclass.size();
			if (classSize > mBiggestEquivalenceClass) {
				mBiggestEquivalenceClass = classSize;
			}
			score += Math.pow(classSize, 2);
		}
		return score;
	}

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
				if (!term.toStringDirect().equals("true") && !term.toStringDirect().equals("false")
						&& (term instanceof TermVariable || isApplicationTermWithArityZero(term))) {
					final Sort currentSort = term.getSort();
					final String currentSortName = term.getSort().toString();
					// Count occurrences of sorts.
					if (mOccuringSortNames.containsKey(currentSortName)) {
						mOccuringSortNames.put(currentSortName, mOccuringSortNames.get(currentSortName) + 1);
					} else {
						mOccuringSortNames.put(currentSortName, 1);
					}

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

		private void createAndAddToTermset(final int eq_class_id, final Term... terms) {
			final Set<Term> termset = new HashSet<>(Arrays.asList(terms));
			termset.addAll(mTermsets.getOrDefault(eq_class_id, Collections.emptySet()));
			mTermsets.put(eq_class_id, termset);
		}

		private void collectVariables(final ApplicationTerm term, final String functionname, final int eq_class_id) {
			final Term[] termParameters = term.getParameters();

			if (termParameters.length == 1) {
				createAndAddToTermset(eq_class_id, termParameters[0]);
			}

			for (int i = 0; i < termParameters.length - 1; i++) {
				final Term term1 = termParameters[i];
				final Term term2 = termParameters[i + 1];
				if ((isApplicationTermWithArityZero(term1) || term1 instanceof TermVariable)
						&& (isApplicationTermWithArityZero(term2) || term2 instanceof TermVariable)) {
					// Base case
					// Both terms are Terms of Arity 0 or Termvariables.
					if (functionname.equals("or")) {
						// if the function is or, both are in separate sets.
						createAndAddToTermset(eq_class_id, term1);
						// create new eq_class
						createAndAddToTermset(mTermsets.size() + 1, term2);
					}
					// else if(functionname.equals("and")) {
					// If the function is and, both go into the same termset.
					// createAndAddToTermset(eq_class_id, term1, term2);
					// }

					else {
						// else both go into the same termset.
						createAndAddToTermset(eq_class_id, term1, term2);

					}

				} else if (isApplicationTermWithArityZero(term1) && term2 instanceof ConstantTerm) {
					// Constant terms go into the current equivalence class
					createAndAddToTermset(eq_class_id, term1);

				} else if (isApplicationTermWithArityZero(term2) && term1 instanceof ConstantTerm) {
					// Constant terms go into the current termset
					createAndAddToTermset(eq_class_id, term2);

				} else if (isApplicationTermWithArityZero(term1) || term1 instanceof TermVariable) {
					// If we are here, term1 is a Termvariable or an Applicationterm with arity 0
					// In this case we can add this term to the current termset.
					createAndAddToTermset(eq_class_id, term1);

					// Term 2 has to be explored further. If the function is "or", we create a new
					// termset.
					final int new_class_id = functionname.equals("or") ? mTermsets.size() + 1 : eq_class_id;
					if (term2 instanceof ApplicationTerm) {
						collectVariables((ApplicationTerm) term2, ((ApplicationTerm) term2).getFunction().getName(),
								new_class_id);
					}

				} else if (isApplicationTermWithArityZero(term2) || term2 instanceof TermVariable) {
					createAndAddToTermset(eq_class_id, term2);

					final int new_class_id = functionname.equals("or") ? mTermsets.size() + 1 : eq_class_id;
					if (term1 instanceof ApplicationTerm) {
						collectVariables((ApplicationTerm) term1, ((ApplicationTerm) term1).getFunction().getName(),
								new_class_id);
					}
				} else if (term1 instanceof ApplicationTerm && term2 instanceof ApplicationTerm) {
					collectVariables((ApplicationTerm) term1, ((ApplicationTerm) term1).getFunction().getName(),
							eq_class_id);
					// Term 2 is a new EQ class
					final int new_class_id = functionname.equals("or") ? mTermsets.size() + 1 : eq_class_id;
					collectVariables((ApplicationTerm) term2, ((ApplicationTerm) term2).getFunction().getName(),
							new_class_id);
				}
			}
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			// Functions are ApplicationTerms that have >0 parameters
			// Variables are ApplicationTerms that have 0 Parameters.
			if (term.getParameters().length > 0) {
				final String functionName = term.getFunction().getName();
				// Count occurrences of functions.
				if (mOccuringFunctionNames.containsKey(functionName)) {
					mOccuringFunctionNames.put(functionName, mOccuringFunctionNames.get(functionName) + 1);
				} else {
					mOccuringFunctionNames.put(functionName, 1);
				}
				// Collect Terms which occur together, then create EQ classes.
				mTermsets = new HashMap<>();
				final int eq_class_id = 0;
				collectVariables(term, functionName, eq_class_id);
				mTermsets.forEach((k, v) -> {
					v.forEach(e -> {
						mVariableEquivalenceClasses.findAndConstructEquivalenceClassIfNeeded(e);
					});
					mVariableEquivalenceClasses.union(v);
				});
				mNumberOfFunctions += 1;
			} else {
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
			final int quantifier = term.getQuantifier();
			if (mOccuringQuantifiers.containsKey(term.getQuantifier())) {
				mOccuringQuantifiers.put(quantifier, mOccuringQuantifiers.get(quantifier) + 1);
			} else {
				mOccuringQuantifiers.put(quantifier, 1);
			}
			mNumberOfQuantifiers += 1;
			walker.enqueueWalker(new MyWalker(term.getSubformula()));
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			if (mVariableToCount.containsKey(term)) {
				mVariableToCount.put(term, mVariableToCount.get(term) + 1);
			} else {
				mVariableToCount.put(term, 1);
				mNumberOfVariables += 1;
			}
			// cannot descend
		}

		@Override
		public void walk(final NonRecursive walker, final LambdaTerm term) {
			throw new UnsupportedOperationException();
		}

	}

}
