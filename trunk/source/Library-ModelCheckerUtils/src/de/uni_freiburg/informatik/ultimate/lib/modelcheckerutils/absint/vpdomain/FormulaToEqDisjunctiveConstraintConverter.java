/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 */
public class FormulaToEqDisjunctiveConstraintConverter extends NonRecursive {

	/**
	 * Does all conjunctive operations on EqConstraints in place, i.e., on the same object if possible. The constraint
	 * remains unfrozen (and must be frozen in order to make all possible propagations at some point..).
	 */
	public static final boolean INPLACE_CONJUNCTIONS = true;

	private final Term mFormula;

	private EqDisjunctiveConstraint<EqNode> mResultConstraint;

	private final EqConstraintFactory<EqNode> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;

	private final Term mTrueTerm;
	private final Term mFalseTerm;

	/**
	 * stores intermediate results of the "recursion"
	 */
	private final Deque<EqDisjunctiveConstraint<EqNode>> mResultStack = new ArrayDeque<>();

	public FormulaToEqDisjunctiveConstraintConverter(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final EqConstraintFactory<EqNode> eqConstraintFactory,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory, final Term formula) {
		mFormula = formula;
		mEqConstraintFactory = eqConstraintFactory;
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;

		mMgdScript = mgdScript;
		mServices = services;

		mMgdScript.lock(this);
		mTrueTerm = mMgdScript.term(this, "true");
		mFalseTerm = mMgdScript.term(this, "false");
		mMgdScript.unlock(this);

		computeResult();
	}

	private void computeResult() {
		final Term formulaInNnf =
				new NnfTransformer(mMgdScript, mServices, QuantifierHandling.CRASH).transform(mFormula);

		final StoreChainSquisher scs = new StoreChainSquisher(mMgdScript);
		final List<Term> conjunction = new ArrayList<>();
		conjunction.add(scs.transform(formulaInNnf));
		conjunction.addAll(scs.getReplacementEquations());
		final Term transFormulaWithSquishedStoreChains = SmtUtils.and(mMgdScript.getScript(), conjunction);

		run(new ConvertTfToEqDisjConsWalker(transFormulaWithSquishedStoreChains));

		assert mResultStack.size() == 1;
		final EqDisjunctiveConstraint<EqNode> processedTf = mResultStack.pop();

		processedTf.closeDisjunctsIfNecessary();
		processedTf.freezeDisjunctsIfNecessary();

		mResultConstraint = processedTf.projectExistentially(scs.getReplacementTermVariables());
	}

	public EqDisjunctiveConstraint<EqNode> getResult() {
		return mResultConstraint;
	}

	class ConvertTfToEqDisjConsWalker extends TermWalker {

		public ConvertTfToEqDisjConsWalker(final Term term) {
			super(term);
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			if ("Bool".equals(term.getSort().getName())) {
				assert false : "TODO: implement";
			} else {
				assert false : "we should have caught this before, right?";
			}
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			walker.enqueueWalker(new ConvertTfToEqDisjConsWalker(term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			if ("=".equals(term.getFunction().getName())) {
				handleXquality(term.getParameters()[0], term.getParameters()[1], true);
			} else if ("distinct".equals(term.getFunction().getName())) {
				handleXquality(term.getParameters()[0], term.getParameters()[1], false);
			} else if ("not".equals(term.getFunction().getName())
					&& SmtUtils.isFunctionApplication(term.getParameters()[0], "=")) {
				final ApplicationTerm innerEqualsTerm = (ApplicationTerm) term.getParameters()[0];
				handleXquality(innerEqualsTerm.getParameters()[0], innerEqualsTerm.getParameters()[1], false);
			} else if ("not".equals(term.getFunction().getName())) {
				handleBooleanTerm(term.getParameters()[0], false);
			} else if ("or".equals(term.getFunction().getName())) {
				walker.enqueueWalker(new MakeDisjunctionWalker(term.getParameters().length));

				for (final Term param : term.getParameters()) {
					walker.enqueueWalker(new ConvertTfToEqDisjConsWalker(param));
				}

			} else if ("and".equals(term.getFunction().getName())) {
				walker.enqueueWalker(new MakeConjunctionWalker(term.getParameters().length));

				for (final Term param : term.getParameters()) {
					walker.enqueueWalker(new ConvertTfToEqDisjConsWalker(param));
				}

			} else if ("false".equals(term.getFunction().getName())) {
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(Collections.emptySet()));
			} else if ("true".equals(term.getFunction().getName())) {
				mResultStack.push(mEqConstraintFactory.getEmptyDisjunctiveConstraint(INPLACE_CONJUNCTIONS));
			} else {
				// we don't recognize this function symbol -- overapproximating its effects by
				// "top"
				// TODO: perhaps we could make some checks here if it is trivially bottom or
				// something like that..
				mResultStack.push(mEqConstraintFactory.getEmptyDisjunctiveConstraint(INPLACE_CONJUNCTIONS));
			}

		}

		private void handleBooleanTerm(final Term term, final boolean polarity) {
			assert "Bool".equals(term.getSort().getName());
			final EqNode tvNode = mEqNodeAndFunctionFactory.getOrConstructNode(term);
			if (polarity) {
				final EqNode trueNode = mEqNodeAndFunctionFactory.getOrConstructNode(mTrueTerm);
				final EqConstraint<EqNode> tvEqualsTrue = mEqConstraintFactory.addEquality(tvNode, trueNode,
						mEqConstraintFactory.getEmptyConstraint(INPLACE_CONJUNCTIONS), INPLACE_CONJUNCTIONS);
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(Collections.singleton(tvEqualsTrue)));
			} else {
				final EqNode falseNode = mEqNodeAndFunctionFactory.getOrConstructNode(mFalseTerm);
				final EqConstraint<EqNode> tvEqualsFalse = mEqConstraintFactory.addEquality(tvNode, falseNode,
						mEqConstraintFactory.getEmptyConstraint(INPLACE_CONJUNCTIONS), INPLACE_CONJUNCTIONS);
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(Collections.singleton(tvEqualsFalse)));
			}
		}

		private void handleXquality(final Term arg1, final Term arg2, final boolean polarity) {
			if (arg1.getSort().isArraySort()) {
				// we have an array equality

				if (!isFunctionTracked(arg1) || !isFunctionTracked(arg2)) {
					// we don't track either side of the equation --> return an empty constraint
					mResultStack.push(mEqConstraintFactory.getEmptyDisjunctiveConstraint(INPLACE_CONJUNCTIONS));
					return;
				}

				ApplicationTerm storeTerm;
				EqNode simpleArray;
				EqNode otherSimpleArray;

				if (SmtUtils.isFunctionApplication(arg1, "store")) {
					assert !SmtUtils.isFunctionApplication(arg2, "store");
					storeTerm = (ApplicationTerm) arg1;
					simpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(arg2);
					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(storeTerm.getParameters()[0]);
				} else if (SmtUtils.isFunctionApplication(arg2, "store")) {
					assert !SmtUtils.isFunctionApplication(arg1, "store");
					storeTerm = (ApplicationTerm) arg2;
					simpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(arg1);
					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(storeTerm.getParameters()[0]);
				} else {
					storeTerm = null;
					simpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(arg1);
					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(arg2);
				}

				final EqConstraint<EqNode> newConstraint;
				if (polarity) {
					if (storeTerm == null) {
						// we have a strong equivalence
						newConstraint = mEqConstraintFactory.addEquality(simpleArray, otherSimpleArray,
								mEqConstraintFactory.getEmptyConstraint(INPLACE_CONJUNCTIONS), INPLACE_CONJUNCTIONS);
					} else {
						final EqNode storeIndex =
								mEqNodeAndFunctionFactory.getOrConstructNode(storeTerm.getParameters()[1]);
						final EqNode storeValue =
								mEqNodeAndFunctionFactory.getOrConstructNode(storeTerm.getParameters()[2]);

						// we have a weak equivalence ..
						final EqConstraint<EqNode> intermediateConstraint = mEqConstraintFactory.addWeakEquivalence(
								simpleArray, otherSimpleArray, storeIndex,
								mEqConstraintFactory.getEmptyConstraint(INPLACE_CONJUNCTIONS), INPLACE_CONJUNCTIONS);
						// .. and an equality on the stored position
						mMgdScript.lock(this);
						final Term selectTerm =
								mMgdScript.term(this, "select", simpleArray.getTerm(), storeTerm.getParameters()[1]);
						mMgdScript.unlock(this);
						final EqNode selectEqNode = mEqNodeAndFunctionFactory.getOrConstructNode(selectTerm);
						newConstraint = mEqConstraintFactory.addEquality(selectEqNode, storeValue,
								intermediateConstraint, INPLACE_CONJUNCTIONS);
					}
				} else {
					if (storeTerm == null) {
						newConstraint = mEqConstraintFactory.addDisequality(simpleArray, otherSimpleArray,
								mEqConstraintFactory.getEmptyConstraint(INPLACE_CONJUNCTIONS), INPLACE_CONJUNCTIONS);
					} else {
						/*
						 * the best approximation for the negation of a weak equivalence that we can express is a
						 * disequality on the arrays. i.e. not ( a -- i -- b ) ~~> a != b However, here we need to
						 * negate a -- i -- b /\ a[i] = x, thus we would need to return two EqConstraints --> TODO
						 * postponing this, overapproximating to "true"..
						 */
						newConstraint = mEqConstraintFactory.getEmptyConstraint(INPLACE_CONJUNCTIONS);
					}
				}

				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(Collections.singleton(newConstraint)));
				return;
			}
			if (!isElementTracked(arg1) || !isElementTracked(arg2)) {
				// we don't track both sides of the equation --> return an empty constraint
				mResultStack.push(mEqConstraintFactory.getEmptyDisjunctiveConstraint(INPLACE_CONJUNCTIONS));
				return;
			}

			final EqNode node1 = mEqNodeAndFunctionFactory.getOrConstructNode(arg1);
			final EqNode node2 = mEqNodeAndFunctionFactory.getOrConstructNode(arg2);

			final EqConstraint<EqNode> newConstraint;
			if (polarity) {
				newConstraint = mEqConstraintFactory.addEquality(node1, node2,
						mEqConstraintFactory.getEmptyConstraint(INPLACE_CONJUNCTIONS), INPLACE_CONJUNCTIONS);
			} else {
				newConstraint = mEqConstraintFactory.addDisequality(node1, node2,
						mEqConstraintFactory.getEmptyConstraint(INPLACE_CONJUNCTIONS), INPLACE_CONJUNCTIONS);
			}
			mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(Collections.singleton(newConstraint)));
			return;
		}

		private boolean isElementTracked(final Term term) {
			// TODO: implement something smart here, or get rid of this method
			return true;
			// return mPreAnalysis.isElementTracked(term, mTf);
		}

		private boolean isFunctionTracked(final Term term) {
			// TODO: implement something smart here, or get rid of this method
			return true;
			// return mPreAnalysis.isArrayTracked(term, mTf.getInVars(), mTf.getOutVars());
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			assert false : "TODO unlet first (or implement let handling..)";
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			throw new UnsupportedOperationException(
					"quantifiers in Transformulas are currently not supported in the" + " equality domain");
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			if ("Bool".equals(term.getSort().getName())) {
				handleBooleanTerm(term, true);
				return;
			}
			throw new AssertionError("we should have caught this before, right?");
		}
	}

	class MakeDisjunctionWalker implements Walker {
		/**
		 * arity of the disjunction (i.e. how many elements to pop from result stack
		 */
		private final int mArity;

		public MakeDisjunctionWalker(final int arity) {
			mArity = arity;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final Set<EqConstraint<EqNode>> allConjunctiveConstraints = new HashSet<>();
			for (int i = 0; i < mArity; i++) {
				allConjunctiveConstraints.addAll(mResultStack.pop().getConstraints());
			}
			mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(allConjunctiveConstraints));
		}
	}

	class MakeConjunctionWalker implements Walker {
		/**
		 * arity of the disjunction (i.e. how many elements to pop from result stack
		 */
		private final int mArity;

		public MakeConjunctionWalker(final int arity) {
			mArity = arity;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ArrayList<EqDisjunctiveConstraint<EqNode>> conjuncts = new ArrayList<>();
			for (int i = 0; i < mArity; i++) {
				conjuncts.add(mResultStack.pop());
			}
			mResultStack.push(mEqConstraintFactory.conjoinDisjunctiveConstraints(conjuncts));
		}
	}

	/**
	 * Transforms a given Term into an equivalent term where every atom contains at most one application of the store
	 * function. (Multidimensional store terms count as one application.)
	 *
	 * Right now the result is not equivalent. However it is equivalent to the original when conjoined with the
	 * equalities from getReplacementEquations, and the replacement variables are existentially quantified.
	 *
	 * removes the following from the formula
	 * <ul>
	 * <li>store chains, i.e., every (store s i x) where s is another store term is eliminated
	 * <li>multidimensional stores, explicit or not, i.e., every (store s i x) where x is another store term is
	 * eliminated
	 * <li>stores on both sides of an equality, for example the term (= (store a i x) (store b j y)) would be
	 * transformed such that it contains at most one store
	 * <li>stores inside selects, for example (select (store a i x) j) would be transformed
	 * </ul>
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	public static final class StoreChainSquisher extends TermTransformer {

		private static final String SQUISHERREPARRAYNAME = "rep";

		private final List<Term> mReplacementEquations;

		private final Map<Term, TermVariable> mReplacedTermToReplacementTv;

		private final Script mScript;

		private final ManagedScript mMgdScript;

		public StoreChainSquisher(final ManagedScript mgdScript) {
			mScript = mgdScript.getScript();
			mMgdScript = mgdScript;
			mReplacementEquations = new ArrayList<>();
			mReplacedTermToReplacementTv = new BidirectionalMap<>();
		}

		public Collection<Term> getReplacementEquations() {
			final Collection<Term> result = new ArrayList<>();
			for (final Entry<Term, TermVariable> en : mReplacedTermToReplacementTv.entrySet()) {
				final Term replacementEquation = SmtUtils.binaryEquality(mScript, en.getValue(), en.getKey());
				result.add(replacementEquation);
			}
			return result;
		}

		public Collection<Term> getReplacementTermVariables() {
			return new ArrayList<>(mReplacedTermToReplacementTv.values());
		}

		@Override
		protected void convert(final Term term) {
			if (SmtUtils.isFunctionApplication(term, "store")) {
				enqueueWalker(new SquishStoreWalker((ApplicationTerm) term));
				pushTerms(((ApplicationTerm) term).getParameters());
			} else if (SmtUtils.isFunctionApplication(term, "select")) {
				enqueueWalker(new SquishStoreInsideSelectWalker());
				pushTerms(((ApplicationTerm) term).getParameters());
			} else if (SmtUtils.isFunctionApplication(term, "=")
					&& SmtUtils.isFunctionApplication(((ApplicationTerm) term).getParameters()[0], "store")
					&& SmtUtils.isFunctionApplication(((ApplicationTerm) term).getParameters()[1], "store")) {
				enqueueWalker(new SquishFirstOfTwoArgumentStoresWalker((ApplicationTerm) term));
				assert ((ApplicationTerm) term).getParameters().length == 2;
				pushTerms(((ApplicationTerm) term).getParameters());
			} else {
				super.convert(term);
			}
		}

		/**
		 * Obtains the replacement TermVariable for the given term.
		 *
		 * If the same term has been replaced before, the same variable is returned.
		 *
		 * The map that is used to manage the replacement variables will also be used to return the of equations between
		 * the replacement variables and their corresponding terms.
		 *
		 * @param term
		 * @return
		 */
		private TermVariable getReplacementTv(final Term term) {
			TermVariable res = mReplacedTermToReplacementTv.get(term);
			if (res == null) {
				/*
				 * note: it is important for untracked array business (see EqNode) that the name of the term is part of
				 * the name of the replacement term
				 */
				final String name =
						SmtUtils.sanitizeStringAsSmtIdentifier(SQUISHERREPARRAYNAME + "_" + term.toString());
				res = mMgdScript.constructFreshTermVariable(name, term.getSort());
				mReplacedTermToReplacementTv.put(term, res);
			}
			return res;
		}

		/**
		 * only used to make getConverted visible to the walker.
		 *
		 * @param oldArgs
		 * @return
		 */
		Term[] getConvertedArray(final Term[] oldArgs) {
			return getConverted(oldArgs);
		}

		class SquishFirstOfTwoArgumentStoresWalker implements Walker {

			private final ApplicationTerm mAppTerm;

			public SquishFirstOfTwoArgumentStoresWalker(final ApplicationTerm term) {
				mAppTerm = term;
				assert term.getParameters().length == 2;
			}

			@Override
			public void walk(final NonRecursive engine) {

				final Term arg2 = getConverted();
				final Term arg1 = getConverted();
				assert SmtUtils.isFunctionApplication(arg1, "store");
				assert SmtUtils.isFunctionApplication(arg2, "store");

				final Term innerStoreTerm = arg1;
				final TermVariable replacmentTv = getReplacementTv(innerStoreTerm);
				setResult(mScript.term(mAppTerm.getFunction().getName(), replacmentTv, arg2));
			}

		}

		/**
		 * removes stores inside selects
		 */
		class SquishStoreInsideSelectWalker implements Walker {

			@Override
			public void walk(final NonRecursive engine) {

				final Term arg2 = getConverted();
				final Term arg1 = getConverted();

				if (SmtUtils.isFunctionApplication(arg1, "store")) {
					final Term innerStoreTerm = arg1;
					final TermVariable replacmentTv = getReplacementTv(innerStoreTerm);
					setResult(mScript.term("select", replacmentTv, arg2));
				} else {
					setResult(mScript.term("select", arg1, arg2));
				}
			}

		}

		/**
		 * removes store chains
		 */
		class SquishStoreWalker implements Walker {

			private static final int NO_STORE_ARGS = 3;

			/** the application term to convert. */
			private final ApplicationTerm mAppTerm;

			public SquishStoreWalker(final ApplicationTerm term) {
				mAppTerm = term;
			}

			@Override
			public void walk(final NonRecursive engine) {
				final StoreChainSquisher transformer = (StoreChainSquisher) engine;
				/* collect args and check if they have been changed */
				final Term[] oldArgs = mAppTerm.getParameters();
				final Term[] newArgs = transformer.getConvertedArray(oldArgs);
				assert newArgs.length == NO_STORE_ARGS;

				final Term replacedArray;
				if (SmtUtils.isFunctionApplication(newArgs[0], "store")) {
					replacedArray = getReplacementTv(newArgs[0]);
				} else {
					replacedArray = newArgs[0];
				}

				final Term replacedValue;
				if (SmtUtils.isFunctionApplication(newArgs[2], "store")) {
					replacedValue = getReplacementTv(newArgs[2]);
				} else {
					replacedValue = newArgs[2];
				}

				setResult(mScript.term("store", replacedArray, newArgs[1], replacedValue));
			}

			@Override
			public String toString() {
				return "StoreTermSquisher: " + mReplacementEquations;
			}

		}
	}
}
