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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqTransitionRelation;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 */
public class ConvertTransformulaToEqTransitionRelation<ACTION extends IIcfgTransition<IcfgLocation>>
		extends NonRecursive {

	private final TransFormula mTf;
	private EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> mResultConstraint;

	private final EqConstraintFactory<ACTION, EqNode, EqFunction> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;

	private final VPDomainPreanalysis mPreAnalysis;

	/**
	 * stores intermediate results of the "recursion"
	 */
	private final ArrayDeque<EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>> mResultStack = new ArrayDeque<>();

	public ConvertTransformulaToEqTransitionRelation(final TransFormula tf,
			final EqConstraintFactory<ACTION, EqNode, EqFunction> eqConstraintFactory,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory, final VPDomainPreanalysis preAnalysis) {
		mTf = tf;
		mEqConstraintFactory = eqConstraintFactory;
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;

		mPreAnalysis = preAnalysis;
		mMgdScript = preAnalysis.getManagedScript();
		mServices = preAnalysis.getServices();

		computeResult();
	}

	private void computeResult() {
		final Term transFormulaInNnf =
				new NnfTransformer(mMgdScript, mServices, QuantifierHandling.CRASH).transform(mTf.getFormula());

		final StoreChainSquisher scs = new StoreChainSquisher();
		final List<Term> conjunction = new ArrayList<>();
		conjunction.add(scs.transform(transFormulaInNnf));
		conjunction.addAll(scs.getReplacementEquations());
		final Term transFormulaWithSquishedStoreChains = SmtUtils.and(mMgdScript.getScript(), conjunction);
		run(new ConvertTfToEqDisjConsWalker(transFormulaWithSquishedStoreChains));
		assert mResultStack.size() == 1;
		final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> processedTf = mResultStack.pop();
		mResultConstraint = processedTf.projectExistentially(scs.getReplacementTermVariables());
	}

	public EqTransitionRelation<ACTION> getResult() {
		assert mResultConstraint != null;
		return new EqTransitionRelation<>(mResultConstraint, mTf);
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
							&& term.getParameters()[0] instanceof ApplicationTerm
							&& "=".equals(((ApplicationTerm) term.getParameters()[0]).getFunction().getName())) {
				final ApplicationTerm innerEqualsTerm = (ApplicationTerm) term.getParameters()[0];
				handleXquality(innerEqualsTerm.getParameters()[0], innerEqualsTerm.getParameters()[1], false);
			} else if ("not".equals(term.getFunction().getName())
							&& term.getParameters()[0] instanceof TermVariable) {
				handleBooleanVariable((TermVariable) term.getParameters()[0], false);
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
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(
						Collections.emptySet()));
			} else if ("true".equals(term.getFunction().getName())) {
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(
						Collections.singleton(mEqConstraintFactory.getEmptyConstraint())));
			} else {
				// we don't recognize this function symbol -- overapproximating its effects by "top"
				// TODO: perhaps we could make some checks here if it is trivially bottom or something like that..
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(
						Collections.singleton(mEqConstraintFactory.getEmptyConstraint())));
			}

		}

		private void handleBooleanVariable(final TermVariable termVariable, final boolean polarity) {
			assert "Bool".equals(termVariable.getSort().getName());
			final EqConstraint<ACTION, EqNode, EqFunction> emptyConstraint =
					mEqConstraintFactory.getEmptyConstraint();
			final EqNode tvNode = mEqNodeAndFunctionFactory.getOrConstructNode(termVariable);
			if (polarity) {
				mMgdScript.lock(this);
				final EqNode trueNode = mEqNodeAndFunctionFactory.getOrConstructNode(mMgdScript.term(this, "true"));
				mMgdScript.unlock(this);
				final EqConstraint<ACTION, EqNode, EqFunction> tvEqualsTrue =
						mEqConstraintFactory.addEqualityFlat(tvNode, trueNode, emptyConstraint);
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(
						Collections.singleton(tvEqualsTrue)));
			} else {
				mMgdScript.lock(this);
				final EqNode falseNode = mEqNodeAndFunctionFactory.getOrConstructNode(mMgdScript.term(this, "false"));
				mMgdScript.unlock(this);
				final EqConstraint<ACTION, EqNode, EqFunction> tvEqualsTrue =
						mEqConstraintFactory.addEqualityFlat(tvNode, falseNode, emptyConstraint);
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(
						Collections.singleton(tvEqualsTrue)));
			}
		}

		private void handleXquality(final Term arg1, final Term arg2, final boolean polarity) {

			final EqConstraint<ACTION, EqNode, EqFunction> emptyConstraint =
					mEqConstraintFactory.getEmptyConstraint();
			final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> emptyDisjunctiveConstraint =
					mEqConstraintFactory.getDisjunctiveConstraint(Collections.singleton(emptyConstraint));

			if (arg1.getSort().isArraySort()) {
				// we have an array equality

				if (!isFunctionTracked(arg1) || !isFunctionTracked(arg2)) {
					// we don't track both sides of the equation --> return an empty constraint
					mResultStack.push(emptyDisjunctiveConstraint);
					return;
				}

				MultiDimensionalStore mds;
				EqFunction simpleArray;
				EqFunction otherSimpleArray;

				if (SmtUtils.isFunctionApplication(arg1, "store")) {
					assert !SmtUtils.isFunctionApplication(arg2, "store");
					mds = new MultiDimensionalStore(arg1);
					simpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(arg2);
					assert !SmtUtils.isFunctionApplication(mds.getArray(), "store");
					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(mds.getArray());
				} else if (SmtUtils.isFunctionApplication(arg2, "store")) {
					assert !SmtUtils.isFunctionApplication(arg1, "store");
					mds = new MultiDimensionalStore(arg2);
					simpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(arg1);
					assert !SmtUtils.isFunctionApplication(mds.getArray(), "store");
					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(mds.getArray());
				} else {
					mds = null;
					simpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(arg1);
					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(arg2);
				}



				final EqConstraint<ACTION, EqNode, EqFunction> newConstraint;
				if (polarity) {
					if (mds == null) {
						// we have a strong equivalence
						newConstraint = mEqConstraintFactory.addFunctionEqualityFlat(simpleArray,
								otherSimpleArray, emptyConstraint);
					} else {

						final List<EqNode> storeIndex = mds.getIndex().stream()
								.map(mEqNodeAndFunctionFactory::getOrConstructNode)
								.collect(Collectors.toList());
						final EqNode storeValue = mEqNodeAndFunctionFactory.getOrConstructNode(mds.getValue());

						// we have a weak equivalence ..
						final EqConstraint<ACTION, EqNode, EqFunction> intermediateConstraint =
								mEqConstraintFactory.addWeakEquivalence(simpleArray, otherSimpleArray, storeIndex,
										emptyConstraint);
						// .. and an equality on the stored position
						final Term selectTerm = SmtUtils.multiDimensionalSelect(mMgdScript.getScript(),
								simpleArray.getTerm(), mds.getIndex());
						final EqNode selectEqNode = mEqNodeAndFunctionFactory.getOrConstructNode(selectTerm);
						newConstraint = mEqConstraintFactory.addEqualityFlat(selectEqNode, storeValue,
								intermediateConstraint);
					}
				} else {
					if (mds == null) {
						newConstraint = mEqConstraintFactory.addFunctionDisequalityFlat(simpleArray,
								otherSimpleArray, emptyConstraint);
					} else {
						assert false;
						// TODO do something here, or not?..
						newConstraint = emptyConstraint;
					}
				}

				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(Collections.singleton(newConstraint)));
				return;
			} else {
				// we have an "normal", element equality

				if (!isElementTracked(arg1) || !isElementTracked(arg2)) {
					// we don't track both sides of the equation --> return an empty constraint
					mResultStack.push(emptyDisjunctiveConstraint);
					return;
				}

				final EqNode node1 = mEqNodeAndFunctionFactory.getOrConstructNode(arg1);
				final EqNode node2 = mEqNodeAndFunctionFactory.getOrConstructNode(arg2);

				final EqConstraint<ACTION, EqNode, EqFunction> newConstraint;
				if (polarity) {
					newConstraint =
							mEqConstraintFactory.addEqualityFlat(node1, node2, emptyConstraint);
				} else {
					newConstraint =
							mEqConstraintFactory.addDisequalityFlat(node1, node2, emptyConstraint);
				}
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(Collections.singleton(newConstraint)));
				return;
			}
		}

		private boolean isElementTracked(final Term term) {
			return mPreAnalysis.isElementTracked(term, mTf);
		}

		private boolean isFunctionTracked(final Term term) {
			return mPreAnalysis.isArrayTracked(term, mTf.getInVars(), mTf.getOutVars());
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			assert false : "TODO unlet first (or implement let handling..)";
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			throw new UnsupportedOperationException("quantifiers in Transformulas are currently not supported in the"
					+ " equality domain");
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			if ("Bool".equals(term.getSort().getName())) {
				handleBooleanVariable(term, true);
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
			final Set<EqConstraint<ACTION, EqNode, EqFunction>> allConjunctiveConstraints = new HashSet<>();
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
			final ArrayList<EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>> conjuncts = new ArrayList<>();
			for (int i = 0; i < mArity; i++) {
				conjuncts.add(mResultStack.pop());
			}
			mResultStack.push(mEqConstraintFactory.conjoinDisjunctiveConstraints(conjuncts));
		}
	}

	/**
	 * Transforms a given Term into an equivalent term where every atom contains at most one application of the store
	 * function.
	 * (Multidimensional store terms count as one application.)
	 *
	 * Right now the result is not equivalent. However it is equivalent to the original when conjoined with the
	 * equalities from getReplacementEquations.
	 *
	 * removes the following from the formula
	 * <ul>
	 *  <li> store chains, i.e., every (store s i x) where s is another store term is eliminated
	 *  <li> stores on both sides of an equality, for example the term (= (store a i x) (store b j y)) would be
	 *     transformed such that it contains at most one store
	 *  <li> stores inside selects, for example (select (store a i x) j) would be transformed
	 * </ul>
	 *
	 * TODO polish -- could be done nicer, probably
	 * TODO cannot yet eliminate equations that have a store term on both sides
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	class StoreChainSquisher extends TermTransformer {

		Script mScript = mMgdScript.getScript();

		private final List<Term> mReplacementEquations = new ArrayList<>();

		private final List<TermVariable> mReplacementTermVariables = new ArrayList<>();


		public List<Term> getReplacementEquations() {
			return mReplacementEquations;
		}

		public List<TermVariable> getReplacementTermVariables() {
			return mReplacementTermVariables;
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

		private TermVariable getReplacementTv(final Sort sort) {
			final TermVariable res = mMgdScript.constructFreshTermVariable("rep", sort);
			mReplacementTermVariables.add(res);
			return res;
		}

		private void addReplacementEquation(final Term replacementEquation) {
			mReplacementEquations.add(replacementEquation);
		}

		/**
		 * only used to make getConverted visible to the walker.
		 *
		 * @param oldArgs
		 * @return
		 */
		Term[] myGetConverted(final Term[] oldArgs) {
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
				final TermVariable replacmentTv = getReplacementTv(innerStoreTerm.getSort());
				final Term replacementEquation = SmtUtils.binaryEquality(mScript, replacmentTv, innerStoreTerm);
				addReplacementEquation(replacementEquation);
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
					final TermVariable replacmentTv = getReplacementTv(innerStoreTerm.getSort());
					final Term replacementEquation = SmtUtils.binaryEquality(mScript, replacmentTv, innerStoreTerm);
					addReplacementEquation(replacementEquation);
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
				final Term[] newArgs = transformer.myGetConverted(oldArgs);
				assert newArgs.length == 3;
				if (SmtUtils.isFunctionApplication(newArgs[0], "store")) {
					final Term innerStoreTerm = newArgs[0];
					final TermVariable replacmentTv = getReplacementTv(innerStoreTerm.getSort());
					final Term replacementEquation = SmtUtils.binaryEquality(mScript, replacmentTv, innerStoreTerm);
					addReplacementEquation(replacementEquation);
					setResult(mScript.term("store", replacmentTv, newArgs[1], newArgs[2]));
				} else {
					// the array argument of the store that we enqueued this walker for is a variable
					// --> we do no further transformation
					setResult(mScript.term("store", newArgs[0], newArgs[1], newArgs[2]));
				}
			}



			@Override
			public String toString() {
				return "StoreTermSquisher: " + mReplacementEquations;
			}

		}


	}
}
