/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator.ITermEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator.ITermEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator.TermExpressionEvaluator;

/**
 * Term walker for non-relational abstract domains.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public abstract class NonrelationalTermProcessor<VALUE extends INonrelationalValue<VALUE>, STATE extends NonrelationalState<STATE, VALUE>>
		extends NonRecursive {

	protected final ILogger mLogger;
	private final ITermEvaluatorFactory<VALUE, STATE> mEvaluatorFactory;
	private final Supplier<STATE> mBottomStateSupplier;

	private TermExpressionEvaluator<VALUE, STATE> mExpressionEvaluator;

	public NonrelationalTermProcessor(final ILogger logger, final int maxParallelStates,
			final Supplier<STATE> bottomStateSupplier) {
		mLogger = logger;
		mEvaluatorFactory = createEvaluatorFactory(maxParallelStates);
		mBottomStateSupplier = bottomStateSupplier;
	}

	protected abstract ITermEvaluatorFactory<VALUE, STATE> createEvaluatorFactory(int maxParallelStates);

	protected abstract INonrelationalValueFactory<VALUE> getNonrelationalValueFactory();

	protected List<STATE> process(final Term term, final STATE oldState) {
		mLogger.debug("Term processor is analyzing term: " + term);

		mExpressionEvaluator = new TermExpressionEvaluator<>();
		run(new NonrelationalTermWalker(term, mLogger));

		if (!mExpressionEvaluator.isFinished()) {
			throw new IllegalStateException("Invalid state: the expression evaluator is not finished.");
		}
		final List<IEvaluationResult<VALUE>> result = mExpressionEvaluator.getRootEvaluator().evaluate(oldState);
		assert result != null;

		final List<STATE> returnStates = new ArrayList<>();
		for (final IEvaluationResult<VALUE> res : result) {
			returnStates.addAll(mExpressionEvaluator.getRootEvaluator().inverseEvaluate(res, oldState));
		}

		return returnStates;
	}

	private final class NonrelationalTermWalker extends TermWalker {

		private final ILogger mLogger;

		public NonrelationalTermWalker(final Term term, final ILogger logger) {
			super(term);
			mLogger = logger;
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			mLogger.debug("Constant Term: " + term);
			mLogger.debug("Type of value: " + term.getValue().getClass().getSimpleName());
			final ITermEvaluator<VALUE, STATE> constantEvaluator =
					mEvaluatorFactory.createConstantValueEvaluator(term.getValue());

			mExpressionEvaluator.addEvaluator(constantEvaluator);
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			mLogger.debug("Annotated Term: " + term);
			throw new UnsupportedOperationException("Not implemented!");
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			mLogger.debug("Application Term: " + term);

			final String fName = term.getFunction().getName();

			final ITermEvaluator<VALUE, STATE> applicationTerm = mEvaluatorFactory.createApplicationTerm(
					term.getParameters().length, fName, getNonrelationalValueFactory(), mBottomStateSupplier);
			mExpressionEvaluator.addEvaluator(applicationTerm);

			for (final Term t : term.getParameters()) {
				run(new NonrelationalTermWalker(t, mLogger));
			}
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			mLogger.debug("Let Term: " + term);
			throw new UnsupportedOperationException("Not implemented!");
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			mLogger.debug("Quantified Formula: " + term);
			throw new UnsupportedOperationException("Not implemented!");
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			mLogger.debug("Term Variable: " + term);

			final ITermEvaluator<VALUE, STATE> variableTermEvaluator =
					mEvaluatorFactory.createVariableTermEvaluator(term.getName(), term.getSort());

			mExpressionEvaluator.addEvaluator(variableTermEvaluator);
		}

		@Override
		public void walk(final NonRecursive walker, final MatchTerm term) {
			throw new UnsupportedOperationException("not yet implemented: MatchTerm");
		}
	}

}
