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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.interval;

import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.NonrelationalTermProcessor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator.ITermEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator.TermEvaluatorFactory;

/**
 * Term processor for the interval abstract domain.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomainTermProcessor extends NonrelationalTermProcessor<IntervalDomainValue, IntervalDomainState> {

	private INonrelationalValueFactory<IntervalDomainValue> mIntervalValueFactory;

	public IntervalDomainTermProcessor(final ILogger logger, final int maxParallelStates,
			final Supplier<IntervalDomainState> bottomStateSupplier) {
		super(logger, maxParallelStates, bottomStateSupplier);
	}

	@Override
	protected INonrelationalValueFactory<IntervalDomainValue> getNonrelationalValueFactory() {
		if (mIntervalValueFactory == null) {
			mIntervalValueFactory = new IntervalValueFactory();
		}
		return mIntervalValueFactory;
	}

	@Override
	protected ITermEvaluatorFactory<IntervalDomainValue, IntervalDomainState>
			createEvaluatorFactory(final int maxParallelStates) {
		final TermEvaluatorFactory.Function<Object, IntervalDomainValue> valueEvaluatorCreator =
				(value) -> new IntervalDomainValue(new IntervalValue(value.toString()),
						new IntervalValue(value.toString()));
		return new TermEvaluatorFactory<>(mLogger, maxParallelStates, valueEvaluatorCreator, mIntervalValueFactory);
	}
}
