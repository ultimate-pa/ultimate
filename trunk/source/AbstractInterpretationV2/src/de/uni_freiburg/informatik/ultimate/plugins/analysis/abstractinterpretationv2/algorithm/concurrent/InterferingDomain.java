/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;

/**
 * Wrapper for an {@code IAbstractDomain} with a different post-operator to consider interferences
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class InterferingDomain<STATE extends IAbstractState<STATE>, ACTION, LOC>
		implements IAbstractDomain<STATE, ACTION> {
	private final IAbstractDomain<STATE, ACTION> mUnderlying;
	private final IAbstractPostOperator<STATE, ACTION> mInterferingPostOperator;

	public InterferingDomain(final IAbstractDomain<STATE, ACTION> underlying,
			final ITransitionProvider<ACTION, LOC> transitionProvider,
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		mUnderlying = underlying;
		mInterferingPostOperator =
				new InterferingPostOperator<>(transitionProvider, interferences, underlying.getPostOperator());
	}

	@Override
	public STATE createTopState() {
		return mUnderlying.createTopState();
	}

	@Override
	public STATE createBottomState() {
		return mUnderlying.createBottomState();
	}

	@Override
	public IAbstractStateBinaryOperator<STATE> getWideningOperator() {
		return mUnderlying.getWideningOperator();
	}

	@Override
	public void beforeFixpointComputation(final Object... objects) {
		mUnderlying.beforeFixpointComputation(objects);
	}

	@Override
	public IAbstractPostOperator<STATE, ACTION> getPostOperator() {
		return mInterferingPostOperator;
	}

	@Override
	public boolean isAbstractable(final Term term) {
		return mUnderlying.isAbstractable(null);
	}

	@Override
	public <LOC2> void afterFixpointComputation(final IAbstractInterpretationResult<STATE, ACTION, LOC2> result) {
		mUnderlying.afterFixpointComputation(result);
	}

	@Override
	public String domainDescription() {
		return mUnderlying.domainDescription() + " with interferences";
	}
}
