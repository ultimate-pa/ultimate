/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.livevariable;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

/**
 * Domain that computes live variables in conjunction with backwards analysis.
 *
 * @param <ACTION>
 *            the type of transition for which the domain should be used.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class LiveVariableDomain<ACTION extends IAction> implements IAbstractDomain<LiveVariableState<ACTION>, ACTION> {

	private final LiveVariablePreOperator<ACTION> mPre;
	private final IAbstractStateBinaryOperator<LiveVariableState<ACTION>> mMerge;

	/**
	 * Create the live variable domain.
	 *
	 * @param logger
	 *            A logger instance.
	 */
	public LiveVariableDomain(final ILogger logger) {
		mPre = new LiveVariablePreOperator<>();
		mMerge = (a, b) -> a.union(b);
	}

	@Override
	public LiveVariableState<ACTION> createTopState() {
		return new LiveVariableState<>();
	}

	@Override
	public LiveVariableState<ACTION> createBottomState() {
		throw new UnsupportedOperationException("createBottomState not implemented, yet.");
	}

	@Override
	public IAbstractStateBinaryOperator<LiveVariableState<ACTION>> getWideningOperator() {
		return mMerge;
	}

	@Override
	public IAbstractTransformer<LiveVariableState<ACTION>, ACTION> getPreOperator() {
		return mPre;
	}
}
