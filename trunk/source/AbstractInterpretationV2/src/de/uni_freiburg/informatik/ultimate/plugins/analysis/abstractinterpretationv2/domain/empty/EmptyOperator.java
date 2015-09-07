/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <ACTION>
 * @param <VARDECL>
 */
public final class EmptyOperator<ACTION, VARDECL> implements IAbstractStateBinaryOperator<ACTION, VARDECL> {

	private EmptyStateConverter<ACTION, VARDECL> mStateConverter;

	protected EmptyOperator(EmptyStateConverter<ACTION, VARDECL> stateConverter) {
		mStateConverter = stateConverter;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> apply(IAbstractState<ACTION, VARDECL> first,
			IAbstractState<ACTION, VARDECL> second) {
		assert first != null;
		assert second != null;
		final EmptyDomainState<ACTION, VARDECL> firstState = mStateConverter.getCheckedState(first);
		final EmptyDomainState<ACTION, VARDECL> secondState = mStateConverter.getCheckedState(second);

		if (!firstState.hasSameVariables(secondState)) {
			throw new UnsupportedOperationException("Cannot widen or merge two states with different variables");
		}

		return new EmptyDomainState<>(firstState.getVariables(), firstState.isFixpoint() || secondState.isFixpoint());
	}
}
