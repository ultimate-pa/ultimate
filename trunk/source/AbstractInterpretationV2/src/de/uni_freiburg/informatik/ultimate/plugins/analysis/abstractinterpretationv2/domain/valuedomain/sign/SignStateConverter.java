/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.sign;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;

/**
 * Checks whether a given IAbstractState is a state of the SignDomain.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 *            Any action.
 * @param <VARDECL>
 *            Any variable declaration.
 */
public class SignStateConverter<ACTION, VARDECL> {
	private final Class<SignDomainState<ACTION, VARDECL>> mStateType;

	@SuppressWarnings("unchecked")
	protected SignStateConverter(SignDomainState<ACTION, VARDECL> sampleState) {
		mStateType = (Class<SignDomainState<ACTION, VARDECL>>) sampleState.getClass();
	}

	/**
	 * Throws an exception if the given state cannot be converted into a SignDomainState.
	 * 
	 * @param state
	 *            The state to be converted into a SignDomainState.
	 * @return Returns the given IAbstractState converted to a SignDomainState.
	 */
	protected SignDomainState<ACTION, VARDECL> getCheckedState(IAbstractState<ACTION, VARDECL> state) {
		if (!(mStateType.isInstance(state))) {
			throw new IllegalArgumentException("SignDomain can only process SignDomainState types as abstract states.");
		}
		return (SignDomainState<ACTION, VARDECL>) state;
	}
	
	protected Class<SignDomainState<ACTION, VARDECL>> getAbstractStateClass() {
		return mStateType;
	}
}
