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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model;

import java.util.Map;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 *            Any action type.
 * @param <VARDECL>
 *            Any variable declaration type.
 */
public interface IAbstractState<ACTION, VARDECL> {

	IAbstractState<ACTION, VARDECL> addVariable(String name, VARDECL variables);

	IAbstractState<ACTION, VARDECL> removeVariable(String name, VARDECL variables);

	IAbstractState<ACTION, VARDECL> addVariables(Map<String, VARDECL> variables);

	IAbstractState<ACTION, VARDECL> removeVariables(Map<String, VARDECL> variables);

	boolean containsVariable(String name);

	/**
	 * An abstract state is empty when it does not contain any variable.
	 * 
	 * @return true iff this abstract state is empty
	 */
	boolean isEmpty();

	boolean isBottom();

	boolean isFixpoint();

	IAbstractState<ACTION, VARDECL> setFixpoint(boolean value);

	String toLogString();

	boolean isEqualTo(IAbstractState<ACTION, VARDECL> other);

	IAbstractState<ACTION, VARDECL> copy();
}
