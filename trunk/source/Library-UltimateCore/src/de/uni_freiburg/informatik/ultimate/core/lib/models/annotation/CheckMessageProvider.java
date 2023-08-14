/*
 * Copyright (C) 2023 Manuel Bentele
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.EnumSet;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.ISpec;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.ISpec.Type.Group;

/**
 * Message provider for {@link Group.PROGRAM} labeled specifications that are checked.
 * 
 * @author Manuel Bentele
 */
public class CheckMessageProvider extends MessageProvider {

	/**
	 * Creates a message provider for {@link Group.GENERIC} and {@link Group.PROGRAM} labeled specifications.
	 */
	public CheckMessageProvider() {
		super(EnumSet.of(Group.GENERIC, Group.PROGRAM));
	}

	/**
	 * Overwrite message for error function specifications ({@link ISpec.Type.ERROR_FUNCTION}).
	 * 
	 * @param functionName
	 *            name of the error function.
	 */
	public void registerSpecificationErrorFunctionName(final String functionName) {

		if (functionName != null && !functionName.isEmpty()) {
			registerPositiveMessageOverride(ISpec.Type.ERROR_FUNCTION,
					() -> String.format("a call to %s is unreachable", functionName));
			registerNegativeMessageOverride(ISpec.Type.ERROR_FUNCTION,
					() -> String.format("a call to %s is reachable", functionName));
		}
	}

	/**
	 * Overwrite message for specification ({@link ISpec.Type}) with given error message.
	 * 
	 * @param spec
	 *            specification type whose message should be overwritten.
	 * @param errorMsg
	 *            message describing the violation of the {@code spec}.
	 */
	public void registerSpecificationErrorMessage(final ISpec.Type spec, final String errorMsg) {

		if (errorMsg != null && !errorMsg.isEmpty()) {
			registerNegativeMessageOverride(spec,
					() -> String.format("%s: %s", getDefaultNegativeMessage(spec), errorMsg));
		}
	}

	/**
	 * Overwrite message for assertion specifications ({@link ISpec.Type.ASSERT}) with named attributes.
	 * 
	 * @param namedAttributes
	 *            description of the named attributes.
	 */
	public void registerSpecificationAssertNamedAttributes(final String namedAttributes) {

		if (namedAttributes != null && !namedAttributes.isEmpty()) {
			registerPositiveMessageOverride(ISpec.Type.ASSERT,
					() -> String.format("assertion with attributes \"%s\" always holds", namedAttributes));
			registerNegativeMessageOverride(ISpec.Type.ASSERT,
					() -> String.format("assertion with attributes \"%s\" can be violated", namedAttributes));
		}
	}
}
