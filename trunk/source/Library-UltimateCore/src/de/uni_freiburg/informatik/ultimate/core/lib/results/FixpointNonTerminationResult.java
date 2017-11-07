/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;

/**
 * Repeating program execution.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <P>
 *            program position class
 */
public class FixpointNonTerminationResult<P extends IElement, E> extends LassoShapedNonTerminationArgument<P, E> {

	private final Map<E, E> mStateInit;
	private final Map<E, E> mStateHonda;

	public FixpointNonTerminationResult(final P position, final String plugin, final Map<E, E> stateInit,
			final Map<E, E> stateHonda, final IBacktranslationService translatorSequence, final Class<E> exprClazz, 
			final IProgramExecution<P, E> stem, final IProgramExecution<P, E> loop) {
		super(position, plugin, translatorSequence, exprClazz, stem, loop);
		mStateInit = stateInit;
		mStateHonda = stateHonda;
	}

	@Override
	public String getShortDescription() {
		return "Nontermination argument in form of an infinite " + "program execution.";
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Nontermination argument in form of an infinite execution\n");

		// State 1 (before the honda)
		sb.append("State at position 0 is\n");
		sb.append(printState2(mStateInit));

		// State 2 (at the honda)
		sb.append("\nState at position 1 is\n");
		sb.append(printState2(mStateHonda));
		return sb.toString();
	}

}
