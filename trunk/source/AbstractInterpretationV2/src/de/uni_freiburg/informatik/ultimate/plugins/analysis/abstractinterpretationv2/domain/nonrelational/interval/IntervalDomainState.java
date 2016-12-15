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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState;

/**
 * Implementation of an abstract state of the {@link IntervalDomain}.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomainState extends NonrelationalState<IntervalDomainState, IntervalDomainValue> {
	
	/**
	 * Default constructor of an {@link IntervalDomainState}.
	 *
	 * @param logger
	 *            The current logger object in the current context.
	 */
	protected IntervalDomainState(final ILogger logger) {
		super(logger);
	}
	
	/**
	 * Constructor of an {@link IntervalDomainState} that is either &bot;, or &top;.
	 *
	 * @param logger
	 *            The current logger object in the current context.
	 * @param isBottom
	 *            If <code>true</code>, the created state corresponds to &bot;, &top; otherwise.
	 */
	protected IntervalDomainState(final ILogger logger, final boolean isBottom) {
		super(logger, isBottom);
	}

	/**
	 * Creates a new instance of {@link IntervalDomainState} with given logger, variables map, values map and boolean
	 * values map.
	 *
	 * @param logger
	 *            The current logger object in the current context.
	 * @param variablesMap
	 *            The map with all variable identifiers and their types.
	 * @param valuesMap
	 *            The values of all variables.
	 * @param booleanValuesMap
	 *            The values of all boolean variables.
	 */
	protected IntervalDomainState(final ILogger logger, final Set<IBoogieVar> variablesMap,
			final Map<IBoogieVar, IntervalDomainValue> valuesMap,
			final Map<IBoogieVar, BooleanValue> booleanValuesMap) {
		super(logger, variablesMap, valuesMap, booleanValuesMap);
	}

	@Override
	protected IntervalDomainState createCopy() {
		return new IntervalDomainState(getLogger(), getVariables(), new HashMap<>(getVar2ValueNonrelational()),
				new HashMap<>(getVar2ValueBoolean()));
	}

	@Override
	protected IntervalDomainState createState(final ILogger logger, final Set<IBoogieVar> newVarMap,
			final Map<IBoogieVar, IntervalDomainValue> newValMap,
			final Map<IBoogieVar, BooleanValue> newBooleanValMap) {
		return new IntervalDomainState(logger, newVarMap, newValMap, newBooleanValMap);
	}

	@Override
	protected IntervalDomainValue createBottomValue() {
		return new IntervalDomainValue(true);
	}

	@Override
	protected IntervalDomainValue createTopValue() {
		return new IntervalDomainValue(false);
	}

	@Override
	protected IntervalDomainValue[] getArray(final int size) {
		return new IntervalDomainValue[size];
	}
}
