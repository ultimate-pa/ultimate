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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.TVBool;

/**
 * Implementation of an abstract state of the {@link CongruenceDomain}.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class CongruenceDomainState extends NonrelationalState<CongruenceDomainState, CongruenceDomainValue> {

	/**
	 * Default constructor of an {@link CongruenceDomainState}.
	 *
	 * @param logger
	 *            The current logger object in the current context.
	 * @param isBottom
	 *            If <code>true</code> the created state corresponds to &bot;, &top; otherwise.
	 */
	protected CongruenceDomainState(final ILogger logger, final boolean isBottom) {
		super(logger, isBottom);
	}

	/**
	 * Creates a new instance of {@link CongruenceDomainState} with given logger, variables map, values map and boolean
	 * values map. The created state is either &bot; or &top;.
	 *
	 * @param logger
	 *            The current logger object in the current context.
	 * @param variablesMap
	 *            The map with all variable identifiers and their types.
	 * @param valuesMap
	 *            The values of all variables.
	 * @param booleanValuesMap
	 *            The values of all boolean variables.
	 * @param isBottom
	 *            If <code>true</code>, the created state is &bot;, &top; otherwise.
	 */
	protected CongruenceDomainState(final ILogger logger, final Set<IProgramVarOrConst> variablesMap,
			final Map<IProgramVarOrConst, CongruenceDomainValue> valuesMap,
			final Map<IProgramVarOrConst, BooleanValue> booleanValuesMap, final boolean isBottom) {
		super(logger, variablesMap, valuesMap, booleanValuesMap, isBottom);
	}

	protected CongruenceDomainState(final ILogger logger, final Set<IProgramVarOrConst> variablesMap,
			final Map<IProgramVarOrConst, CongruenceDomainValue> valuesMap,
			final Map<IProgramVarOrConst, BooleanValue> booleanValuesMap, final TVBool isBottom) {
		super(logger, variablesMap, valuesMap, booleanValuesMap, isBottom);
	}

	@Override
	protected CongruenceDomainState createCopy() {
		return new CongruenceDomainState(getLogger(), getVariables(), getVar2ValueNonrelational(),
				getVar2ValueBoolean(), getBottomFlag());
	}

	@Override
	protected CongruenceDomainState createState(final ILogger logger, final Set<IProgramVarOrConst> newVarMap,
			final Map<IProgramVarOrConst, CongruenceDomainValue> newValMap,
			final Map<IProgramVarOrConst, BooleanValue> newBooleanValMap, final boolean isBottom) {
		return new CongruenceDomainState(logger, newVarMap, newValMap, newBooleanValMap, isBottom);
	}

	@Override
	protected CongruenceDomainValue createBottomValue() {
		return CongruenceDomainValue.createBottom();
	}

	@Override
	protected CongruenceDomainValue createTopValue() {
		return CongruenceDomainValue.createTop();
	}

	@Override
	protected CongruenceDomainValue[] getArray(final int size) {
		return new CongruenceDomainValue[size];
	}

	@Override
	protected CongruenceDomainState getThis() {
		return this;
	}
}
