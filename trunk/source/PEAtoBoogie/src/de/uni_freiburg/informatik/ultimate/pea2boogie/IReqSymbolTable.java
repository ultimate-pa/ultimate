/*
 * Copyright (C) 2019-2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019-2020 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.AuxiliaryStatementContainer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public interface IReqSymbolTable {

	IdentifierExpression getIdentifierExpression(final String name);

	String getPcName(PhaseEventAutomata automaton);

	Set<String> getConstVars();

	Set<String> getPrimedVars();

	Set<String> getHistoryVars();

	Set<String> getEventVars();

	Set<String> getInputVars();

	Set<String> getOutputVars();

	String getDeltaVarName();

	VariableLHS getVariableLhs(String clockVar);

	Set<String> getClockVars();

	Set<String> getStateVars();

	// Allows you to easily add more elements to the Boogie program at any line without the need to create more
	// interface methods.
	Set<String> getAuxVars();

	AuxiliaryStatementContainer getAuxStatementContainer();

	/**
	 * Given a variable name, return the name of the primed version of this variable.
	 */
	String getPrimedVarId(String name);

	/**
	 * Given a variable name, return the name of the history version of this variable.
	 */
	String getHistoryVarId(String name);

	Set<String> getPcVars();

	Collection<Declaration> getDeclarations();

	Map<PatternType<?>, BoogieLocation> getLocations();

	Map<String, Expression> getConstToValue();

	IBoogieType getFunctionReturnType(String identifier);

	/**
	 * Get a {@link UnionFind} data structure that partitions all variables in the PEA product based on their usage,
	 * i.e., all variables of all PEAs that share (also transitively) one variable are in one class.
	 */
	UnionFind<String> getVariableEquivalenceClasses();
}
