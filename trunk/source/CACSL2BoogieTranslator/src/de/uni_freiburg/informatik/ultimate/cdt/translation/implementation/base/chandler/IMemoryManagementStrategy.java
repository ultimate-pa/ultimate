/*
 * Copyright (C) 2025 Jan Körner
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * This interface defines the functions for different memory management strategies. E.g. counting up, counting down, or
 * non-deterministically.
 *
 * @author Jan Körner
 */
public interface IMemoryManagementStrategy {
	/**
	 * Constructs a list of expressions that are used in the specifications of malloc.
	 *
	 * @return The expressions.
	 */
	List<Pair<Expression, Set<VariableLHS>>> constructMallocSpecificationExpressions(ILocation tuLoc,
			MemoryArea memoryArea, RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Constructs a list of expressions that are used in the specifications of dealloc.
	 *
	 * @return The expressions.
	 */
	List<Triple<Expression, Set<VariableLHS>, Boolean>> constructDeallocSpecificationExpressions(ILocation tuLoc,
			RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Returns a list of statements that are part of Ultimate.Init.
	 *
	 * @return The statements.
	 */
	List<Statement> constructUltimateInitStatements(ILocation loc,
			RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			MemoryModelDeclarationsHandler memoryModelDeclarationsHandler, BigInteger fixedAddressCounter);

	/**
	 * Constructs the expressions used in the specifications for allocInit.
	 *
	 * @return The expressions.
	 */
	List<Pair<Expression, Set<VariableLHS>>> constructAllocInitSpecificationExpressions(ILocation tuLoc,
			RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);
}
