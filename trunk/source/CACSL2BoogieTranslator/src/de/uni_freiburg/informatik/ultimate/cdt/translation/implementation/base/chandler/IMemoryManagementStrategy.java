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
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * This interface defines the functions for different memory management strategies. E.g. counting up, counting down, or
 * non-deterministically.
 *
 * @author Jan Körner
 */
public interface IMemoryManagementStrategy {
	/**
	 * Constructs the specification of malloc.
	 *
	 * @return a record representing the specification
	 */
	AllocationProcedureSpec constructMallocSpecification(ILocation tuLoc, MemoryArea memoryArea,
			RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Constructs the specification of dealloc.
	 *
	 * @return a record representing the specification
	 */
	AllocationProcedureSpec constructDeallocSpecification(ILocation tuLoc,
			RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Constructs the specification for allocInit.
	 *
	 * @return a record representing the specification
	 */
	AllocationProcedureSpec constructAllocInitSpecification(ILocation tuLoc,
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
	 * Encapsulates the specification for an allocation procedure.
	 *
	 * Currently, we do not allow allocation procedures to have "requires" clauses.
	 *
	 * @param ensures
	 *            the "ensures" clauses for the procedure
	 * @param freeEnsures
	 *            the "free ensures" clauses for the procedure
	 * @param modifies
	 *            the set of modified global variables of the procedure
	 */
	record AllocationProcedureSpec(List<Expression> ensures, List<Expression> freeEnsures, Set<VariableLHS> modifies) {
		/**
		 * Convenience constructor for specs that do not have "free ensures" clauses.
		 */
		AllocationProcedureSpec(final List<Expression> ensures, final Set<VariableLHS> modifies) {
			this(ensures, Collections.emptyList(), modifies);
		}

		public AllocationProcedureSpec {
			Objects.requireNonNull(ensures);
			Objects.requireNonNull(freeEnsures);
			Objects.requireNonNull(modifies);
		}

		/**
		 * Constructs "requires" resp. "free requires" clauses from the expressions stored in this specification.
		 *
		 * Note: Do not forget to handle the "modifies" clauses separately!
		 *
		 * @param loc
		 *            the location for the specification clauses
		 * @return the list of clauses
		 */
		List<EnsuresSpecification> constructSpecificationClauses(final ILocation loc) {
			final var result = new ArrayList<EnsuresSpecification>();
			for (final Expression ens : ensures) {
				result.add(new EnsuresSpecification(loc, false, ens));
			}
			for (final Expression freeEns : freeEnsures) {
				result.add(new EnsuresSpecification(loc, true, freeEns));
			}
			return result;
		}
	}
}
