/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 * Sometimes we might want to verify a property under the assumption that a certain precondition holds. In the trace
 * abstraction CEGAR loop we do not reuse {@link IPredicate}s from one iteration to another. Hence we cannot use the
 * same {@link IPredicate} in each iteration but need a mechanism hat provides a new {@link IPredicate} in each
 * iteration.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
@FunctionalInterface
public interface IPreconditionProvider {

	IPredicate constructPrecondition(IPredicateUnifier predicateUnifier);

	/**
	 * Construct {@link IPreconditionProvider} that always return a the {@link IPredicate} true. Use this
	 * {@link IPreconditionProvider} if you do not have any assumptions about the initial state of the verified system.
	 */
	static IPreconditionProvider constructDefaultPreconditionProvider() {
		return IPredicateUnifier::getTruePredicate;
	}

}
