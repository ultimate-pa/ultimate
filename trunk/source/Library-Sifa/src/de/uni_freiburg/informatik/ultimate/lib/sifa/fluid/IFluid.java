/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.fluid;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * An oracle deciding when to apply abstraction to predicates. Fluids are related to abstract domains.
 * The difference is that {@link IDomain#alpha(IPredicate)} describes <i>how</i> to abstract and
 * {@link IFluid#shallBeAbstracted(IPredicate)} describes <i>when</i> to abstract.
 * <p>
 * At certain points during interpretation the oracle is asked whether a symbolic state should be abstracted or not.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
@FunctionalInterface
public interface IFluid {

	/**
	 * Asks the oracle whether to abstract or not.
	 *
	 * @param predicate
	 *            Symbolic state
	 * @return The predicate shall be abstracted (using any {@link IDomain#alpha(IPredicate)})
	 */
	boolean shallBeAbstracted(IPredicate predicate);
}
