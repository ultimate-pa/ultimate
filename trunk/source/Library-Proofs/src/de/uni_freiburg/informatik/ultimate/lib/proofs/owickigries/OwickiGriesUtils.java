/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.ThreadModularPrePostSpecification;

/**
 * Provides utility functionalities related to Owicki-Gries proofs.
 */
public class OwickiGriesUtils {
	/**
	 * Constructs the default specification for Petri programs: from the initial marking, no accepting place is
	 * reachable.
	 *
	 * @param <L>
	 *            the type of actions in the Petri program
	 * @param <P>
	 *            the type of places in the Petri program
	 * @param net
	 *            the Petri net
	 * @param factory
	 *            the predicate factory to use for the specification
	 * @return the thread-modular specification as described above
	 */
	public static <L, P> ThreadModularPrePostSpecification<P, Marking<P>>
			getSpecificationForPetriNet(final IPetriNet<L, P> net, final BasicPredicateFactory factory) {
		final var preconditions = Map.of(Marking.initial(net), factory.and());
		return new ThreadModularPrePostSpecification<>(preconditions, net::isAccepting, factory.or());
	}
}
