/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * What a producer hands to the {@link InvariantSupplier}. The terms belong to the producer's own script {@link #source()};
 * the supplier copies them into its script on its own thread, so the producer never builds a term in a script it does
 * not own. The producer may keep using its script afterwards: terms are immutable, it only must not submit terms that
 * mention a function symbol it declared itself (program variables and constants are declared in every script).
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public sealed interface InvariantMessage {

	/** The script the terms of this message belong to. */
	ManagedScript source();

	/** Who produced the message, for the log. */
	String origin();

	/**
	 * Invariants that are sound by construction, e.g. the fixpoint of an abstract interpretation of the program. They
	 * are taken without a check.
	 *
	 * @param invariants
	 *            for a program location, a state predicate over the term variables of the program variables that holds
	 *            whenever control is at that location
	 */
	record TrustedInvariants(ManagedScript source, Map<IcfgLocation, Term> invariants, String origin)
			implements InvariantMessage {
		public TrustedInvariants {
			invariants = Map.copyOf(invariants);
		}
	}

	/**
	 * The interpolants of an infeasible trace. {@code interpolants.get(i)} holds at {@code locations.get(i)} on this
	 * trace, which does not make it an invariant of that location: the supplier only publishes what it proves to be
	 * inductive.
	 */
	record InterpolantSequence(ManagedScript source, List<IcfgLocation> locations, List<Term> interpolants,
			String origin) implements InvariantMessage {
		public InterpolantSequence {
			if (locations.size() != interpolants.size()) {
				throw new IllegalArgumentException("an interpolant sequence of " + origin + " has "
						+ interpolants.size() + " interpolant(s) for " + locations.size() + " location(s)");
			}
			locations = List.copyOf(locations);
			interpolants = List.copyOf(interpolants);
		}
	}
}
