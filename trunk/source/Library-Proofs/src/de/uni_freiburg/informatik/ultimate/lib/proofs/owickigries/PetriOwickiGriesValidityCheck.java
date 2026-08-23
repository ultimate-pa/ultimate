/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public class PetriOwickiGriesValidityCheck<L extends IAction, P> extends OwickiGriesValidityCheck<Transition<L, P>, P> {
	private final IPetriNet<L, P> mProgram;

	public PetriOwickiGriesValidityCheck(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final CfgSmtToolkit csToolkit, final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation) {
		super(services, csToolkit, annotation);
		mProgram = program;
	}

	public PetriOwickiGriesValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IPetriNet<L, P> program, final ModifiableGlobalsTable modifiableGlobals,
			final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation) {
		super(services, mgdScript, modifiableGlobals, annotation);
		mProgram = program;
	}

	public PetriOwickiGriesValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker htc, final IPetriNet<L, P> program,
			final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation) {
		super(services, mgdScript, htc, annotation);
		mProgram = program;
	}

	@Override
	protected Collection<P> getProgramLocations() {
		return mProgram.getPlaces();
	}

	@Override
	protected Collection<Transition<L, P>> getProgramTransitions() {
		return mProgram.getTransitions();
	}

	@Override
	protected Set<P> getPredecessors(final Transition<L, P> transition) {
		return transition.getPredecessors();
	}

	@Override
	protected Set<P> getSuccessors(final Transition<L, P> transition) {
		return transition.getSuccessors();
	}

	@Override
	protected UnmodifiableTransFormula getTransformula(final Transition<L, P> transition) {
		return transition.getSymbol().getTransformula();
	}
}
