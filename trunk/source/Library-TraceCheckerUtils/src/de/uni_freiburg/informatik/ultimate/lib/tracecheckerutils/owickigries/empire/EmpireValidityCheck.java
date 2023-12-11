/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.PetriFloydHoareValidityCheck;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Check a given Empire annotation for validity i.e. the initial markings law evaluates to true and every accepting
 * markings law evaluates to false. Further for all other markings m1, m2 must hold: If there is a firing relation f_t
 * between m1 and m2 then the Hoare-Triple {m1}t{m2} is valid.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public class EmpireValidityCheck<PLACE, LETTER extends IAction> {
	private final MarkingLaw<PLACE, LETTER> mMarkingLaw;
	private final BasicPredicateFactory mFactory;
	private final IPetriNet<LETTER, PLACE> mNet;
	private final MonolithicImplicationChecker mImplicationChecker;
	private final Validity mValidity;

	public EmpireValidityCheck(final MarkingLaw<PLACE, LETTER> markingLaw, final IPetriNet<LETTER, PLACE> net,
			final BasicPredicateFactory factory, final MonolithicImplicationChecker implicationChecker,
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable,
			final ModifiableGlobalsTable modifiableGlobals) throws PetriNetNot1SafeException {
		mMarkingLaw = markingLaw;
		mFactory = factory;
		mNet = net;
		mImplicationChecker = implicationChecker;
		mValidity = checkValidity(services, mgdScript, symbolTable, modifiableGlobals);
	}

	private boolean checkInitialMarking() {
		final Marking<PLACE> initialMarking = new Marking<>(ImmutableSet.copyOf(mNet.getInitialPlaces()));
		final IPredicate trueIPredicate = mFactory.and();
		return mImplicationChecker.checkImplication(trueIPredicate, false, mMarkingLaw.getMarkingLaw(initialMarking),
				false) == Validity.VALID;
	}

	private boolean checkFinalMarkings() {
		final Set<PLACE> acceptingPlaces = mNet.getAcceptingPlaces();
		for (final Marking<PLACE> marking : mMarkingLaw.getMarkings()) {
			if (marking.containsAny(acceptingPlaces)) {
				return false;
			}
		}
		return true;
	}

	private Validity checkHoareTriples(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable, final ModifiableGlobalsTable modifiableGlobals)
			throws PetriNetNot1SafeException {
		final PetriFloydHoareValidityCheck<LETTER, PLACE> petriFloydHoareValidityCheck;
		petriFloydHoareValidityCheck = new PetriFloydHoareValidityCheck<>(services, mgdScript, symbolTable,
				modifiableGlobals, mNet, mMarkingLaw.getLawMap());
		return petriFloydHoareValidityCheck.isValid();
	}

	private Validity checkValidity(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable, final ModifiableGlobalsTable modifiableGlobals)
			throws PetriNetNot1SafeException {
		final boolean initialMarkingValidity = checkInitialMarking();
		assert initialMarkingValidity : "Initial markings law does not evaluate to true.";
		final boolean finalMarkingValidity = checkFinalMarkings();
		assert finalMarkingValidity : "Final markings law does not evaluate to false";
		if (!initialMarkingValidity || !finalMarkingValidity) {
			return Validity.INVALID;
		}
		return checkHoareTriples(services, mgdScript, symbolTable, modifiableGlobals);
	}

	public Validity getValidity() {
		return mValidity;
	}
}
