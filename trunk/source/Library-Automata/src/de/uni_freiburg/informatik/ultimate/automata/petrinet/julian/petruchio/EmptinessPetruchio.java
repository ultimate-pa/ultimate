/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.petruchio;

import java.util.ArrayList;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import petruchio.cov.Backward;
import petruchio.cov.SimpleList;
import petruchio.interfaces.petrinet.Place;
import petruchio.interfaces.petrinet.Transition;

/**
 * Check if a PetriNetJulian has an accepting run.
 * The emptiness check uses Tim Straznys Petruchio.
 * A marking of a PetriNetJulian is accepting if the marking contains an
 * accepting place.
 * EmptinessPetruchio checks if any (singleton) marking {p} such that p is an
 * accepting place can be covered.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <S>
 *            Type of alphabet symbols
 * @param <C>
 *            Type of place labeling
 */

public class EmptinessPetruchio<S, C> implements IOperation<S, C> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	@Override
	public String operationName() {
		return "emptinessPetruchio";
	}
	
	@Override
	public String startMessage() {
		return "Start emptinessPetruchio. "
				+ "Operand " + mNetJulian.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished emptinessPetruchio";
	}
	
	final PetruchioWrapper<S, C> mPetruchio;
	
	final PetriNetJulian<S, C> mNetJulian;
	
	NestedRun<S, C> mAcceptedRun = null;
	
	public EmptinessPetruchio(final AutomataLibraryServices services,
			final PetriNetJulian<S, C> net) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mNetJulian = net;
		mLogger.info(startMessage());
		mPetruchio = new PetruchioWrapper<S, C>(mServices, net);
		mAcceptedRun = constructAcceptingRun();
		mLogger.info(exitMessage());
	}
	
	/**
	 * @return Some accepting run if the Petri net has an accepting run, null
	 *         otherwise.
	 *         Note: A run should be an interleaved sequence of markings and symbols.
	 *         Here each marking will be null instead.
	 */
	private NestedRun<S, C> constructAcceptingRun() {
		mLogger.debug("Net has " + mNetJulian.getPlaces().size() + " Places");
		mLogger.debug("Net has " + mNetJulian.getTransitions().size() + " Transitions");
		
		// construct single invariant p_1 + ... + p_n where p_i \in places
		final Collection<Map<Place, Integer>> invariants = new ArrayList<Map<Place, Integer>>(1);
		final Map<Place, Integer> theInvariant =
				new IdentityHashMap<Place, Integer>(mPetruchio.getNet().getPlaces().size());
		for (final Place pPetruchio : mPetruchio.getNet().getPlaces()) {
			theInvariant.put(pPetruchio, Integer.valueOf(1));
		}
		invariants.add(theInvariant);
		
		// construct the following target:
		// at least one of { {p_j} | p_j \in Paccepting } is coverable
		final Collection<Map<Place, Integer>> targets = new ArrayList<Map<Place, Integer>>();
		for (final de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S, C> pAcceptingJulian : mNetJulian
				.getAcceptingPlaces()) {
			// construct single target pAccepting >= 1
			final Place pAcceptingPetruchio = mPetruchio.getpJulian2pPetruchio().get(pAcceptingJulian);
			final Map<Place, Integer> placeWithOneToken = new IdentityHashMap<Place, Integer>();
			placeWithOneToken.put(pAcceptingPetruchio, 1);
			targets.add(placeWithOneToken);
		}
		
		mLogger.debug("Check coverability of " + mNetJulian.getAcceptingPlaces().toString());
		mLogger.warn(targets);
		final SimpleList<Transition> tracePetruchio =
				Backward.checkCoverability(mPetruchio.getNet(), targets);//, invariants);
		mLogger.debug("done");
		
		if (tracePetruchio == null) {
			return null;
			
		} else {
			return tracePetruchio2run(tracePetruchio);
		}
		
	}
	
	/**
	 * Translate sequence of Petruchio transitions to run of PetriNet
	 */
	private NestedRun<S, C> tracePetruchio2run(final SimpleList<Transition> tracePetruchio) {
		
		NestedRun<S, C> result = new NestedRun<S, C>(null);
		// workaround if initial marking can be covered petruchio deliveres a
		// list with one element that is null
		if (tracePetruchio.getLength() == 1
				&& tracePetruchio.iterator().next() == null) {
			return result;
		}
		for (final Transition tPetruchio : tracePetruchio) {
			final S symbol = mPetruchio.gettPetruchio2tJulian().get(tPetruchio).getSymbol();
			final NestedRun<S, C> oneStepSubrun =
					new NestedRun<S, C>(null, symbol, NestedWord.INTERNAL_POSITION, null);
			result = result.concatenate(oneStepSubrun);
		}
		return result;
	}
	
	@Override
	public NestedRun<S, C> getResult() {
		return mAcceptedRun;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<C> stateFactory)
			throws AutomataLibraryException {
		mLogger.info("Testing correctness of emptinessCheck");
		
		boolean correct = true;
		if (mAcceptedRun == null) {
			final NestedRun<S, C> automataRun = (new IsEmpty<S, C>(mServices,
					(new PetriNet2FiniteAutomaton<S, C>(mServices, mNetJulian)).getResult())).getNestedRun();
			correct = (automataRun == null);
		} else {
			correct = mNetJulian.accepts(mAcceptedRun.getWord());
		}
		mLogger.info("Finished testing correctness of emptinessCheck");
		return correct;
	}
	
}
