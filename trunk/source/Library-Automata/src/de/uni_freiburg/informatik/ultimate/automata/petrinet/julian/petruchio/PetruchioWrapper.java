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

import java.util.IdentityHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import petruchio.interfaces.petrinet.Place;
import petruchio.interfaces.petrinet.Transition;
import petruchio.pn.PetriNet;

/**
 * Wraps the Petri net representation used in Tim Strazny's Petruchio.
 * <p>
 * Use a {@link PetriNetJulian} to construct a Petruchio Petri net. Stores mapping for transitions and places of both
 * representations.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            Type of alphabet symbols
 * @param <C>
 *            Type of place labeling
 */

public class PetruchioWrapper<S, C> {
	private final ILogger mLogger;

	private final PetriNetJulian<S, C> mNetJulian;
	private final PetriNet mNetPetruchio = new PetriNet();

	// Maps each place of mNetJulian to the corresponding place in mNetPetruchio
	private final Map<de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S, C>, Place> mPJulian2pPetruchio =
			new IdentityHashMap<>();

	// Maps each transition of mNetPetruchio to the corresponding transition in mNetJulian
	private final Map<Transition, ITransition<S, C>> mTPetruchio2tJulian = new IdentityHashMap<>();

	/**
	 * @param services
	 *            Ultimate services.
	 * @param net
	 *            Petri net
	 */
	public PetruchioWrapper(final AutomataLibraryServices services, final PetriNetJulian<S, C> net) {
		mLogger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mNetJulian = net;
		constructNetPetruchio();
	}

	/**
	 * Given a {@link PetriNetJulian}, construct
	 * <ul>
	 * <li>the corresponding Petruchio Petri net representation mNetPetruchio
	 * <li>the Julian -> Petruchio place mapping plMap
	 * <li>the Petruchio -> Julian place mapping trMap.
	 * </ul>
	 */
	private void constructNetPetruchio() {
		// construct a Petruchio place for each NetJulian place
		for (final de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S, C> pJulian : mNetJulian.getPlaces()) {
			Place pPetruchio;
			String pLabel = "";
			final C content = pJulian.getContent();
			pLabel += content;
			pLabel += String.valueOf(content.hashCode());
			pPetruchio = mNetPetruchio.addPlace(pLabel, mNetJulian.getInitialMarking().contains(pJulian) ? 1 : 0);
			// 1-sicheres Netz, Info hilft Petruchio/BW
			pPetruchio.setBound(1);
			mPJulian2pPetruchio.put(pJulian, pPetruchio);
		}
		// construct a Petruchio transition for each NetJulian transition
		for (final ITransition<S, C> tJulian : mNetJulian.getTransitions()) {
			final Transition transitionPetruchio = mNetPetruchio.addTransition(tJulian.toString());
			mTPetruchio2tJulian.put(transitionPetruchio, tJulian);
			// PTArcs kopieren
			for (final de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S, C> pJulian : tJulian
					.getSuccessors()) {
				// 1-safe net
				mNetPetruchio.addArc(transitionPetruchio, mPJulian2pPetruchio.get(pJulian), 1);
			}
			// TPArcs kopieren
			for (final de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S, C> p : tJulian
					.getPredecessors()) {
				// 1-safe net
				mNetPetruchio.addArc(mPJulian2pPetruchio.get(p), transitionPetruchio, 1);
			}
		}
	}

	/**
	 * Write Petri net to file by using Petruchio. The ending of the filename
	 * determines how the Petri net is encoded (e.g., .spec, .lola, etc.).
	 * 
	 * @param filename
	 *            file name
	 */
	public void writeToFile(final String filename) {
		mLogger.debug("Writing net to file " + filename);
		petruchio.pn.Converter.writeNet(mNetPetruchio, filename);
		mLogger.info("Accepting places: " + mNetJulian.getAcceptingPlaces());
	}

	/**
	 * @return Map (place in {@link PetriNetJulian} -> place in Petruchio).
	 */
	public Map<de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S, C>, Place> getpJulian2pPetruchio() {
		return mPJulian2pPetruchio;
	}

	/**
	 * @return Map (transition in {@link PetriNetJulian} -> transition in Petruchio).
	 */
	public Map<Transition, ITransition<S, C>> gettPetruchio2tJulian() {
		return mTPetruchio2tJulian;
	}

	public PetriNet getNet() {
		return mNetPetruchio;
	}
}
