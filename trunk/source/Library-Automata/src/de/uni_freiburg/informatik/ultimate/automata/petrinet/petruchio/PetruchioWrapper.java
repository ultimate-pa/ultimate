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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.petruchio;

import java.util.IdentityHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import petruchio.interfaces.petrinet.Place;
import petruchio.interfaces.petrinet.Transition;
import petruchio.pn.PetriNet;

/**
 * Wraps the Petri net representation used in Tim Strazny's Petruchio.
 * <p>
 * Use a {@link BoundedPetriNet} to construct a Petruchio Petri net. Stores mapping for transitions and places of both
 * representations.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Type of alphabet symbols
 * @param <PLACE>
 *            Type of place labeling
 */

public class PetruchioWrapper<LETTER, PLACE> {
	private final ILogger mLogger;

	private final BoundedPetriNet<LETTER, PLACE> mBoundedNet;
	private final PetriNet mNetPetruchio = new PetriNet();

	// Maps each place of mBoundedNet to the corresponding place in mNetPetruchio
	private final Map<PLACE, Place> mPBounded2pPetruchio =
			new IdentityHashMap<>();

	// Maps each transition of mNetPetruchio to the corresponding transition in mBoundedNet
	private final Map<Transition, ITransition<LETTER, PLACE>> mTPetruchio2tBounded = new IdentityHashMap<>();

	/**
	 * @param services
	 *            Ultimate services.
	 * @param net
	 *            Petri net
	 */
	public PetruchioWrapper(final AutomataLibraryServices services, final BoundedPetriNet<LETTER, PLACE> net) {
		mLogger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mBoundedNet = net;
		constructNetPetruchio();
	}

	/**
	 * Given a {@link BoundedPetriNet}, construct
	 * <ul>
	 * <li>the corresponding Petruchio Petri net representation mNetPetruchio
	 * <li>the Bounded -> Petruchio place mapping plMap
	 * <li>the Petruchio -> Bounded place mapping trMap.
	 * </ul>
	 */
	private void constructNetPetruchio() {
		// construct a Petruchio place for each BoundedNet place
		for (final PLACE pBounded : mBoundedNet.getPlaces()) {
			Place pPetruchio;
			String pLabel = "";
			final PLACE content = pBounded;
			pLabel += content;
			pLabel += String.valueOf(content.hashCode());
			pPetruchio = mNetPetruchio.addPlace(pLabel, mBoundedNet.getInitialPlaces().contains(pBounded) ? 1 : 0);
			// 1-sicheres Netz, Info hilft Petruchio/BW
			pPetruchio.setBound(1);
			mPBounded2pPetruchio.put(pBounded, pPetruchio);
		}
		// construct a Petruchio transition for each BoundedNet transition
		for (final ITransition<LETTER, PLACE> tBounded : mBoundedNet.getTransitions()) {
			final Transition transitionPetruchio = mNetPetruchio.addTransition(tBounded.toString());
			mTPetruchio2tBounded.put(transitionPetruchio, tBounded);
			// PTArcs kopieren
			for (final PLACE pBounded :
				mBoundedNet.getSuccessors(tBounded)) {
				// 1-safe net
				mNetPetruchio.addArc(transitionPetruchio, mPBounded2pPetruchio.get(pBounded), 1);
			}
			// TPArcs kopieren
			for (final PLACE p :
					mBoundedNet.getPredecessors(tBounded)) {
				// 1-safe net
				mNetPetruchio.addArc(mPBounded2pPetruchio.get(p), transitionPetruchio, 1);
			}
		}
	}

	/**
	 * Write Petri net to file by using Petruchio. The ending of the filename determines how the Petri net is encoded
	 * (e.g., .spec, .lola, etc.).
	 *
	 * @param filename
	 *            file name
	 */
	public void writeToFile(final String filename) {
		mLogger.debug("Writing net to file " + filename);
		petruchio.pn.Converter.writeNet(mNetPetruchio, filename);
		mLogger.info("Accepting places: " + mBoundedNet.getAcceptingPlaces());
	}

	/**
	 * @return Map (place in {@link BoundedPetriNet} -> place in Petruchio).
	 */
	public Map<PLACE, Place> getpBounded2pPetruchio() {
		return mPBounded2pPetruchio;
	}

	/**
	 * @return Map (transition in {@link BoundedPetriNet} -> transition in Petruchio).
	 */
	public Map<Transition, ITransition<LETTER, PLACE>> gettPetruchio2tBounded() {
		return mTPetruchio2tBounded;
	}

	public PetriNet getNet() {
		return mNetPetruchio;
	}
}
