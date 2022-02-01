/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Represents an incomplete Event. A <i>Candidate</i> consists of
 * <ul>
 * <li>the transition which belongs to the event</li>
 * <li>a list of {@link Condition}s that represents predecessor places of the
 * transition that have already been instantiated by (these) condition</li>
 * <li>a list of {@link Place}s that represent predecessor places of the
 * transition that have not yet been instantiated.</li>
 * </ul>
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 **/
public class Candidate<LETTER, PLACE> {

	private final ISuccessorTransitionProvider<LETTER, PLACE> mSuccTransProvider;

	
	private final LinkedList<Condition<LETTER, PLACE>> mInstantiated;
	private final LinkedList<PLACE> mNotInstantiated;
	private final Map<PLACE, Set<Condition<LETTER, PLACE>>> mPossibleInstantiationsMap;
	private final LinkedList<Condition<LETTER, PLACE>>  mInstantiatedButNotInitially;


	public Candidate(final ISuccessorTransitionProvider<LETTER, PLACE> succTransProvider,
			final Collection<Condition<LETTER, PLACE>> conditionsForImmediateInstantiation,
			final HashRelation<PLACE, Condition<LETTER, PLACE>> place2coRelatedConditions) {
		mSuccTransProvider = succTransProvider;
		mInstantiated = new LinkedList<>();
		mNotInstantiated = new LinkedList<>(mSuccTransProvider.getPredecessorPlaces());
		mInstantiatedButNotInitially =  new LinkedList<>();
		// instantiate the places with the given conditions
		for (final Condition<LETTER, PLACE> condition : conditionsForImmediateInstantiation) {
			final boolean wasContained = mNotInstantiated.remove(condition.getPlace());
			if (wasContained) {
				mInstantiated.add(condition);
			}
		}
		mPossibleInstantiationsMap = new HashMap<>();
		for (final PLACE p: mNotInstantiated) {
			mPossibleInstantiationsMap.put(p, place2coRelatedConditions.getImage(p));
		}
	}

	public Candidate(ISuccessorTransitionProvider<LETTER, PLACE> succTransProvider, LinkedList<PLACE> notInstantiated,
			LinkedList<Condition<LETTER, PLACE>> instantiated, Map<PLACE, Set<Condition<LETTER, PLACE>>> possibleInstantiationsMap) {
		mSuccTransProvider = succTransProvider;
		mInstantiated = instantiated;
		mNotInstantiated = notInstantiated;
		mPossibleInstantiationsMap = possibleInstantiationsMap;
		mInstantiatedButNotInitially = null;
	}


	public ISuccessorTransitionProvider<LETTER, PLACE> getTransition() {
		return mSuccTransProvider;
	}

	public boolean isFullyInstantiated() {
		return mNotInstantiated.isEmpty();
	}

	public PLACE getNextUninstantiatedPlace() {
		return mNotInstantiated.get(mNotInstantiated.size() - 1);
	}
	
	public Map<PLACE, Set<Condition<LETTER, PLACE>>> getPossibleInstantiationsMap(){
		return mPossibleInstantiationsMap;
	}
	public LinkedList<PLACE> getNotInstantiated() {
		return mNotInstantiated;
	}
	public  Set<Condition<LETTER, PLACE>> getPossibleInstantiations(PLACE p){
		assert !mPossibleInstantiationsMap.get(p).equals(null): "p must be contained in the map";
		return mPossibleInstantiationsMap.get(p);
	}

	public void instantiateNext(final Condition<LETTER, PLACE> condition) {
		if (!getNextUninstantiatedPlace().equals(condition.getPlace())) {
			throw new IllegalStateException();
		} else {
			mInstantiatedButNotInitially.add(condition);
			mInstantiated.add(condition);
			mNotInstantiated.remove(mNotInstantiated.size() - 1);
		}
	}

	public void undoOneInstantiation() {
		final Condition<LETTER, PLACE> last = mInstantiated.remove(mInstantiated.size() - 1);
		mInstantiatedButNotInitially.remove(mInstantiatedButNotInitially.size() - 1);
		mNotInstantiated.add(last.getPlace());
	}
	public List<Condition<LETTER, PLACE>> getInstantiatedButNotInitially() {
		return mInstantiatedButNotInitially;
	}

	public List<Condition<LETTER, PLACE>> getInstantiated() {
		return Collections.unmodifiableList(mInstantiated);
	}

	@Override
	public String toString() {
		return mSuccTransProvider.toString();
	}
}
