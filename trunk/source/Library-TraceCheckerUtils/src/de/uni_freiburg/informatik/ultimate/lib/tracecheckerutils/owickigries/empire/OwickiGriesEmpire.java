/*
 * Copyright (C) 2020 University of Freiburg
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

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * An Owicki/Gries Empire annotation of a Petri program.
 *
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <LETTER>
 *            The type of program statements
 * @param <PLACE>
 *            The type of places in the Petri program
 */
public class OwickiGriesEmpire<LETTER, PLACE> {

	/**
	 * The set of Territories.
	 */
	/* TODO:Change type to Set<TERRITORY> */
	private final Set<Set<Set<PLACE>>> mEmpire;

	/**
	 * The set of regions in the Empire.
	 */
	/* TODO:Change type to Set<REGION> */
	private final Set<Set<PLACE>> mColony;

	/**
	 * "Law" - maps a territory to a predicate that holds at all markings contained in the territory. TODO: Change Map
	 * type to territory,predicate.
	 */
	private final Map<PLACE, IPredicate> mLaw;

	/**
	 * The annotated Petri program.
	 */
	private final IPetriNet<LETTER, PLACE> mPetriNet;

	/**
	 * The foundation crown map of the empire.
	 */
	private final Map<LETTER, PLACE> mCrown;

	/**
	 * A symbol table containing both the program symbols and the ghost variables in the annotation.
	 */
	private final IIcfgSymbolTable mSymbolTable;

	public OwickiGriesEmpire(final Set<Set<Set<PLACE>>> empire, final Set<Set<PLACE>> colony,
			final Map<PLACE, IPredicate> law, final IPetriNet<LETTER, PLACE> net, final Map<LETTER, PLACE> crown,
			final IIcfgSymbolTable symbolTable) {

		mEmpire = empire;
		mColony = colony;
		mLaw = law;
		mPetriNet = net;
		mCrown = crown;
		mSymbolTable = symbolTable;
	}

	public Set<Set<Set<PLACE>>> getEmpire() {
		return mEmpire;
	}

	public Set<Set<PLACE>> getColony() {
		return mColony;
	}

	public Map<PLACE, IPredicate> getLaw() {
		return mLaw;
	}

	public Map<LETTER, PLACE> getCrown() {
		return mCrown;
	}

	/**
	 * TODO: Check Inductivity & Interference freedom, other properties of all territories
	 */
	public boolean checkValidity() {
		return true;
	}
}
