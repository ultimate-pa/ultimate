/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction;

public class IndependenceMonitorVisitor<L, S, R, V /* extends IDfsVisitor<L, R> */> /*
																					 * extends WrapperVisitor<L, R, V>
																					 */ {

	// private final ISleepMapStateFactory<L, S, R> mFactory;
	//
	// private int mMinRelation; // not final
	// private final int mMaxRelation;
	//
	// public IndependenceMonitorVisitor(final V underlying, final ISleepMapStateFactory<L, S, R> factory,
	// final int minRelation, final int maxRelation) {
	// super(underlying);
	// mFactory = factory;
	// mMinRelation = minRelation; // pass the speculative successor budget
	// mMaxRelation = maxRelation; // pass the current state's budget
	// }
	//
	// @Override
	// public boolean discoverTransition(final R source, final L letter, final R target) {
	// // TODO check for letters that could be in target sleep map, but are not
	// // TODO check if they are not there because commutativity failed (could there be other reasons?)
	// // TODO check if a more concrete commutativity relation would have worked
	// // TODO if so, record the most abstract relation that would have worked (update mMinRelation)
	// // TODO in the future, only check for relations more concrete than that (mMinRelation <= i <= mMaxRelation)
	// mMinRelation = 0;
	// return super.discoverTransition(source, letter, target);
	// }

}
