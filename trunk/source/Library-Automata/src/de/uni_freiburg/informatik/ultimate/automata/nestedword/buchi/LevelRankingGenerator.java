/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Builder used by buchiComplementFKV to obtain TightLevelRankingStateGenerators.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @param <CONSTRAINT>
 *            constraint type
 */
public abstract class LevelRankingGenerator<LETTER, STATE, CONSTRAINT extends LevelRankingConstraint<LETTER, STATE>> {
	protected final AutomataLibraryServices mServices;
	protected final ILogger mLogger;
	protected final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	protected final int mUserDefinedMaxRank;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param userDefinedMaxRank
	 *            user-defined maximal rank
	 */
	public LevelRankingGenerator(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final int userDefinedMaxRank) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = operand;
		mUserDefinedMaxRank = userDefinedMaxRank;
	}

	/**
	 * @param constraint
	 *            The constraint.
	 * @param predecessorIsSubsetComponent
	 *            {@code true} iff the predecessor is of subset component type
	 * @return level rankings
	 */
	public abstract Collection<LevelRankingState<LETTER, STATE>> generateLevelRankings(CONSTRAINT constraint,
			boolean predecessorIsSubsetComponent);
}
