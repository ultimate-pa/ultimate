/*
 * Copyright (C) 2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.nontermination;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.logic.Term;


/**
 * Represents a non-termination argument for a lasso program. <br>
 * This is work in progress and should probably replace
 * {@link InfiniteFixpointRepetition}. Currently, we have only an execution for
 * the stem because we cannot yet compute an execution for the loop.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de
 */
public class InfiniteFixpointRepetitionWithExecution<L extends IIcfgTransition<?>> extends NonTerminationArgument implements Serializable {

	private static final long serialVersionUID = -4391252776990865865L;

	private final IProgramExecution<L, Term> mStemExecution;

	public InfiniteFixpointRepetitionWithExecution(final IProgramExecution<L, Term> stemExecution) {
		super();
		mStemExecution = stemExecution;
	}

	public IProgramExecution<L, Term> getStemExecution() {
		return mStemExecution;
	}

}
