/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Default implementation of {@link IForkActionThreadCurrent}.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class BasicForkActionCurrent extends AbstractBasicAction implements IForkActionThreadCurrent {
	private final UnmodifiableTransFormula mTransFormula;
	private final ForkSmtArguments mForkSmtArguments;
	private final String mNameOfForkedProcedure;

	public BasicForkActionCurrent(final String preceedingProcedure, final String succeedingProcedure,
			final UnmodifiableTransFormula transFormula, final ForkSmtArguments forkSmtArguments,
			final String nameOfForkedProcedure) {
		super(preceedingProcedure, succeedingProcedure);
		mTransFormula = transFormula;
		mForkSmtArguments = forkSmtArguments;
		mNameOfForkedProcedure = nameOfForkedProcedure;
	}

	@Override
	public UnmodifiableTransFormula getTransformula() {
		return mTransFormula;
	}

	@Override
	public ForkSmtArguments getForkSmtArguments() {
		return mForkSmtArguments;
	}

	@Override
	public String getNameOfForkedProcedure() {
		return mNameOfForkedProcedure;
	}
}
