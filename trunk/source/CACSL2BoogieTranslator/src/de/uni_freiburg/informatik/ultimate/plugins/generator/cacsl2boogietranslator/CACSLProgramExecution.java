/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.ProgramExecutionFormatter;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Boogie2ACSL.BacktranslatedExpression;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class CACSLProgramExecution implements IProgramExecution<CACSLLocation, BacktranslatedExpression> {

	private final ProgramState<BacktranslatedExpression> mInitialState;
	private final List<ProgramState<BacktranslatedExpression>> mProgramStates;
	private final List<AtomicTraceElement<CACSLLocation>> mTrace;
	private final boolean mIsConcurrent;

	public CACSLProgramExecution(final ProgramState<BacktranslatedExpression> initialState,
			final Collection<AtomicTraceElement<CACSLLocation>> trace,
			final Collection<ProgramState<BacktranslatedExpression>> programStates, final boolean isConcurrent) {
		assert trace != null;
		assert programStates != null;
		assert trace.size() == programStates.size() : "Need a program state after each atomic trace element";
		mProgramStates = new ArrayList<>(programStates);
		mTrace = new ArrayList<>(trace);
		mInitialState = initialState;
		mIsConcurrent = isConcurrent;
	}

	public CACSLProgramExecution(final Collection<AtomicTraceElement<CACSLLocation>> trace,
			final boolean isConcurrent) {
		assert trace != null;
		mTrace = new ArrayList<>(trace);
		mProgramStates = new ArrayList<>();
		for (int i = 0; i < mTrace.size(); ++i) {
			mProgramStates.add(null);
		}
		mInitialState = null;
		mIsConcurrent = isConcurrent;
	}

	@Override
	public int getLength() {
		return mTrace.size();
	}

	@Override
	public AtomicTraceElement<CACSLLocation> getTraceElement(final int i) {
		return mTrace.get(i);
	}

	@Override
	public ProgramState<BacktranslatedExpression> getProgramState(final int i) {
		return mProgramStates.get(i);
	}

	@Override
	public ProgramState<BacktranslatedExpression> getInitialProgramState() {
		return mInitialState;
	}

	@Override
	public Class<BacktranslatedExpression> getExpressionClass() {
		return BacktranslatedExpression.class;
	}

	@Override
	public Class<CACSLLocation> getTraceElementClass() {
		return CACSLLocation.class;
	}

	@Override
	public String toString() {
		final ProgramExecutionFormatter<CACSLLocation, BacktranslatedExpression> pef =
				new ProgramExecutionFormatter<>(new CACSLBacktranslationValueProvider());
		return pef.formatProgramExecution(this);
	}

	@Override
	public IBacktranslationValueProvider<CACSLLocation, BacktranslatedExpression> getBacktranslationValueProvider() {
		return new CACSLBacktranslationValueProvider();
	}

	@Override
	public boolean isConcurrent() {
		return mIsConcurrent;
	}
}
