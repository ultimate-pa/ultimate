/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE JUnit Helper Library.
 *
 * The ULTIMATE JUnit Helper Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE JUnit Helper Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JUnit Helper Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JUnit Helper Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE JUnit Helper Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.test.mocks;

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.core.lib.results.NoBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;

/**
 * This class mocks {@link IProgramExecution}. It can be used in JUnit tests.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <TE>
 * @param <E>
 */
final class ProgramExecutionMock<TE, E> implements IProgramExecution<TE, E> {

	private final Class<E> mExprClazz;
	private final Class<TE> mTraceElementClazz;

	public ProgramExecutionMock(final Class<E> exprClazz, final Class<TE> traceElementClazz) {
		mExprClazz = exprClazz;
		mTraceElementClazz = traceElementClazz;
	}

	@Override
	public int getLength() {
		return 0;
	}

	@Override
	public AtomicTraceElement<TE> getTraceElement(final int index) {
		throw new IndexOutOfBoundsException();
	}

	@Override
	public ProgramState<E> getProgramState(final int index) {
		throw new IndexOutOfBoundsException();
	}

	@Override
	public ProgramState<E> getInitialProgramState() {
		return new ProgramState<>(Collections.emptyMap());
	}

	@Override
	public Class<E> getExpressionClass() {
		return mExprClazz;
	}

	@Override
	public Class<TE> getTraceElementClass() {
		return mTraceElementClazz;
	}

	@Override
	public IBacktranslationValueProvider<TE, E> getBacktranslationValueProvider() {
		return new NoBacktranslationValueProvider<>();
	}
}
