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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
final class BacktranslationServiceMock implements IBacktranslationService {

	@Override
	public <STE, TTE, SE, TE, SVL, TVL> void addTranslator(final ITranslator<STE, TTE, SE, TE, SVL, TVL> translator) {
		// does nothing
	}

	@Override
	public <SE, TE> TE translateExpression(final SE expression, final Class<SE> sourceExpressionClass) {
		return null;
	}

	@Override
	public <SE> String translateExpressionToString(final SE expression, final Class<SE> clazz) {
		return "";
	}

	@Override
	public <STE> List<?> translateTrace(final List<STE> trace, final Class<STE> clazz) {
		return Collections.emptyList();
	}

	@Override
	public <STE> List<String> translateTraceToHumanReadableString(final List<STE> trace, final Class<STE> clazz) {
		return Collections.emptyList();
	}

	@Override
	public <STE, SE> IProgramExecution<?, ?>
			translateProgramExecution(final IProgramExecution<STE, SE> programExecution) {
		return new ProgramExecutionMock<>(null, null);
	}
	
	@Override
	public <SE> ProgramState<?> translateProgramState(final ProgramState<SE> programState) {
		return null;
	}

	@Override
	public <STE, SE> IBacktranslatedCFG<?, ?> translateCFG(final IBacktranslatedCFG<?, STE> cfg) {
		return null;
	}

	@Override
	public IBacktranslationService getTranslationServiceCopy() {
		return this;
	}


}