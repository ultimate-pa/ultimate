/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.lpsolver;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.lpsolver.ojalgo.OjAlgoSolver;

/**
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class LpSolverFactory {

	private final ILogger mLogger;
	// private final Class<? extends Number> mType;

	private enum Type {
		BIGDECIMAL, BIGINTEGER, DOUBLE, INTEGER,
	}

	private final Type mType;

	public LpSolverFactory(ILogger logger,IUltimateServiceProvider services) {
		mLogger = logger;
		final IPreferenceProvider prefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
		final String type = prefs.getString(LpSolverPreferences.LABEL_LPSOLVER_NUMBER_TYPE);

		if (type.equals(LpSolverPreferences.VALUE_NUMBER_TYPE_BIGDECIMAL)) {
			mType = Type.BIGDECIMAL;
		} else if (type.equals(LpSolverPreferences.VALUE_NUMBER_TYPE_BIGINTEGER)) {
			mType = Type.BIGINTEGER;
		} else if (type.equals(LpSolverPreferences.VALUE_NUMBER_TYPE_DOUBLE)) {
			mType = Type.DOUBLE;
		} else if (type.equals(LpSolverPreferences.VALUE_NUMBER_TYPE_INTEGER)) {
			mType = Type.INTEGER;
		} else {
			mType = Type.BIGDECIMAL;
		}
	}

	protected ILpSolver<? extends Number> getOjAlgoLpSolver() {
		switch (mType) {
		case BIGDECIMAL:
			return new OjAlgoSolver<BigDecimal>(mLogger, BigDecimal.class);
		case BIGINTEGER:
			return new OjAlgoSolver<BigInteger>(mLogger, BigInteger.class);
		case DOUBLE:
			return new OjAlgoSolver<Double>(mLogger, Double.class);
		case INTEGER:
			return new OjAlgoSolver<Integer>(mLogger, Integer.class);
		default:
			return new OjAlgoSolver<BigDecimal>(mLogger, BigDecimal.class);
		}
	}

}
