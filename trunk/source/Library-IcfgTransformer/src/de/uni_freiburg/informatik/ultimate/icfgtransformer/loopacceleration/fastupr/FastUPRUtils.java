/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
*
* @author Jill Enke (enkei@informatik.uni-freiburg.de)
*
*/
public class FastUPRUtils {
	
	private UnmodifiableTransFormula mCachedFormula;
	private int mCachedCount;
	private final ILogger mLogger;
	
	public FastUPRUtils(ILogger logger) {
		mLogger = logger;
		// Prevent instantiation of this utility class
	}
	
	public UnmodifiableTransFormula composition(ILogger logger, IUltimateServiceProvider services, ManagedScript managedScript, UnmodifiableTransFormula formula, int count) {
		ArrayList<UnmodifiableTransFormula> formulas = new ArrayList<>();
		
		
		if (mCachedCount <= count) {
			formulas.add(mCachedFormula);
			for (int i = mCachedCount + 1; i <= count; i++) {
				formulas.add(formula);
			}
		} else {
			for (int i = 1; i <= count; i++) {
				formulas.add(formula);
			}
		}
		
		
		
		mCachedCount = count;
		mCachedFormula = TransFormulaUtils.sequentialComposition(logger,
				services,
				managedScript,
				false,
				false,
				false,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
				SimplificationTechnique.SIMPLIFY_DDA,
				formulas);
		
		mLogger.debug(mCachedFormula.toString());
		
		return mCachedFormula;
		
	}
}
