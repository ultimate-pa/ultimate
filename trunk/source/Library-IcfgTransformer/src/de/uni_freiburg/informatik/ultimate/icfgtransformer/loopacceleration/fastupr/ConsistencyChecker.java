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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
*
* @author Jill Enke (enkei@informatik.uni-freiburg.de)
*
*/
public class ConsistencyChecker {

	private final Term mResult;
	private final boolean mSuccess;
	private final FastUPRUtils mUtils;
	ManagedScript mManagedScript;
	ILogger mLogger;
	IUltimateServiceProvider mServices;
	
	public ConsistencyChecker(FastUPRUtils utils, ILogger logger, ManagedScript managedScript, IUltimateServiceProvider services, UnmodifiableTransFormula formula, int b, int c) {
		mLogger = logger;
		mServices = services;
		mManagedScript = managedScript;
		mUtils = utils;
		Script script = mManagedScript.getScript();
		mResult = check(formula, b, c, script);https://www.reddit.com/r/Overwatch/comments/618nv8/runaway_kaiser_with_a_huge_earthshatter/?utm_content=comments&utm_medium=front&utm_source=reddit&utm_name=Overwatch
		mSuccess = ((mResult == null) ? false : true);
	}

	private Term check(UnmodifiableTransFormula formula, int b, int c, Script script) {
		for (int k = 0; k <= 2; k++) {
			if(!solve(formula, b, c, k, script)) {
				// return S1
				return null;	
			}
		}
		
		return null;
	}
	
	private boolean solve(UnmodifiableTransFormula formula, int b, int c, int k, Script script) {
		UnmodifiableTransFormula toCheck = mUtils.composition(mLogger, mServices, mManagedScript, formula, b + (k * c));
		return (script.checkSatAssuming(toCheck.getFormula()).equals(LBool.SAT));
	}
	
	public boolean isSuccess() {
		return mSuccess;
	}

	public Term getResult() {
		return mResult;
	}

}
