/*
 * Copyright (C) 2016 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 *
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.util;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class FirstOrderLinearODE {
	String mODE;
	String mSolution;
	String mTimeVar;
	Term mSolutionTerm;
	
	public FirstOrderLinearODE(final String ode, final String timevarName) {
		mODE = ode;
		mTimeVar = timevarName;
		mSolution = solveODE(ode);
	}
	
	private String solveODE(final String ode) {
		String result = "";
		final List<String> evaluationList = new ArrayList<>();
		final List<String> equationArray = SpaceExMathHelper.expressionToArray(ode);
		for (int i = 0; i < equationArray.size(); i++) {
			final String element = equationArray.get(i);
			if (i == 0) {
				result += element + "==" + element;
			} else if ("==".equals(element) || "=".equals(element)) {
				continue;
			} else {
				evaluationList.add(element);
			}
		}
		result += integrateWrtToT(evaluationList);
		return result;
	}
	
	private String integrateWrtToT(final List<String> evaluationList) {
		String integral = "";
		for (final String el : evaluationList) {
			if (el.matches("\\*|\\+|-|/|\\(|\\)")) {
				integral += el;
			} else {
				integral += el + "*" + mTimeVar;
			}
		}
		if (!integral.startsWith("-") && !integral.startsWith("+")) {
			integral = "+" + integral;
		}
		return integral;
	}
	
	public String getmSolution() {
		return mSolution;
	}
	
	public Term getmSolutionTerm() {
		return mSolutionTerm;
	}
}
