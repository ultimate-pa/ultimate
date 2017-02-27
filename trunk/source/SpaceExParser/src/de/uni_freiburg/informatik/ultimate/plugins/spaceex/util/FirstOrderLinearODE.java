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
				result += element.replaceAll("'", "") + "==" + element.replaceAll("'", "");
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
