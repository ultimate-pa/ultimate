package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

public record ThreadModularAbsintPrefs(String method, String locationAbstraction, String interferencePrestatePrecision,
		String locationReduction, Boolean reiterate, Integer maxStates, Integer maxItf) {
}
