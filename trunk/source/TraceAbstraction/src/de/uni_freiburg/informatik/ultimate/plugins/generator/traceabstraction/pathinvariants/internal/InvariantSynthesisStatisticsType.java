package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator.InvariantSynthesisStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

public class InvariantSynthesisStatisticsType extends StatisticsType<InvariantSynthesisStatisticsDefinitions> {

	public InvariantSynthesisStatisticsType() {
		super(InvariantSynthesisStatisticsDefinitions.class);
	}

	private static InvariantSynthesisStatisticsType s_Instance = new InvariantSynthesisStatisticsType();

	public static InvariantSynthesisStatisticsType getInstance() {
		return s_Instance;
	}
}
