package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator.PathInvariantsStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

public class PathInvariantsStatisticsType extends StatisticsType<PathInvariantsStatisticsDefinitions> {

	public PathInvariantsStatisticsType() {
		super(PathInvariantsStatisticsDefinitions.class);
	}

	private static PathInvariantsStatisticsType s_Instance = new PathInvariantsStatisticsType();

	public static PathInvariantsStatisticsType getInstance() {
		return s_Instance;
	}
}
