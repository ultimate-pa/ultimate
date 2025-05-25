package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

public class Test {
	public static void test(final BoogieIcfgContainer icfg) {
		System.out.println("TEST");
		for (final BoogieIcfgLocation icfgLocation : icfg.getInitialNodes()) {
			System.out.println(icfgLocation.getOutgoingEdges().toString());
			final DfgBuilder dfgBuilder = new DfgBuilder();
			final DfgContainer dfg = dfgBuilder.buildDfg(icfgLocation);
			System.out.println("PRINTING EDGERELATION");
			System.out.println(dfg.getEdgeRelation().toString());
			System.out.println("ERFLOG");

		}
	}

}
