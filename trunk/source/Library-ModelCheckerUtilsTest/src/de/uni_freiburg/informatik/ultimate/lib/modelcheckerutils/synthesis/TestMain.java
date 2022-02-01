package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.synthesis;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;


public class TestMain {
	public static void main(final String[] args) {
		System.out.println("test");
	}

	public static void testEntryPoint(final IIcfg<IcfgLocation> icfg, final IUltimateServiceProvider mServices) {
		System.out.println("got root node");
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();

		final boolean mAnnotateTerms = true;
		final Script mScript = (Script) mgdScript;

//		final MotzkinTransformation motzkin =
//				new MotzkinTransformation(mServices, mScript, AnalysisType.LINEAR, mAnnotateTerms);

		// Strategy strategy = new Strategy(icfg);
		// DisjunctionTemplate dt = new DisjunctionTemplate(2, new int[] {1,2}, new int[][] {{1}, {1, 1}}, new HashSet<TermVariable>(), "name");
		// System.out.println("formula");
	}
}
