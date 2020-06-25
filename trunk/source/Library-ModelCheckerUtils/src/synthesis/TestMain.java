package synthesis;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.MotzkinTransformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;


public class TestMain {
	public static void main(String[] args) {
		System.out.println("test");
	}
	
	public static void testEntryPoint(IIcfg<IcfgLocation> icfg, IUltimateServiceProvider mServices) {
		System.out.println("got root node");
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		
		boolean mAnnotateTerms = true;
		Script mScript = (Script) mgdScript;
		
		final MotzkinTransformation motzkin =
				new MotzkinTransformation(mServices, mScript, AnalysisType.LINEAR, mAnnotateTerms);
		
		// Strategy strategy = new Strategy(icfg);
		// DisjunctionTemplate dt = new DisjunctionTemplate(2, new int[] {1,2}, new int[][] {{1}, {1, 1}}, new HashSet<TermVariable>(), "name");
		// System.out.println("formula");
	}
}
