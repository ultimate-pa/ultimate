package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public class SmtUtils {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	public static Term simplify(Script script, Term formula) {
		s_Logger.debug(new DebugMessage(
				"simplifying formula of DAG size {0}", 
				new DagSizePrinter(formula)));
		Term simplified = (new SimplifyDDA(script)).getSimplifiedTerm(formula);
		s_Logger.debug(new DebugMessage(
				"DAG size before simplification {0}, DAG size after simplification {1}", 
				new DagSizePrinter(formula), new DagSizePrinter(simplified)));
		return simplified;
	}
}
