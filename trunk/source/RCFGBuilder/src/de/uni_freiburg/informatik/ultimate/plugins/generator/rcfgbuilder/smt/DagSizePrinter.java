package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * Object that returns the DAG size of a term on demand.
 * Use this e.g. in 
 * s_Logger.debug(new DebugMessage("size of formula" new DagSizePrinter(formula));
 * in order to compute the dag size only if the log level is set to debug.
 * 
 * @author Matthias Heizmann
 *
 */
public class DagSizePrinter {
	
	private final Term m_Term;
	
	public DagSizePrinter(Term term) {
		m_Term = term;
	}
	
	@Override
	public String toString() {
		return String.valueOf((new DAGSize()).size(m_Term));
	}

}
