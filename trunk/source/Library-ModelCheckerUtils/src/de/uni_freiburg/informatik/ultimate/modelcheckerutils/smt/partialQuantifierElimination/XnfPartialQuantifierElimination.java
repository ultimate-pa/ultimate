package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination;

import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;

/**
 * Abstract superclass for our partical quantifier elimination for terms in XNF.
 * @author Matthias Heizmann
 */

public abstract class XnfPartialQuantifierElimination {
	protected final Script m_Script;
	protected final IUltimateServiceProvider m_Services; 
	protected final Logger m_Logger;
	
	
	public XnfPartialQuantifierElimination(Script script,
			IUltimateServiceProvider services) {
		super();
		m_Script = script;
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(ModelCheckerUtils.sPluginID);
	}
	public abstract String getName();
	public abstract String getAcronym();
	public abstract Term[] tryToEliminate(int quantifier, Term[] oldParams, Set<TermVariable> eliminatees);

}
