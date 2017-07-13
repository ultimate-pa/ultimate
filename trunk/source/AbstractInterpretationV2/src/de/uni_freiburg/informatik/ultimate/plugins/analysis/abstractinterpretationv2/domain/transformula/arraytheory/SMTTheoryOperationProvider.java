package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;

public class SMTTheoryOperationProvider extends TermDomainOperationProvider {

	private final ILogger mLogger;
	private final CfgSmtToolkit mCsToolkit;

	public SMTTheoryOperationProvider(IUltimateServiceProvider services, CfgSmtToolkit csToolkit) {
		super(services, csToolkit.getManagedScript());
		mCsToolkit = csToolkit;
		mLogger = services.getLoggingService().getLogger(getClass());
	}

	@Override
	public Term projectExistentially(Set<TermVariable> varsToProjectAway, Term constraint) {
		
		return super.projectExistentially(varsToProjectAway, constraint);
	}
	
	


}
