package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;

public class SMTTheoryOperationProvider extends TermDomainOperationProvider {

	public SMTTheoryOperationProvider(IUltimateServiceProvider services, ManagedScript mgdScript) {
		super(services, mgdScript);
		// TODO Auto-generated constructor stub
	}

	@Override
	public Term projectExistentially(Set<TermVariable> varsToProjectAway, Term constraint) {
		// TODO Auto-generated method stub
		return super.projectExistentially(varsToProjectAway, constraint);
	}

}
