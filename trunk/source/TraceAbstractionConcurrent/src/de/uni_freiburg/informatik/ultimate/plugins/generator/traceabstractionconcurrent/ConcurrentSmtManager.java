package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.HashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class ConcurrentSmtManager extends SmtManager {

	
	public ConcurrentSmtManager(Boogie2SMT boogie2smt,
			ModifiableGlobalVariableManager modifiableGlobals) {
		super(boogie2smt, modifiableGlobals);
		// TODO Auto-generated constructor stub
	}

	ProdState getNewProdState(List<IPredicate> programPoints) {
		return new ProdState(m_SerialNumber++, programPoints, super.getScript().term("true"),new HashSet<BoogieVar>(0));
	}
}
