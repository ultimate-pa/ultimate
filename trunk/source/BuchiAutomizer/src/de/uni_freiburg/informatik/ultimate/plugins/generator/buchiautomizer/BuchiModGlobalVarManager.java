package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;

public class BuchiModGlobalVarManager extends ModifiableGlobalVariableManager {

	public BuchiModGlobalVarManager(
			Map<String, Map<String, ASTType>> m_ModifiedVars,
			Boogie2SMT m_Boogie2smt) {
		super(m_ModifiedVars, m_Boogie2smt);
		// TODO Auto-generated constructor stub
	}

}
