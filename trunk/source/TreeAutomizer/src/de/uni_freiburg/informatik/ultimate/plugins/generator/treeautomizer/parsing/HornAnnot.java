package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class HornAnnot implements IAnnotations {

	private static final long serialVersionUID = -3542578811318106167L;
	private final ManagedScript mBackendSolverScript;
	private final Map<String, Object> mp = new HashMap<>();
	private final HCSymbolTable mSymbolTable;

	public HornAnnot(final List<HornClause> clauses, 
			final ManagedScript backendSolver,
			final HCSymbolTable symbolTable) {
		mp.put(HornUtilConstants.HORN_ANNOT_NAME, clauses);
		mBackendSolverScript = backendSolver;
		mSymbolTable = symbolTable;
	}

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return mp;
	}

	public ManagedScript getScript() {
		return mBackendSolverScript;
	}
	
	public HCSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	@Override
	public String toString() {
		StringBuilder res = new StringBuilder();
		for (final Entry<String, Object> en : mp.entrySet()) {
			if (res.length() != 0) {
				res.append('\t');
			}
			res.append("{{" + en.getValue().toString() + "}}");
		}
		return res.toString();
	}
}
