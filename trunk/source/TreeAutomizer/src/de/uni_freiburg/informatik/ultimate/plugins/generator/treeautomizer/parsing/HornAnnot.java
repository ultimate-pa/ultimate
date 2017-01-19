package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class HornAnnot implements IAnnotations {

	private final ManagedScript mBackendSolverScript;
	final Map<String, Object> mp = new HashMap<>();

	public HornAnnot(final List<HornClause> clauses, final ManagedScript backendSolver) {
		mp.put("HoRNClauses", clauses);
		mBackendSolverScript = backendSolver;
	}

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return mp;
	}

	public ManagedScript getScript() {
		return mBackendSolverScript;
	}

	@Override
	public String toString() {
		String res = "";
		for (final String key : mp.keySet()) {
			if (!res.isEmpty()) {
				res += '\t';
			}
			res += "{{" + mp.get(key).toString() + "}}";
		}
		return res;
	}
}
