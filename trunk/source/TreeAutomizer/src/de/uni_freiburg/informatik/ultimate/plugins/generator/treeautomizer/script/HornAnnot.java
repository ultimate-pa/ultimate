package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.script;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;

public class HornAnnot implements IAnnotations {

	private final Script mBackendSolverScript;
	final Map<String, Object> mp = new HashMap<>();

	public HornAnnot(final List<HornClause> clauses, final Script backendSolver) {
		mp.put("HoRNClauses", clauses);
		mBackendSolverScript = backendSolver;
	}

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return mp;
	}

	public Script getScript() {
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
