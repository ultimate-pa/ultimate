package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.script;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil.HornClause;

public class HornAnnot implements IAnnotations {

	final Map<String, Object> mp = new HashMap<String, Object>();
	public HornAnnot(List<HornClause> clauses) {
		mp.put("HoRNClauses", clauses);
	}
	
	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return mp;
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
