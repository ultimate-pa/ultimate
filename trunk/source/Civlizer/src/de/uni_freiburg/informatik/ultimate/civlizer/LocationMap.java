
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.HashSet;
import java.util.regex.*;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Term2Expression;

final class LocationMap {

	//private Term2Expression mSmtTranslator;
	private Map<String, Map<Integer, Expression>> mLocationMap;

	LocationMap() {
		//mSmtTranslator = new Term2Expression(...);
		mLocationMap = new HashMap<String, Map<Integer, Expression>>();
	}

	Map<Integer, Expression> getProcedureMap(String procName) {
		return mLocationMap.get(procName);
	}

	void addProcedureMap(Procedure proc, Map formulaMapping) {
		// handle while if TODO
		int line_offset = -1;
		Map<Integer, Expression> result = new HashMap<Integer, Expression>();

		Statement[] statements = proc.getBody().getBlock();

		int i = 0;

		if (statements.length > 0) {
			//IPredicate formulaMapping.keySet()();
			line_offset = statements[0].getLoc().getStartLine();
		}

		/*Pattern pattern = Pattern.compile("^L\\d+(?:-\\d+)");

		for (var entry : formulaMapping.entrySet()) {
			String key = entry.getKey().toString();

			Matcher matcher = pattern.matcher(key);

			if (matcher.matches()) {
				int line = Integer.parseInt(matcher.group(2)) - line_offset;
			}
			else {

			}

			//System.out.println(key + " -> " + entry.getValue());
		}*/

		mLocationMap.put(proc.getIdentifier(), result);
	}
}