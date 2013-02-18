/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.test;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.result.IValuation;

/**
 * Objects return Test Data.
 * 
 * @author Stefan Wissert
 * 
 */
public class TestValuation implements IValuation {

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.result.IValuation#
	 * getValuesForFailurePathIndex(int)
	 */
	@Override
	public Map<String, SimpleEntry<IType, List<String>>> getValuesForFailurePathIndex(
			int index) {
		HashMap<String, SimpleEntry<IType, List<String>>> map = new HashMap<String, SimpleEntry<IType, List<String>>>();
		switch (index) {
		case 0:
			map.put("x",
					new SimpleEntry<IType, List<String>>(BoogieType.intType,
							new ArrayList<String>(Arrays.asList("11"))));
			return map;
		case 1:
			map.put("names",
					new SimpleEntry<IType, List<String>>(BoogieType
							.createArrayType(3,
									new BoogieType[] { BoogieType.intType },
									BoogieType.intType), new ArrayList<String>(
							Arrays.asList("Stefan", "Alex", "Markus"))));
			return map;
		default:
			map.put("x",
					new SimpleEntry<IType, List<String>>(BoogieType.intType,
							new ArrayList<String>(Arrays.asList("11"))));
			map.put("y",
					new SimpleEntry<IType, List<String>>(BoogieType.intType,
							new ArrayList<String>(Arrays.asList("4711"))));
			map.put("counter",
					new SimpleEntry<IType, List<String>>(BoogieType.intType,
							new ArrayList<String>(Arrays.asList("133423421"))));
			return map;
		}
	}
}
