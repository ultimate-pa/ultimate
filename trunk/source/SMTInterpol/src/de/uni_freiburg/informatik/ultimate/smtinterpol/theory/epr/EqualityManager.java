/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqualityManager {

	HashMap<ApplicationTerm, HashSet<ApplicationTerm>> eqGraph = new HashMap<ApplicationTerm, HashSet<ApplicationTerm>>();
	HashMap<ApplicationTerm, HashMap<ApplicationTerm, CCEquality>> termPairToEquality = new HashMap<ApplicationTerm, HashMap<ApplicationTerm, CCEquality>>();


	public void addEquality(ApplicationTerm a, ApplicationTerm b, CCEquality e) {
		updateTermPairToEquality(a, b, e);

		HashSet<ApplicationTerm> aTargets = eqGraph.get(a);
		if (aTargets == null) {
			aTargets = new HashSet<ApplicationTerm>();
			eqGraph.put(a, aTargets);
		}
		aTargets.add(b);

		HashSet<ApplicationTerm> bTargets = eqGraph.get(b);
		if (bTargets == null) {
			bTargets = new HashSet<ApplicationTerm>();
			eqGraph.put(b, bTargets);
		}
		bTargets.add(a);
	}

	private void updateTermPairToEquality(ApplicationTerm a, ApplicationTerm b, CCEquality e) {
		HashMap<ApplicationTerm, CCEquality> termToEquality = termPairToEquality.get(a);
		if (termToEquality == null) {
			termToEquality = new HashMap<ApplicationTerm, CCEquality>();
			termPairToEquality.put(a, termToEquality);
		}
		termToEquality.put(b, e);

		termToEquality = termPairToEquality.get(b);
		if (termToEquality == null) {
			termToEquality = new HashMap<ApplicationTerm, CCEquality>();
			termPairToEquality.put(b, termToEquality);
		}
		termToEquality.put(a, e);
	}

//	public CCEquality getCCEquality(ApplicationTerm a, ApplicationTerm b) {
//		return termPairToEquality.get(a).get(b);
//	}

	public void backtrackEquality(ApplicationTerm a, ApplicationTerm b) {
		eqGraph.get(a).remove(b);
		eqGraph.get(b).remove(a);
	}

	public ArrayList<CCEquality> isEqualRec(ApplicationTerm a, ApplicationTerm b,
			ArrayList<CCEquality> pathSoFar, HashSet<ApplicationTerm> visited) {
		if (a.equals(b))
			return pathSoFar;
		if (eqGraph.get(a) == null)
			return null;
		for (ApplicationTerm trg : eqGraph.get(a)) {
			if (!visited.contains(trg)) {
				visited.add(trg);
				ArrayList<CCEquality> newPath = new ArrayList<CCEquality>(pathSoFar);
				newPath.add(termPairToEquality.get(a).get(trg));
				ArrayList<CCEquality> res = isEqualRec(trg, b, newPath, visited);
				if (res != null)
					return res;
			}
		}
		return null;
	}

	/**
	 *
	 * @param a
	 * @param b
	 * @return null if a and b are not equal in the current state, a list of CCEqualities which are set and by transitivity witness a=b otherwise
	 */
	public ArrayList<CCEquality> isEqual(ApplicationTerm a, ApplicationTerm b) {
//		ArrayDeque<ApplicationTerm> queue = new ArrayDeque<>();
		HashSet<ApplicationTerm> visited = new HashSet<ApplicationTerm>();
		ArrayList<CCEquality> path = new ArrayList<CCEquality>();

		return isEqualRec(a, b, path, visited);

//		queue.addLast(a);
//
//		while (!queue.isEmpty()) {
//			ApplicationTerm current = queue.pollFirst();
//
//			if (current.equals(b))
//				return result;
//
//			visited.add(current);
//
//			for (ApplicationTerm n : eqGraph.get(current)) {
//				if (!visited.contains(n))
//					queue.add(n);
//			}
//		}
//		return null;
	}

//	public Object getCCEqualities() {
//		if (termPairTo)
//		// TODO Auto-generated method stub
//		return null;
//	}
}
