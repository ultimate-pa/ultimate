/*
 * Copyright (C) 2014-2015 Mostafa Mahmoud Amin
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.impulse;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.RedirectionStrategy;


public class RedirectionFinder {
	
	private final ImpulseChecker codeChecker;
	public RedirectionFinder(ImpulseChecker codeChecker) {
		this.codeChecker = codeChecker;
	}
	
	public AnnotatedProgramPoint getStrongestValidCopy(AppEdge edge) {
		return depthFirstSearch(edge, edge.getTarget());
	}
	private AnnotatedProgramPoint depthFirstSearch(AppEdge edge, AnnotatedProgramPoint clone) {
		final ArrayList <AnnotatedProgramPoint> nextNodes = new ArrayList<AnnotatedProgramPoint> ();
		for (final AnnotatedProgramPoint nextClone : clone.getNextClones()) {
			if (codeChecker.isValidRedirection(edge, nextClone)) {
				if (codeChecker.getGlobalSettings().getRedirectionStrategy() == RedirectionStrategy.FIRST) {
					return depthFirstSearch(edge, nextClone);
				}
				nextNodes.add(depthFirstSearch(edge, nextClone));
			}
		}
		return pickUp(clone, nextNodes);
	}
	private AnnotatedProgramPoint pickUp(AnnotatedProgramPoint def, ArrayList<AnnotatedProgramPoint> nodes) {
		AnnotatedProgramPoint ret = def;
		if (!nodes.isEmpty()) {
			if (codeChecker.getGlobalSettings().getRedirectionStrategy() == RedirectionStrategy.RANDOM) {
				ret = nodes.get((int) (Math.random() * nodes.size()));
			}
			if (codeChecker.getGlobalSettings().getRedirectionStrategy() == RedirectionStrategy.RANDOmSTRONGEST) {
				ret = strongRandomPickup(nodes);
			}
		}
		return ret;
	}
	private AnnotatedProgramPoint strongRandomPickup(ArrayList<AnnotatedProgramPoint> nodes) {
		final HashSet<AnnotatedProgramPoint> predicates = new HashSet<AnnotatedProgramPoint>();
		for (final AnnotatedProgramPoint node : nodes) {
			predicates.add(node);
		}
		
		for (final AnnotatedProgramPoint node : nodes) {
			if (!predicates.contains(node)) {
				continue;
			}
			final AnnotatedProgramPoint[] comp = predicates.toArray(new AnnotatedProgramPoint[]{});
			for (final AnnotatedProgramPoint subNode : comp) {
				if (subNode == node) {
					continue;
				}
				if (codeChecker.isStrongerPredicate(node, subNode)) {
					predicates.remove(subNode);
				}
			}
		}
		final AnnotatedProgramPoint[] best = predicates.toArray(new AnnotatedProgramPoint[]{});
		return best[(int) (best.length * Math.random())];
	}
}
