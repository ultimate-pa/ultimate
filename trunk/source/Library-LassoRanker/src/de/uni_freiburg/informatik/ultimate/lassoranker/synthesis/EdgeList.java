/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
/**
 * This package provides a framework for the constraint-based synthesis of
 * safety invariants, ranking functions, danger invariants, recurrence sets,
 * etc.
 *
 * @author Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Jan Oreans (oreansj@cs.uni-freiburg.de)
 *
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.synthesis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/* Contains a List of all edges and their source and target */
public class EdgeList {
	private final ArrayList<EdgeListEntry> mList;
	private Theory mTheory;
	private final TreeMap<String, TermVariable> mBuildVariables;

	public EdgeList(final IIcfg<IcfgLocation> icfg) {
		mList = new ArrayList<>();
		mBuildVariables = new TreeMap<>();

		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		final Map<String, Map<DebugIdentifier, IcfgLocation>> i = icfg.getProgramPoints();
		for (final String j : i.keySet()) {
			final Map<DebugIdentifier, IcfgLocation> l = i.get(j);
			for (final DebugIdentifier k : l.keySet()) {
				final IcfgLocation point = l.get(k);
				for (final IcfgEdge edge : point.getOutgoingEdges()) {
					processEdge(edge, mgdScript);
					System.out.println("Running");
				}
			}
		}
		System.out.println(mList);
	}

	private void processEdge(final IcfgEdge e, final ManagedScript s) {
		final IcfgLocation target = e.getTarget();
		final IcfgLocation source = e.getSource();
		final TransFormula f = e.getTransformula();
		Term term = f.getFormula();
		final Map<Term, Term> m = new HashMap<>();
		System.out.println("term old: " + term);
		final ArrayList<TermVariable> invars = new ArrayList<>();
		// Process invars
		for (final IProgramVar in : f.getInVars().keySet()) {
			if (mTheory == null) { // initialize mtheory once
				mTheory = in.getTerm().getTheory();
			}
			// System.out.println("All Invars: " + f.getInVars());
			final TermVariable var = getVariable("v_" + in.toString() + "_old", s); // TODO ints or reals?
			// System.out.println("in: " + in + " var: " + var);
			m.put(f.getInVars().get(in), var);
			// System.out.println(f.getInVars().get(in) + " " + m);

		}
		// Process outvars
		for (final IProgramVar out : f.getOutVars().keySet()) {
			if (mTheory == null) { // initialize mtheory once
				mTheory = out.getTerm().getTheory();
			}
			// System.out.println("All outvars: " + f.getOutVars());
			final TermVariable var = getVariable("v_" + out.toString() + "_new", s); // TODO ints or reals?
			// System.out.println("out: " + out + " var: " + var);
			m.put(f.getOutVars().get(out), var);
			// System.out.println(f.getInVars().get(out) + " " + m);
		}
		term = Substitution.apply(s, m, term);
		System.out.println("term new: " + term + "\n");
		mList.add(new EdgeListEntry(source, target, term));
	}

	/* Returns a variable with the name str. if one already exists, returns it */
	private TermVariable getVariable(final String str, final ManagedScript s) {
		if (!mBuildVariables.containsKey(str)) {
			final TermVariable v = s.variable(str, mTheory.getNumericSort());
			mBuildVariables.put(str, v);
			// System.out.println(str);
		}
		return mBuildVariables.get(str);
	}
}
