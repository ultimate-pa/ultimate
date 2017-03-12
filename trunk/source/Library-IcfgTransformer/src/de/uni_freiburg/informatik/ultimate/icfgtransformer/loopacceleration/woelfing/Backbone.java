/*
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.woelfing;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * A Backbone.
 *
 * @author Dennis Wölfing
 *
 */
public class Backbone {

	private final List<IcfgEdge> mTransitions;
	private TransFormula mTransFormula;

	/**
	 * Constructs a Backbone with an initial transition.
	 *
	 * @param transition
	 *            The entry transition of the Backbone.
	 */
	public Backbone(final IcfgEdge transition) {
		mTransitions = new ArrayList<>();
		mTransitions.add(transition);
	}

	/**
	 * Constructs a copy of a Backbone.
	 *
	 * @param other
	 *            The original Backbone.
	 */
	public Backbone(final Backbone other) {
		mTransitions = new ArrayList<>(other.mTransitions);
	}

	/**
	 * Calculates a TransFormula that holds after the given backbone was taken once.
	 *
	 * @param script
	 *            A ManagedScipt.
	 * @return A Transformula.
	 */
	public TransFormula getTransformula(final ManagedScript script) {
		if (mTransFormula != null) {
			return mTransFormula;
		}

		Term term = script.getScript().term("true");

		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();

		for (final IcfgEdge edge : mTransitions) {
			final TransFormula tf = edge.getTransformula();

			for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
				if (!outVars.containsKey(entry.getKey())) {
					assert !inVars.containsKey(entry.getKey());
					inVars.put(entry.getKey(), entry.getValue());
				} else if (outVars.get(entry.getKey()) != entry.getValue()) {
					term = Util.and(script.getScript(), term,
							script.getScript().term("=", entry.getValue(), outVars.get(entry.getKey())));
				}
			}

			term = Util.and(script.getScript(), term, tf.getFormula());

			for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
				outVars.put(entry.getKey(), entry.getValue());
			}
		}

		final TransFormulaBuilder builder = new TransFormulaBuilder(inVars, outVars, true, null, true, null, true);
		builder.setFormula(term);
		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		mTransFormula = builder.finishConstruction(script);
		return mTransFormula;
	}

	/**
	 * Appends a transition to the Backbone.
	 *
	 * @param transition
	 *            The transition to append.
	 */
	public void addTransition(final IcfgEdge transition) {
		mTransitions.add(transition);
	}

	/**
	 * Checks whether the Backbone ends in a loop.
	 *
	 * @return true if the Backbone end in a loop.
	 */
	public boolean endsInLoop() {
		final IcfgLocation lastLocation = getLastLocation();
		for (final IcfgEdge edge : mTransitions) {
			if (edge.getSource() == lastLocation) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Gets the last location of the Backbone.
	 *
	 * @return An IcfgLocation.
	 */
	public IcfgLocation getLastLocation() {
		return mTransitions.get(mTransitions.size() - 1).getTarget();
	}

	/**
	 * Gets the transition that enters the loop.
	 *
	 * @return The transition that enters the loop or null if the Backbone does not end in a loop.
	 */
	public IcfgEdge getLoopEntryTransition() {
		final IcfgLocation loopEntry = getLastLocation();

		for (final IcfgEdge edge : mTransitions) {
			if (edge.getSource() == loopEntry) {
				return edge;
			}
		}

		return null;
	}

	public List<IcfgEdge> getTransitions() {
		return mTransitions;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("[");
		for (final IcfgEdge edge : mTransitions) {
			builder.append(edge.getSource());
			builder.append(", ");
		}
		builder.append(getLastLocation());
		builder.append("]");
		return builder.toString();
	}
}
